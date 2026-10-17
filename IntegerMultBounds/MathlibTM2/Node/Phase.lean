module

public import IntegerMultBounds.MathlibTM2.Host.IndexRoute
public import IntegerMultBounds.MathlibTM2.Layer.Enc
public import IntegerMultBounds.MathlibTM2.Layer.GaussStream
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# Phase multiplication of stored arrays

`phaseZ mask c Z` multiplies every cell of a Gaussian-integer array by the unit
`i ^ (c · popcount(mask AND a))`, `a` the address of the cell. The exponent `phaseExp mask c a` is
`c * ∑ t, (mask t * a t).val` in `ZMod 4`; `phaseClass` reads it in `Fin 4`, and `unitG q` is the
unit `i ^ q` as a pair of integers.

**Code.** The code automaton `phaseCode c : CAuto A 2 4` reads the address field (code-pass
register `0`) and the mask register (register `1`) one bit of each per step, counts modulo `4`
the positions where both bits are set, and outputs `c` times the count. The index counter is a
single field of length `n` (`phaseSrc mnum` names its sources), so the code of record index
`i` is the class of the in-row address `i % 2 ^ n` (`idxCode_phase`), and at
`i = 2 ^ n u + a`, `a < 2 ^ n`, the class of `addrBits n a` (`idxCode_phase_addr`).

**Program.** `phaseProg ρ st c` runs on the registers `ρ x`, `x : PhaseReg`, with the code and
automaton state in scan slot `st`:
1. `routeIdx` moves the records of `arr` (blocks of `r * w` symbols, counted by `rc`) onto the
   class registers `cls q` by code, the address field `af` counting from `0`;
2. for each class `q`, `classPass` reverses `cls q` onto `aux` (forward order), multiplies every
   coefficient by `i ^ q` onto `aux2` (`mulG_exec` with the unit `unitG q`, words of `w` symbols
   counted by `wc`), and moves `aux2` back onto `cls q` (forward order);
3. `mergeIdx` with the same code merges the classes onto `aux` in record order, one record per
   symbol of `cnt`; after `R * 2 ^ n` records the field is back at `0`, so the merge starts from
   index `0` again;
4. `moveR` puts the result in forward order on `arr`.

Register interface (`ρ` injective, `st` outside `ρ aux`, `ρ af`, `ρ msk`, `ρ t0`, `ρ t1`):
`arr` holds `encZ A w Z`; `cls q`, `tmp`, `aux`, `aux2`, `t0`, `t1` are empty; `rc` holds `r * w`
symbols, `wc` holds `w` symbols, `cnt` holds `R * 2 ^ n` symbols; `af` holds `binSyms n 0`;
`msk` holds `binSyms n mnum` with `addrBits n mnum = mask` (for instance
`mnum = ∑ t, if mask t = 1 then 2 ^ t else 0`, by `addrBits_bitsNum`).

`phaseProg_exec`: the program ends with `encZ A w (phaseZ mask c Z)` on `arr`, every other
register as it started and `v'.user = v.user`, in at most
`R * 2 ^ n * (25 * r * w + 20 * n + 36) + 33` steps, for `5 ≤ A`, `1 ≤ r`, `1 ≤ w`.

Proof devices: `blocksIdx_flatMap` (routing commutes with expanding every element into a list of
constant length) and `blocksIdx_map` (a map acting on every block of class `d` acts on the routed
list of class `d`) reduce the class contents to records (`recKeys`, `recOf`, `blk_coeffList`);
`blocksIdx_encZ_phase` identifies the multiplied class lists with the class lists of the phased
array, and the round trip `mergeIdx_exec_blocks` reassembles the phased stream. The class passes
cost at most `R * 2 ^ n * r * (9 * w + 6) + 25` steps in total, since every record has one class
(`sum_idxCount`).

**Sign corrections.** `signM_eq_phaseZ`: for an injective `e`, the column characters `signM e u`
of `NodeZ` are the phase `phaseZ (signMask e u) 2`, where `signMask e u` is the indicator of the
positions `e (bitIdx j c)` with `u j = 1`. The proof goes through `prod_signZ_binary`, stated for
any number `h` of slots and the dot product `Labels.binary h`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer


/-! ### The phase on arrays -/

section Arrays

variable {Y : Type} {n : ℕ}

/-- The phase exponent of an address `x`: `c` times the popcount of `mask AND x`, modulo `4`. -/
def phaseExp (mask : Fin n → ZMod 2) (c : ZMod 4) (x : Fin n → ZMod 2) : ZMod 4 :=
  c * ∑ t, ((mask t * x t).val : ZMod 4)

/-- Multiplication of every cell by `i ^ (c · popcount(mask AND address))`. -/
def phaseZ (mask : Fin n → ZMod 2) (c : ZMod 4) (Z : ZArr Y n) : ZArr Y n :=
  fun p => (⟨0, 1⟩ : GaussianInt) ^ (phaseExp mask c p.2).val * Z p

/-- The class of an address: its phase exponent as an element of `Fin 4`. -/
def phaseClass (mask : Fin n → ZMod 2) (c : ZMod 4) (x : Fin n → ZMod 2) : Fin 4 :=
  ⟨(phaseExp mask c x).val, ZMod.val_lt _⟩

/-- The unit `i ^ q` as a pair of integers. -/
def unitG : Fin 4 → ℤ × ℤ := ![(1, 0), (0, 1), (-1, 0), (0, -1)]

lemma pow_I_eq_unitG (q : Fin 4) :
    (⟨0, 1⟩ : GaussianInt) ^ q.val = ⟨(unitG q).1, (unitG q).2⟩ := by
  fin_cases q <;> decide

lemma unitG_natAbs (q : Fin 4) : (unitG q).1.natAbs + (unitG q).2.natAbs = 1 := by
  fin_cases q <;> rfl

lemma red_phaseZ (w : ℕ) (mask : Fin n → ZMod 2) (c : ZMod 4) (Z : ZArr Y n) (p) :
    red w (phaseZ mask c Z p) =
      GR.mulG (unitG (phaseClass mask c p.2)).1 (unitG (phaseClass mask c p.2)).2 (red w (Z p)) := by
  rw [phaseZ, show (phaseExp mask c p.2).val = (phaseClass mask c p.2).val from rfl,
    pow_I_eq_unitG, red_mulG]

end Arrays

/-! ### Sign corrections as phases -/

section Sign

open IntegerMultBounds.Networks

variable {Y : Type} {n h k : ℕ}

/-- The mask of the set bits of `u` in the active bits: `t = e (bitIdx j c)` with `u j = 1`. -/
def signMask (e : Fin (h * k) → Fin n) (u : Fin h → ZMod 2) (t : Fin n) : ZMod 2 :=
  if ∃ j c, e (bitIdx j c) = t ∧ u j = 1 then 1 else 0

lemma signMask_bitIdx {e : Fin (h * k) → Fin n} (he : Function.Injective e) (u : Fin h → ZMod 2)
    (j : Fin h) (c : Fin k) : signMask e u (e (bitIdx j c)) = u j := by
  unfold signMask
  split_ifs with hex
  · obtain ⟨j', c', hjc, hu'⟩ := hex
    rw [(bitIdx_inj.1 (he hjc)).1] at hu'
    exact hu'.symm
  · rcases zmod2_zero_or_one (u j) with h0 | h1
    · exact h0.symm
    · exact absurd ⟨j, c, rfl, h1⟩ hex

/-- The dot product of the mask with a bit vector is the sum over the columns of the dot
products of `u` with the column bits. -/
lemma sum_signMask {e : Fin (h * k) → Fin n} (he : Function.Injective e) (u : Fin h → ZMod 2)
    (x : Fin n → ZMod 2) :
    ∑ t, signMask e u t * x t = ∑ c : Fin k, ∑ j : Fin h, u j * x (e (bitIdx j c)) := by
  have h1 : ∑ t, signMask e u t * x t = ∑ t ∈ Finset.univ.image e, signMask e u t * x t := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have : signMask e u t = 0 := by
      unfold signMask
      split_ifs with hex
      · obtain ⟨j, c, hjc, _⟩ := hex
        exact absurd (Finset.mem_image.2 ⟨_, Finset.mem_univ _, hjc⟩) ht
      · rfl
    rw [this, zero_mul]
  rw [h1, Finset.sum_image (fun a _ b _ hab => he hab), ← Equiv.sum_comp finProdFinEquiv,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show finProdFinEquiv (j, c) = bitIdx j c from rfl, signMask_bitIdx he]

lemma signZ_eq_pow (a : ZMod 2) : signZ a = (-1) ^ a.val := by
  rcases zmod2_zero_or_one a with rfl | rfl <;> rfl

lemma neg_one_pow_congr {a b : ℕ} (hab : (a : ZMod 2) = b) :
    ((-1 : GaussianInt)) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := b),
    (ZMod.natCast_eq_natCast_iff' a b 2).1 hab]

/-- `i ^ (2 s)` for a natural number `s` is the sign `(-1) ^ s`. -/
lemma pow_I_two_mul (N : ℕ) :
    (⟨0, 1⟩ : GaussianInt) ^ (2 * (N : ZMod 4)).val = (-1) ^ N := by
  have h4 : (⟨0, 1⟩ : GaussianInt) ^ 4 = 1 := by decide
  have h2 : (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 := by decide
  rw [show (2 * (N : ZMod 4)) = ((2 * N : ℕ) : ZMod 4) by push_cast; ring, ZMod.val_natCast,
    ← pow_eq_pow_mod _ h4, pow_mul, h2]

/-- The product of the column signs is the phase `i ^ (2 · popcount(signMask e u AND x))`, for
any number `h` of slots. -/
theorem prod_signZ_binary {e : Fin (h * k) → Fin n} (he : Function.Injective e)
    (u : Fin h → ZMod 2) (x : Fin n → ZMod 2) :
    (∏ c : Fin k, signZ (Labels.binary h u (fun j => x (e (bitIdx j c))))) =
      (⟨0, 1⟩ : GaussianInt) ^ (phaseExp (signMask e u) 2 x).val := by
  have hdot : ∀ y : Fin h → ZMod 2, Labels.binary h u y = ∑ j, u j * y j := fun y => by
    simp [Labels.binary, Labels.form_apply]
  simp only [hdot, signZ_eq_pow]
  rw [Finset.prod_pow_eq_pow_sum, phaseExp,
    show (∑ t, (((signMask e u t * x t).val : ℕ) : ZMod 4)) =
      ((∑ t, (signMask e u t * x t).val : ℕ) : ZMod 4) by push_cast; rfl,
    pow_I_two_mul]
  apply neg_one_pow_congr
  push_cast
  simp only [ZMod.natCast_zmod_val]
  rw [sum_signMask he]

/-- **Sign corrections are phases.** For an injective `e`, the product of the column characters
`signM e u` is the phase `i ^ (2 · popcount(signMask e u AND address))`. -/
theorem signM_eq_phaseZ {e : Fin (m * k) → Fin n} (he : Function.Injective e)
    (u : BinaryWalsh.Address m) (Z : ZArr Y n) : signM e u Z = phaseZ (signMask e u) 2 Z := by
  funext p
  exact congrArg (· * Z p) (prod_signZ_binary he u p.2)

end Sign

/-! ### Blocks by index code -/

section Lists

variable {α β : Type} {nd : ℕ}

/-- Routing commutes with expanding every element into `k` elements. -/
lemma blocksIdx_flatMap (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) (l : List α)
    (B nb : ℕ) (code : ℕ → Fin nd) (i₀ : ℕ) (d : Fin nd) :
    blocksIdx (l.flatMap f) (B * k) nb code i₀ d = (blocksIdx l B nb code i₀ d).flatMap f := by
  unfold blocksIdx blk
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun m _ => ?_
  rw [← Nat.mul_assoc, drop_flatMap_const f k hf, take_flatMap_const f k hf]

/-- A map acting on the blocks of code `d` acts on the routed list of code `d`. -/
lemma blocksIdx_map (l : List α) (l' : List β) (φ : α → β) (B nb : ℕ) (code : ℕ → Fin nd)
    (i₀ : ℕ) (d : Fin nd) (h : ∀ m < nb, code (i₀ + m) = d → (blk l B m).map φ = blk l' B m) :
    (blocksIdx l B nb code i₀ d).map φ = blocksIdx l' B nb code i₀ d := by
  unfold blocksIdx
  rw [List.map_flatMap]
  refine List.flatMap_congr fun m hm => ?_
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
  exact h m hm.1 hm.2

/-- Every index has one code. -/
lemma sum_idxCount (code : ℕ → Fin nd) : ∀ (m j : ℕ), ∑ d, idxCount code j m d = m := by
  intro m
  induction m with
  | zero => intro j; simp [idxCount]
  | succ m ih =>
      intro j
      simp only [idxCount_succ, Finset.sum_add_distrib, ih (j + 1)]
      rw [Finset.sum_ite_eq]
      simp; ring

end Lists

/-! ### Records in stream order -/

section Records

variable {R r n w : ℕ}

/-- The keys `(row, address)` of the records in stream order. -/
def recKeys (R n : ℕ) : List (Fin R × ℕ) :=
  (List.finRange R).flatMap fun u => (List.range (2 ^ n)).map fun a => (u, a)

/-- The record of a key. -/
def recOf (w : ℕ) (Z : ZArr (Fin R × Fin r) n) (k : Fin R × ℕ) : List (GR w) :=
  List.ofFn fun c : Fin r => red w (Z ((k.1, c), addrBits n k.2))

@[simp] lemma length_recOf (Z : ZArr (Fin R × Fin r) n) (k : Fin R × ℕ) :
    (recOf w Z k).length = r := by simp [recOf]

lemma length_recKeys : (recKeys R n).length = R * 2 ^ n := by
  rw [recKeys, length_flatMap_const _ (2 ^ n) (by simp)]
  simp

lemma coeffList_eq_keys (Z : ZArr (Fin R × Fin r) n) :
    coeffList w Z = (recKeys R n).flatMap (recOf w Z) := by
  simp [coeffList, recList, recKeys, recOf, List.flatMap_def, List.flatten_flatten,
    List.map_flatten, Function.comp_def]

lemma recKeys_snd (i : ℕ) (hi : i < (recKeys R n).length) : ((recKeys R n)[i]).2 = i % 2 ^ n := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  obtain ⟨u, a, ha, rfl⟩ : ∃ u a, a < 2 ^ n ∧ i = 2 ^ n * u + a :=
    ⟨i / 2 ^ n, i % 2 ^ n, Nat.mod_lt _ hpos, (Nat.div_add_mod i (2 ^ n)).symm⟩
  have hu : u < (List.finRange R).length := by
    rw [length_recKeys] at hi
    simp only [List.length_finRange]
    by_contra hh
    have : 2 ^ n * R ≤ 2 ^ n * u := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm R] at hi
    omega
  simp only [recKeys] at hi ⊢
  rw [getElem_flatMap_const _ (2 ^ n) (by simp) _ u a hu ha]
  simp [Nat.mod_eq_of_lt ha]

lemma blk_coeffList (Z : ZArr (Fin R × Fin r) n) (i : ℕ) (hi : i < (recKeys R n).length) :
    blk (coeffList w Z) r i = recOf w Z (recKeys R n)[i] := by
  rw [coeffList_eq_keys, blk]
  exact block_flatMap_const _ r (length_recOf Z) _ i hi

end Records

/-! ### The code automaton -/

section Code

variable {A : ℕ}

/-- A residue modulo `4` as a stack symbol. -/
def z4Sym (A : ℕ) (x : ZMod 4) : Fin (A + 4) := ⟨x.val, by have := ZMod.val_lt x; omega⟩

@[simp] lemma cast_z4Sym (x : ZMod 4) : ((z4Sym A x).val : ZMod 4) = x := ZMod.natCast_zmod_val x

/-- The phase code automaton: per step it reads one bit of the address (register `0`) and one
bit of the mask (register `1`), counts modulo `4` the positions where both are set, and outputs
`c` times the count. -/
def phaseCode (c : ZMod 4) : CAuto A 2 4 where
  init := z4Sym A 0
  step s b := z4Sym A ((s.val : ZMod 4) + if b 0 && b 1 then 1 else 0)
  out s := ⟨(c * (s.val : ZMod 4)).val, ZMod.val_lt _⟩

lemma phaseCode_run (c : ZMod 4) : ∀ (L : ℕ) (s : Fin (A + 4)) (vals : Fin 2 → ℕ),
    (((phaseCode c).run L s vals).val : ZMod 4) = (s.val : ZMod 4) +
      ∑ t ∈ Finset.range L, if (vals 0).testBit t && (vals 1).testBit t then 1 else 0 := by
  intro L
  induction L with
  | zero => intro s vals; simp [CAuto.run]
  | succ L ih =>
      intro s vals
      rw [CAuto.run, ih, Finset.sum_range_succ']
      simp only [phaseCode, cast_z4Sym, Nat.testBit_div_two]
      ring

/-- Sources of the two code-pass registers: the address field `0` and the mask number. -/
def phaseSrc (mnum : ℕ) : Fin 2 → Fin 1 ⊕ ℕ := ![.inl 0, .inr mnum]

/-- **The code of a record index.** At index `i` the code is the class of the in-row address
`i % 2 ^ n` (so the class of `addrBits n a` at index `2 ^ n u + a`, `a < 2 ^ n`). -/
theorem idxCode_phase (c : ZMod 4) (mnum i : ℕ) :
    idxCode (phaseCode (A := A) c) n (fun _ : Fin 1 => n) (phaseSrc mnum) i =
      phaseClass (addrBits n mnum) c (addrBits n (i % 2 ^ n)) := by
  have key : ∀ t : Fin n, (((addrBits n mnum t * addrBits n (i % 2 ^ n) t).val : ℕ) : ZMod 4) =
      if (i % 2 ^ n).testBit t && mnum.testBit t then 1 else 0 := by
    intro t
    simp only [addrBits]
    cases (i % 2 ^ n).testBit t <;> cases mnum.testBit t <;> rfl
  have hreg : regVal (fun _ : Fin 1 => n) (phaseSrc mnum) i = ![i % 2 ^ n, mnum] := by
    funext r
    fin_cases r
    · simp [regVal, phaseSrc, digit, fieldOff_zero]
    · simp [regVal, phaseSrc]
  apply Fin.ext
  simp only [idxCode, CAuto.eval, phaseClass, phaseExp, hreg]
  change (c * (((phaseCode (A := A) c).run n (z4Sym A 0) ![i % 2 ^ n, mnum]).val : ZMod 4)).val = _
  rw [phaseCode_run]
  simp only [key, cast_z4Sym, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun t => if (i % 2 ^ n).testBit t && mnum.testBit t then
    (1 : ZMod 4) else 0) n]
  simp

theorem idxCode_phase_addr (c : ZMod 4) (mnum u a : ℕ) (ha : a < 2 ^ n) :
    idxCode (phaseCode (A := A) c) n (fun _ : Fin 1 => n) (phaseSrc mnum) (2 ^ n * u + a) =
      phaseClass (addrBits n mnum) c (addrBits n a) := by
  rw [idxCode_phase, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

end Code

/-! ### The record lists of the phased array -/

section PhaseLists

variable {A R r n w : ℕ}

/-- After multiplying the coefficients of class `d` by `i ^ d`, the routed coefficient list of
class `d` is that of the phased array. -/
theorem blocksIdx_phase (Z : ZArr (Fin R × Fin r) n) (mask : Fin n → ZMod 2) (c : ZMod 4)
    (mnum : ℕ) (hmask : addrBits n mnum = mask) (d : Fin 4) :
    (blocksIdx (coeffList w Z) r (R * 2 ^ n)
        (idxCode (phaseCode (A := A) c) n (fun _ => n) (phaseSrc mnum)) 0 d).map
        (GR.mulG (unitG d).1 (unitG d).2) =
      blocksIdx (coeffList w (phaseZ mask c Z)) r (R * 2 ^ n)
        (idxCode (phaseCode (A := A) c) n (fun _ => n) (phaseSrc mnum)) 0 d := by
  apply blocksIdx_map
  intro m hm hcode
  have hm' : m < (recKeys R n).length := by rw [length_recKeys]; exact hm
  rw [Nat.zero_add, idxCode_phase, hmask] at hcode
  rw [blk_coeffList Z m hm', blk_coeffList _ m hm']
  simp only [recOf, List.map_ofFn]
  congr 1
  funext c'
  rw [Function.comp_apply, red_phaseZ, recKeys_snd m hm', hcode]

/-- Symbol form of `blocksIdx_phase`. -/
theorem blocksIdx_encZ_phase (Z : ZArr (Fin R × Fin r) n) (mask : Fin n → ZMod 2) (c : ZMod 4)
    (mnum : ℕ) (hmask : addrBits n mnum = mask) (d : Fin 4) :
    ((blocksIdx (coeffList w Z) r (R * 2 ^ n)
        (idxCode (phaseCode (A := A) c) n (fun _ => n) (phaseSrc mnum)) 0 d).map
        (GR.mulG (unitG d).1 (unitG d).2)).flatMap (coeffSyms A w) =
      blocksIdx (encZ A w (phaseZ mask c Z)) (r * w) (R * 2 ^ n)
        (idxCode (phaseCode (A := A) c) n (fun _ => n) (phaseSrc mnum)) 0 d := by
  rw [blocksIdx_phase Z mask c mnum hmask d, encZ,
    blocksIdx_flatMap (coeffSyms A w) w (length_coeffSyms A w)]

lemma length_encZ (Z : ZArr (Fin R × Fin r) n) :
    (encZ A w Z).length = R * 2 ^ n * (r * w) := by
  rw [encZ, length_flatMap_const _ w (length_coeffSyms A w), length_coeffList]
  ring

end PhaseLists

/-! ### The host program -/

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

/-- Register roles of the phase program. -/
inductive PhaseReg where
  /-- The array: `encZ A w Z` at the start, `encZ A w (phaseZ mask c Z)` at the end. -/
  | arr
  /-- The class registers, empty. -/
  | cls (q : Fin 4)
  /-- The record counter: `r * w` symbols. -/
  | rc
  /-- The coefficient counter: `w` symbols. -/
  | wc
  /-- An empty spare of routing, merging, increments and automata. -/
  | tmp
  /-- An empty spare: a class stream in forward order, then the merged stream. -/
  | aux
  /-- An empty spare: a multiplied class stream; the count spare of the merge. -/
  | aux2
  /-- The address field: `binSyms n 0`. -/
  | af
  /-- The mask: `binSyms n mnum`. -/
  | msk
  /-- An empty spare of the code pass. -/
  | t0
  /-- An empty spare of the code pass. -/
  | t1
  /-- The record count: `R * 2 ^ n` symbols. -/
  | cnt
  deriving DecidableEq

section Program

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
  (ρ : PhaseReg → Fin T) (st : Fin T)

/-- The code-pass registers: the address field and the mask. -/
def phaseRs : Fin 2 → Fin T := ![ρ .af, ρ .msk]

/-- The spares of the code pass. -/
def phaseTmps : Fin 2 → Fin T := ![ρ .t0, ρ .t1]

/-- Multiplication by `i ^ q` on coefficient streams. -/
def unitAuto (A : ℕ) (q : Fin 4) : Auto A 1 1 :=
  gaussAuto A ![![((unitG q).1, (unitG q).2)]] ((unitG q).1.natAbs + (unitG q).2.natAbs) false

/-- The pass of class `q`: reverse its register onto `aux` (forward order), multiply every
coefficient by `i ^ q` from `aux` onto `aux2` (reversed), and move `aux2` back (forward). -/
def classPass (q : Fin 4) : Pr P T Q A U :=
  .seq (moveR (ρ (.cls q)) (ρ .aux) id)
    (.seq (autoWords (fun _ => ρ .aux) (fun _ => ρ .aux2) st (ρ .wc) (ρ .tmp) (unitAuto A q))
      (moveR (ρ .aux2) (ρ (.cls q)) id))

/-- The phase program: route the records by class, multiply class `q` by `i ^ q`, merge the
classes back in record order onto `aux`, and move the result (forward) onto `arr`. -/
def phaseProg (c : ZMod 4) : Pr P T Q A U :=
  .seq (routeIdx (ρ .arr) (fun q => ρ (.cls q)) (ρ .rc) (ρ .tmp) (fun _ : Fin 1 => ρ .af)
      (phaseRs ρ) (phaseTmps ρ) st (phaseCode c))
    (.seq (Prog.seqList ((List.finRange 4).map (classPass ρ st)))
      (.seq (mergeIdx (fun q => ρ (.cls q)) (ρ .aux) (ρ .rc) (ρ .tmp) (ρ .cnt) (ρ .aux2)
          (fun _ : Fin 1 => ρ .af) (phaseRs ρ) (phaseTmps ρ) st (phaseCode c))
        (moveR (ρ .aux) (ρ .arr) id)))

variable {ρ st}

lemma classLayout (hρ : Function.Injective ρ) (hst : ρ .aux ≠ st) :
    AutoLayout (fun _ : Fin 1 => ρ .aux) (fun _ : Fin 1 => ρ .aux2) st (ρ .wc) (ρ .tmp) where
  ins_inj := Function.injective_of_subsingleton _
  outs_inj := Function.injective_of_subsingleton _
  ins_outs _ _ := hρ.ne (by simp)
  ins_ctr _ := hρ.ne (by simp)
  ins_tmp _ := hρ.ne (by simp)
  outs_ctr _ := hρ.ne (by simp)
  outs_tmp _ := hρ.ne (by simp)
  ctr_tmp := hρ.ne (by simp)
  ins_st _ := hst

/-- One class pass: the class register holding the reversed stream of the coefficients `zs`
ends holding the forward stream of `zs` multiplied by `i ^ q`; every other register ends as it
started. -/
theorem classPass_exec (hρ : Function.Injective ρ) (hst : ρ .aux ≠ st) (hA : 5 ≤ A) {w : ℕ}
    (hw : 1 ≤ w) {ws : List (Fin (A + 4))} (hws : ws.length = w) (q : Fin 4) (zs : List (GR w))
    (v : HS T Q A U) (S : Stacks T A)
    (hcl : S.R (ρ (.cls q)) = (zs.flatMap (coeffSyms A w)).reverse) (haux : S.R (ρ .aux) = [])
    (haux2 : S.R (ρ .aux2) = []) (hwc : S.R (ρ .wc) = ws) (htmp : S.R (ρ .tmp) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ zs.length * (9 * w + 6) + 6 ∧
      Exec body (classPass ρ st q) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (ρ (.cls q))
            ((zs.map (GR.mulG (unitG q).1 (unitG q).2)).flatMap (coeffSyms A w)) }) := by
  have h1 : ρ (.cls q) ≠ ρ .aux := hρ.ne (by simp)
  have h2 : ρ (.cls q) ≠ ρ .aux2 := hρ.ne (by simp)
  have h3 : ρ .aux ≠ ρ .aux2 := hρ.ne (by simp)
  have hlen : (zs.flatMap (coeffSyms A w)).length = zs.length * w :=
    length_flatMap_const _ w (length_coeffSyms A w) zs
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body (ρ (.cls q)) (ρ .aux) h1 id v S
  set S₁ : Stacks T A := { S with R := movedR S.R (ρ (.cls q)) (ρ .aux) id (S.R (ρ (.cls q))) }
    with hS₁
  have hS₁aux : S₁.R (ρ .aux) = zs.flatMap (coeffSyms A w) := by
    simp [hS₁, movedR, hcl, haux]
  have hS₁oth : ∀ k, k ≠ ρ (.cls q) → k ≠ ρ .aux → S₁.R k = S.R k := by
    intro k hk1 hk2
    simp [hS₁, movedR, hk1, hk2]
  obtain ⟨v₂, m₂, S₂, hu₂, hm₂, he₂, hi₂, ho₂, hl₂, hins, houts, hoth⟩ :=
    mulG_exec body (classLayout hρ hst) (unitG q).1 (unitG q).2 (by omega)
      (by rw [unitG_natAbs]; omega) hw hws zs v₁ S₁
      (by rw [hS₁oth _ (hρ.ne (by simp)) (hρ.ne (by simp))]; exact hwc)
      (by rw [hS₁oth _ (hρ.ne (by simp)) (hρ.ne (by simp))]; exact htmp) hS₁aux
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (ρ .aux2) (ρ (.cls q)) (Ne.symm h2) id v₂ S₂
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · rw [houts, hS₁oth _ (Ne.symm h2) (Ne.symm h3), haux2, List.append_nil, hcl,
      List.length_reverse, List.length_reverse, hlen,
      length_flatMap_const _ w (length_coeffSyms A w), List.length_map]
    have : zs.length * (9 * w + 6) = 4 * (zs.length * w) + zs.length * (5 * w + 6) := by ring
    omega
  · congr 1
    refine Stacks.ext (by rw [hi₂]) (by rw [ho₂]) (by rw [hl₂]) ?_
    funext k
    simp only [movedR]
    by_cases hk : k = ρ (.cls q)
    · subst hk
      rw [Function.update_self, Function.update_self, houts,
        hoth _ h1 h2, hS₁oth _ (Ne.symm h2) (Ne.symm h3), haux2]
      simp [hS₁, movedR, Function.update_of_ne h1]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases hk2 : k = ρ .aux2
      · subst hk2; rw [Function.update_self, haux2]
      · rw [Function.update_of_ne hk2]
        by_cases hk3 : k = ρ .aux
        · subst hk3; rw [hins, haux]
        · rw [hoth _ hk3 hk2, hS₁oth _ hk hk3]

/-- The class passes over a duplicate-free list `qs` of classes. -/
theorem classPasses_exec (hρ : Function.Injective ρ) (hst : ρ .aux ≠ st) (hA : 5 ≤ A) {w : ℕ}
    (hw : 1 ≤ w) {ws : List (Fin (A + 4))} (hws : ws.length = w) (zs : Fin 4 → List (GR w)) :
    ∀ (qs : List (Fin 4)), qs.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      (∀ q ∈ qs, S.R (ρ (.cls q)) = ((zs q).flatMap (coeffSyms A w)).reverse) →
      S.R (ρ .aux) = [] → S.R (ρ .aux2) = [] → S.R (ρ .wc) = ws → S.R (ρ .tmp) = [] →
      ∃ (v' : HS T Q A U) (m : ℕ) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        m ≤ (qs.map fun q => (zs q).length * (9 * w + 6) + 6).sum + 1 ∧
        Exec body (Prog.seqList (qs.map (classPass ρ st))) (mk v S) m (mk v' { S with R := R' }) ∧
        (∀ q ∈ qs, R' (ρ (.cls q)) =
          ((zs q).map (GR.mulG (unitG q).1 (unitG q).2)).flatMap (coeffSyms A w)) ∧
        ∀ k, (∀ q ∈ qs, ρ (.cls q) ≠ k) → R' k = S.R k := by
  intro qs
  induction qs with
  | nil =>
      intro _ v S _ _ _ _ _
      have he := Exec.act (body := body) .done (mk v S)
      exact ⟨v, 1, S.R, rfl, by simp, by simpa [Prog.seqList] using he, by simp, fun _ _ => rfl⟩
  | cons q qs ih =>
      intro hnd v S hcl haux haux2 hwc htmp
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := classPass_exec body hρ hst hA hw hws q (zs q) v S
        (hcl q List.mem_cons_self) haux haux2 hwc htmp
      have hfr : ∀ x, x ≠ PhaseReg.cls q →
          Function.update S.R (ρ (.cls q)) (((zs q).map (GR.mulG (unitG q).1 (unitG q).2)).flatMap
            (coeffSyms A w)) (ρ x) = S.R (ρ x) :=
        fun x hx => Function.update_of_ne (hρ.ne hx) _ _
      obtain ⟨v', m, R', hu, hm, he, hcls, hoth⟩ := ih hnd.2 v₁
        { S with
          R := Function.update S.R (ρ (.cls q))
            (((zs q).map (GR.mulG (unitG q).1 (unitG q).2)).flatMap (coeffSyms A w)) }
        (fun q' hq' => (hfr _ (fun e => hnd.1 (by cases e; exact hq'))).trans
          (hcl q' (List.mem_cons_of_mem _ hq')))
        ((hfr _ (by simp)).trans haux) ((hfr _ (by simp)).trans haux2)
        ((hfr _ (by simp)).trans hwc) ((hfr _ (by simp)).trans htmp)
      refine ⟨v', m₁ + m, R', by rw [hu, hu₁], ?_, Exec.seq he₁ he, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        omega
      · intro q' hq'
        rcases List.mem_cons.1 hq' with rfl | hq'
        · rw [hoth _ (fun q'' hq'' e => hnd.1 (by
            have := hρ e; cases this; exact hq''))]
          exact Function.update_self _ _ _
        · exact hcls q' hq'
      · intro k hk
        rw [hoth k (fun q' hq' => hk q' (List.mem_cons_of_mem _ hq'))]
        exact Function.update_of_ne (Ne.symm (hk q List.mem_cons_self)) _ _

/-- The address field reads the index modulo `2 ^ n`. -/
lemma digit_phase (n : ℕ) (f : Fin 1) (i : ℕ) : digit (fun _ : Fin 1 => n) f i = i % 2 ^ n := by
  simp [digit, fieldOff_zero _ f (Nat.lt_one_iff.1 f.isLt)]

/-- The index layout of the phase program beside the stream registers `X`. -/
lemma phaseIdxLayout (hρ : Function.Injective ρ) (hst : ∀ x ∈ [PhaseReg.af, .msk, .t0, .t1], ρ x ≠ st)
    (n mnum : ℕ) (X : Fin T → Prop) (hX : ∀ x ∈ [PhaseReg.af, .msk, .t0, .t1], ¬ X (ρ x)) :
    IdxLayout (fun _ : Fin 1 => ρ .af) (fun _ => n) n (phaseRs ρ) (phaseTmps ρ) (phaseSrc mnum) st
      X where
  rs_inj := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h (hρ.ne (by simp))
    · exact absurd h (hρ.ne (by simp))
    · rfl
  tmps_inj := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h (hρ.ne (by simp))
    · exact absurd h (hρ.ne (by simp))
    · rfl
  rs_tmps i j := by
    fin_cases i <;> fin_cases j <;> exact hρ.ne (by simp)
  rs_st i := by
    fin_cases i
    · exact hst _ (by simp)
    · exact hst _ (by simp)
  tmps_st i := by
    fin_cases i
    · exact hst _ (by simp)
    · exact hst _ (by simp)
  cf_inj := Function.injective_of_subsingleton _
  tmps_cf i _ := by fin_cases i <;> exact hρ.ne (by simp)
  field r f hr := by
    fin_cases r
    · exact ⟨rfl, rfl⟩
    · simp [phaseSrc] at hr
  param r p f hr := by
    fin_cases r
    · simp [phaseSrc] at hr
    · exact hρ.ne (by simp)
  cf_X _ := hX _ (by simp)
  rs_X r := by fin_cases r <;> exact hX _ (by simp)
  tmps_X r := by fin_cases r <;> exact hX _ (by simp)

/-- The index registers at an index `i ≡ 0` modulo `2 ^ n`. -/
lemma phaseIdxState {Rg : Fin T → List (Fin (A + 4))} {n mnum i : ℕ} (hi : i % 2 ^ n = 0)
    (haf : Rg (ρ .af) = binSyms n 0) (hmsk : Rg (ρ .msk) = binSyms n mnum)
    (ht0 : Rg (ρ .t0) = []) (ht1 : Rg (ρ .t1) = []) :
    IdxState (fun _ : Fin 1 => ρ .af) (fun _ => n) n (phaseRs ρ) (phaseTmps ρ) (phaseSrc mnum)
      Rg i := by
  refine ⟨fun _ => by rw [haf, digit_phase, hi], fun r p hr => ?_, fun r => ?_⟩
  · fin_cases r
    · simp [phaseSrc] at hr
    · simp only [phaseSrc] at hr
      have : p = mnum := by simpa using hr.symm
      subst this
      exact hmsk
  · fin_cases r
    · exact ht0
    · exact ht1

/-- **The phase program.** The array register holds the stream of `Z`, the mask register the
low `n` bits of `mnum` with `addrBits n mnum = mask`, the address field `n` zero bits, the record
counter `r * w` symbols, the coefficient counter `w` symbols, the count register `R * 2 ^ n`
symbols, and the other spares are empty. Afterwards the array register holds the stream of
`phaseZ mask c Z` and every other register ends as it started. -/
theorem phaseProg_exec (hρ : Function.Injective ρ)
    (hst : ∀ x ∈ [PhaseReg.aux, .af, .msk, .t0, .t1], ρ x ≠ st) (hA : 5 ≤ A)
    {R r n w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (c : ZMod 4) (mask : Fin n → ZMod 2) (mnum : ℕ)
    (hmask : addrBits n mnum = mask) (Z : ZArr (Fin R × Fin r) n)
    {cs ws kk : List (Fin (A + 4))} (hcs : cs.length = r * w) (hws : ws.length = w)
    (hkk : kk.length = R * 2 ^ n) (v : HS T Q A U) (S : Stacks T A)
    (harr : S.R (ρ .arr) = encZ A w Z) (hcls : ∀ q, S.R (ρ (.cls q)) = [])
    (hrc : S.R (ρ .rc) = cs) (hwc : S.R (ρ .wc) = ws) (htmp : S.R (ρ .tmp) = [])
    (haux : S.R (ρ .aux) = []) (haux2 : S.R (ρ .aux2) = []) (haf : S.R (ρ .af) = binSyms n 0)
    (hmsk : S.R (ρ .msk) = binSyms n mnum) (ht0 : S.R (ρ .t0) = []) (ht1 : S.R (ρ .t1) = [])
    (hcnt : S.R (ρ .cnt) = kk) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ R * 2 ^ n * (25 * r * w + 20 * n + 36) + 33 ∧
      Exec body (phaseProg ρ st c) (mk v S) m
        (mk v' { S with R := Function.update S.R (ρ .arr) (encZ A w (phaseZ mask c Z)) }) := by
  set code := idxCode (phaseCode (A := A) c) n (fun _ : Fin 1 => n) (phaseSrc mnum) with hcode
  set nb := R * 2 ^ n with hnb
  have hnb0 : (0 + nb) % 2 ^ n = 0 := by rw [Nat.zero_add, hnb, Nat.mul_mod_left]
  have hst' : ∀ x ∈ [PhaseReg.af, .msk, .t0, .t1], ρ x ≠ st :=
    fun x hx => hst x (List.mem_cons_of_mem _ hx)
  have hB : 1 ≤ r * w := Nat.mul_le_mul hr hw
  -- routing
  obtain ⟨v₁, R₁, hu₁, he₁, harr₁, hcls₁, haf₁, hoth₁⟩ :=
    routeIdx_exec body (ρ .arr) (fun q => ρ (.cls q)) (ρ .rc) (ρ .tmp) (fun _ : Fin 1 => ρ .af)
      (fun _ => n) n (phaseRs ρ) (phaseTmps ρ) (phaseSrc mnum) st (phaseCode c)
      (phaseIdxLayout hρ hst' n mnum _ (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [routeRegs, hρ.eq_iff]))
      (List.Nodup.map hρ (by decide) : ([PhaseReg.arr, .rc, .tmp].map ρ).Nodup)
      (fun d => by simp [hρ.eq_iff]) (fun a b h => by simpa using hρ h)
      (l := encZ A w Z) (c := cs) (nb := nb) (B := r * w) (i₀ := 0) hB (length_encZ Z) hcs v S
      harr hrc htmp (phaseIdxState (by simp) haf hmsk ht0 ht1)
  have hfr₁ : ∀ x, x ≠ .arr → (∀ d, x ≠ .cls d) → x ≠ .af → R₁ (ρ x) = S.R (ρ x) :=
    fun x h1 h2 h3 => hoth₁ _ (hρ.ne h1) (fun d => hρ.ne (fun e => h2 d e.symm))
      (fun _ => hρ.ne (Ne.symm h3))
  set zs : Fin 4 → List (GR w) := fun d => blocksIdx (coeffList w Z) r nb code 0 d with hzs
  have hcl₁ : ∀ q, R₁ (ρ (.cls q)) = ((zs q).flatMap (coeffSyms A w)).reverse := by
    intro q
    rw [hcls₁, hcls, List.append_nil, encZ, blocksIdx_flatMap _ w (length_coeffSyms A w)]
  -- the class passes
  obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hcls₂, hoth₂⟩ :=
    classPasses_exec body hρ (hst _ (by simp)) hA hw hws zs (List.finRange 4)
      (List.nodup_finRange 4) v₁ { S with R := R₁ } (fun q _ => hcl₁ q)
      ((hfr₁ _ (by simp) (by simp) (by simp)).trans haux)
      ((hfr₁ _ (by simp) (by simp) (by simp)).trans haux2)
      ((hfr₁ _ (by simp) (by simp) (by simp)).trans hwc)
      ((hfr₁ _ (by simp) (by simp) (by simp)).trans htmp)
  dsimp only at hoth₂
  have hfr₂ : ∀ x, (∀ d, x ≠ .cls d) → R₂ (ρ x) = R₁ (ρ x) :=
    fun x h => hoth₂ _ (fun q _ => hρ.ne (fun e => h q e.symm))
  have hS₂ : ∀ x, x ≠ .arr → (∀ d, x ≠ .cls d) → x ≠ .af → R₂ (ρ x) = S.R (ρ x) :=
    fun x h1 h2 h3 => (hfr₂ x h2).trans (hfr₁ x h1 h2 h3)
  have haf₂ : R₂ (ρ .af) = binSyms n 0 := by
    rw [hfr₂ _ (by simp), haf₁ 0, digit_phase, hnb0]
  -- merging
  obtain ⟨v₃, R₃, hu₃, he₃, haux₃, hcls₃, haf₃, hoth₃⟩ :=
    mergeIdx_exec_blocks body (fun q => ρ (.cls q)) (ρ .aux) (ρ .rc) (ρ .tmp) (ρ .cnt) (ρ .aux2)
      (fun _ : Fin 1 => ρ .af) (fun _ => n) n (phaseRs ρ) (phaseTmps ρ) (phaseSrc mnum) st
      (phaseCode c)
      (phaseIdxLayout hρ hst' n mnum _ (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [mergeRegs, hρ.eq_iff]))
      (List.Nodup.map hρ (by decide) : ([PhaseReg.aux, .rc, .tmp, .cnt, .aux2].map ρ).Nodup)
      (fun d => by simp [hρ.eq_iff]) (fun a b h => by simpa using hρ h)
      (l := encZ A w (phaseZ mask c Z)) (c := cs) (kk := kk) (nb := nb) (B := r * w) (i₀ := 0)
      (length_encZ _) hcs hkk (fun _ => []) v₂ { S with R := R₂ }
      (fun d => by
        rw [List.append_nil, ← blocksIdx_encZ_phase Z mask c mnum hmask d]
        exact hcls₂ d (List.mem_finRange d))
      ((hS₂ _ (by simp) (by simp) (by simp)).trans hrc)
      ((hS₂ _ (by simp) (by simp) (by simp)).trans htmp)
      ((hS₂ _ (by simp) (by simp) (by simp)).trans hcnt)
      ((hS₂ _ (by simp) (by simp) (by simp)).trans haux2)
      (phaseIdxState (by simp) haf₂ ((hS₂ _ (by simp) (by simp) (by simp)).trans hmsk)
        ((hS₂ _ (by simp) (by simp) (by simp)).trans ht0)
        ((hS₂ _ (by simp) (by simp) (by simp)).trans ht1))
  dsimp only at haux₃ hoth₃
  -- back to the array register
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body (ρ .aux) (ρ .arr) (hρ.ne (by simp)) id v₃
    { S with R := R₃ }
  have haux₃' : R₃ (ρ .aux) = (encZ A w (phaseZ mask c Z)).reverse := by
    rw [haux₃, hS₂ _ (by simp) (by simp) (by simp), haux, List.append_nil]
  have harr₃ : R₃ (ρ .arr) = [] := by
    rw [hoth₃ _ (hρ.ne (by simp)) (fun d => hρ.ne (by simp)) (fun _ => hρ.ne (by simp)),
      hfr₂ _ (by simp), harr₁]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · -- the step count
    dsimp only
    have hzlen : ∀ q, (zs q).length = idxCount code 0 nb q * r := fun q =>
      length_blocksIdx code r nb 0 (coeffList w Z) q (by rw [length_coeffList])
    have hsum : ((List.finRange 4).map fun q => (zs q).length * (9 * w + 6) + 6).sum =
        nb * (r * (9 * w + 6)) + 24 := by
      rw [← Fin.sum_univ_def, Finset.sum_add_distrib]
      simp only [hzlen]
      rw [show (∑ q : Fin 4, idxCount code 0 nb q * r * (9 * w + 6)) =
          (∑ q : Fin 4, idxCount code 0 nb q) * (r * (9 * w + 6)) by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun q _ => by ring,
        sum_idxCount]
      simp
    rw [hsum] at hm₂
    rw [haux₃', List.length_reverse, length_encZ, ← hnb]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul]
    have hrw : r ≤ r * w := Nat.le_mul_of_pos_right r hw
    have hZ : nb * r ≤ nb * (r * w) := Nat.mul_le_mul_left _ hrw
    have e1 : nb * (4 * (r * w) + 6 * n + 4 * n + 4 * 1 + 13) =
        4 * (nb * (r * w)) + 10 * (nb * n) + 17 * nb := by ring
    have e2 : nb * (4 * (r * w) + 6 * n + 4 * n + 4 * 1 + 15) =
        4 * (nb * (r * w)) + 10 * (nb * n) + 19 * nb := by ring
    have e3 : nb * (r * (9 * w + 6)) = 9 * (nb * (r * w)) + 6 * (nb * r) := by ring
    have e4 : nb * (25 * r * w + 20 * n + 36) = 25 * (nb * (r * w)) + 20 * (nb * n) + 36 * nb := by
      ring
    rw [e1, e2, e4]
    rw [e3] at hm₂
    omega
  · -- the final registers
    congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [movedR]
    by_cases hka : k = ρ .arr
    · subst hka
      rw [Function.update_self, Function.update_self, haux₃', harr₃]
      simp
    rw [Function.update_of_ne hka, Function.update_of_ne hka]
    by_cases hkx : k = ρ .aux
    · subst hkx
      rw [Function.update_self, haux]
    rw [Function.update_of_ne hkx]
    by_cases hkc : ∃ d, ρ (.cls d) = k
    · obtain ⟨d, rfl⟩ := hkc
      rw [hcls₃ d, hcls d]
    push Not at hkc
    by_cases hkf : k = ρ .af
    · subst hkf
      rw [haf₃ 0, digit_phase, hnb0, haf]
    rw [hoth₃ _ hkx hkc (fun _ => Ne.symm hkf), hoth₂ _ (fun q _ => hkc q),
      hoth₁ _ hka hkc (fun _ => Ne.symm hkf)]

end Program

end IntegerMultBounds.MathlibTM2.Node
