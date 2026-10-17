module

public import IntegerMultBounds.MathlibTM2.Layer.NodeZ
public import IntegerMultBounds.MathlibTM2.Layer.GaussLin
public import IntegerMultBounds.MathlibTM2.Host.Route
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# Streams of Gaussian-integer arrays

An array `Z : ZArr (Fin R × Fin r) n` is stored row by row; a row holds the records of the
`2^n` addresses in increasing order (address `a` has bits `addrBits n a`), and a record holds
the `r` coefficients, each reduced modulo `2^w` (`coeffList`). The symbol stream is
`encZ = (coeffList Z).flatMap (coeffSyms A w)`.

The lemmas translate stream passes into array operations:
* `coeffList_map`, `coeffList_zip`: a coefficientwise pass (one Gaussian automaton reading the
  aligned coefficients of several arrays) computes the reduction of a pointwise integer map;
* `blocksTo_roles`, `roleArr_unroles`, `unroles_roleArr`: routing the rows by `u % W` gives the
  arrays of the row roles `u = W g + i`, and `unroles` reassembles the array;
* `recList`, `recList_pull`: an address permutation inside every row permutes the records.

Proof devices: `coeffList_eq_map` writes the coefficient list as the reduction of the array along
the fixed list of cells `cellList`; `coeffList_eq_rows` writes it as the concatenation of the rows
`rowCoeffs`, each of length `2^n r`. Lists `l.flatMap f` with `f` of constant length `k` have
blocks of length `k` (`block_flatMap_const`), and `blocksTo` commutes with such a `flatMap`
(`blocksTo_flatMap`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.MathlibTM2.Host

/-! ### Concatenations of constant-length pieces -/

section ListHelpers

variable {α β : Type}

lemma length_flatMap_const (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) (l : List α) :
    (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, hf, ih, Nat.succ_mul, Nat.add_comm]

/-- Dropping `j` pieces of length `k`. -/
lemma drop_flatMap_const (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) (l : List α)
    (j : ℕ) : (l.flatMap f).drop (j * k) = (l.drop j).flatMap f := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.flatMap_cons, List.drop_append, hf, List.drop_eq_nil_of_le (by rw [hf]; nlinarith),
        show (j + 1) * k - k = j * k by rw [Nat.succ_mul, Nat.add_sub_cancel], ih]
      simp

/-- Taking `j` pieces of length `k`. -/
lemma take_flatMap_const (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) (l : List α)
    (j : ℕ) : (l.flatMap f).take (j * k) = (l.take j).flatMap f := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.flatMap_cons, List.take_append, hf, List.take_of_length_le (by rw [hf]; nlinarith),
        show (j + 1) * k - k = j * k by rw [Nat.succ_mul, Nat.add_sub_cancel], ih]
      simp

/-- Block `m` of length `k` is the `m`-th piece. -/
lemma block_flatMap_const (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) (l : List α)
    (m : ℕ) (hm : m < l.length) : ((l.flatMap f).drop (m * k)).take k = f l[m] := by
  have h1 := take_flatMap_const f k hf (l.drop m) 1
  rw [one_mul] at h1
  rw [drop_flatMap_const f k hf, h1, List.drop_eq_getElem_cons hm]
  simp only [List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- Entry `k m + a` is entry `a` of the `m`-th piece. -/
lemma getElem_flatMap_const (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) (l : List α)
    (m a : ℕ) (hm : m < l.length) (ha : a < k) (h : k * m + a < (l.flatMap f).length) :
    (l.flatMap f)[k * m + a] = (f l[m])[a]'(by rw [hf]; exact ha) := by
  have hb := block_flatMap_const f k hf l m hm
  have hl : a < (((l.flatMap f).drop (m * k)).take k).length := by rw [hb, hf]; exact ha
  calc (l.flatMap f)[k * m + a] = (((l.flatMap f).drop (m * k)).take k)[a]'hl := by
        simp [Nat.mul_comm]
    _ = (f l[m])[a]'(by rw [hf]; exact ha) := by simp only [hb]

/-- Routing commutes with expanding every element into `k` elements: blocks of `B` elements
become blocks of `B k` elements. -/
lemma blocksTo_flatMap {nd : ℕ} (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k)
    (l : List α) (B W nb : ℕ) (sel : ℕ → Fin nd) (d : Fin nd) :
    blocksTo (l.flatMap f) (B * k) W nb sel d = (blocksTo l B W nb sel d).flatMap f := by
  unfold blocksTo
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun m _ => ?_
  rw [← Nat.mul_assoc, drop_flatMap_const f k hf, take_flatMap_const f k hf]

lemma flatMap_range_dite (N : ℕ) (h : Fin N → List α) :
    (List.range N).flatMap (fun m => if hm : m < N then h ⟨m, hm⟩ else []) =
      (List.finRange N).flatMap h := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  exact List.flatMap_congr fun u _ => by simp [u.2]

/-- The indices below `W R'` with residue `i` modulo `W`. -/
lemma filter_range_mod (W R' i : ℕ) (hi : i < W) :
    (List.range (W * R')).filter (fun m => m % W = i) = (List.range R').map (fun g => W * g + i) := by
  induction R' with
  | zero => simp
  | succ R' ih =>
    rw [Nat.mul_succ, List.range_add, List.filter_append, ih, List.range_succ, List.map_append,
      List.filter_map]
    congr 1
    have h1 : (List.range W).filter ((fun m => decide (m % W = i)) ∘ fun x => W * R' + x) =
        (List.range W).filter (· = i) := by
      refine List.filter_congr fun x hx => ?_
      have hx' : x < W := List.mem_range.1 hx
      simp [Nat.mod_eq_of_lt hx']
    rw [h1, List.filter_eq, List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hi)]
    simp

end ListHelpers

variable {R r n w : ℕ}

/-- The bit vector of an address. -/
def addrBits (n a : ℕ) : Fin n → ZMod 2 := fun t => if a.testBit t then 1 else 0

/-- The records of an array in stream order; each is the list of its reduced coefficients. -/
def recList (w : ℕ) (Z : ZArr (Fin R × Fin r) n) : List (List (GR w)) :=
  (List.finRange R).flatMap fun u => (List.range (2 ^ n)).map fun a =>
    List.ofFn fun c : Fin r => red w (Z ((u, c), addrBits n a))

/-- The coefficients of an array in stream order. -/
def coeffList (w : ℕ) (Z : ZArr (Fin R × Fin r) n) : List (GR w) := (recList w Z).flatten

/-- The symbol stream of an array. -/
def encZ (A w : ℕ) (Z : ZArr (Fin R × Fin r) n) : List (Fin (A + 4)) :=
  (coeffList w Z).flatMap (coeffSyms A w)

/-- The cells of an array in stream order. -/
def cellList (R r n : ℕ) : List ((Fin R × Fin r) × (Fin n → ZMod 2)) :=
  (List.finRange R).flatMap fun u => (List.range (2 ^ n)).flatMap fun a =>
    List.ofFn fun c : Fin r => ((u, c), addrBits n a)

/-- The coefficients of row `u` in stream order. -/
def rowCoeffs (w : ℕ) (Z : ZArr (Fin R × Fin r) n) (u : Fin R) : List (GR w) :=
  (List.range (2 ^ n)).flatMap fun a => List.ofFn fun c : Fin r => red w (Z ((u, c), addrBits n a))

lemma length_cellList : (cellList R r n).length = R * 2 ^ n * r := by
  rw [cellList, length_flatMap_const _ (2 ^ n * r)]
  · simp [Nat.mul_assoc]
  · intro u
    rw [length_flatMap_const _ r (by simp)]
    simp

/-- The coefficient list is the reduction of the array along `cellList`. -/
lemma coeffList_eq_map (Z : ZArr (Fin R × Fin r) n) :
    coeffList w Z = (cellList R r n).map fun p => red w (Z p) := by
  simp [coeffList, recList, cellList, List.flatMap_def, List.flatten_flatten, List.map_flatten,
    Function.comp_def, List.map_ofFn]

/-- The coefficient list is the concatenation of the rows. -/
lemma coeffList_eq_rows (Z : ZArr (Fin R × Fin r) n) :
    coeffList w Z = (List.finRange R).flatMap (rowCoeffs w Z) := by
  show _ = (List.finRange R).flatMap fun u => rowCoeffs w Z u
  simp [coeffList, recList, rowCoeffs, List.flatMap_def, List.flatten_flatten, Function.comp_def]

lemma length_rowCoeffs (Z : ZArr (Fin R × Fin r) n) (u : Fin R) :
    (rowCoeffs w Z u).length = 2 ^ n * r := by
  rw [rowCoeffs, length_flatMap_const _ r (by simp)]
  simp

theorem length_recList (Z : ZArr (Fin R × Fin r) n) : (recList w Z).length = R * 2 ^ n := by
  rw [recList, length_flatMap_const _ (2 ^ n) (by simp)]
  simp

theorem length_coeffList (Z : ZArr (Fin R × Fin r) n) :
    (coeffList w Z).length = R * 2 ^ n * r := by
  rw [coeffList_eq_map, List.length_map, length_cellList]

lemma zmod2_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

lemma ite_zmod2 (x : ZMod 2) (c : ℕ) : (if x = 1 then c else 0) = x.val * c := by
  rcases zmod2_zero_or_one x with rfl | rfl
  · simp
  · simp [ZMod.val_one]

/-- A bit vector with values in `Fin 2`. -/
def finBits (v : Fin n → ZMod 2) : Fin n → Fin 2 := fun t => ⟨(v t).val, ZMod.val_lt _⟩

/-- The number with bits `v` is the base-2 value of `finBits v`. -/
lemma bitsNum_eq (v : Fin n → ZMod 2) :
    (∑ t : Fin n, if v t = 1 then 2 ^ (t : ℕ) else 0) = (finFunctionFinEquiv (finBits v) : ℕ) := by
  rw [finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ite_zmod2]; rfl

lemma bitsNum_lt (v : Fin n → ZMod 2) :
    (∑ t : Fin n, if v t = 1 then 2 ^ (t : ℕ) else 0) < 2 ^ n := by
  rw [bitsNum_eq]; exact Fin.isLt _

lemma addrBits_bitsNum (v : Fin n → ZMod 2) :
    addrBits n (∑ t : Fin n, if v t = 1 then 2 ^ (t : ℕ) else 0) = v := by
  funext t
  rw [bitsNum_eq]
  have h1 := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv (finBits v)) t
  rw [Equiv.symm_apply_apply] at h1
  simp only [addrBits, Nat.testBit_eq_decide_div_mod_eq, ← h1, finBits]
  rcases zmod2_zero_or_one (v t) with h | h <;> rw [h] <;> simp [ZMod.val_one]

/-- `addrBits` is a bijection from `[0, 2^n)` onto bit vectors. -/
theorem addrBits_bijOn : Set.BijOn (addrBits n) (Set.Iio (2 ^ n)) Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, fun v _ => ⟨_, bitsNum_lt v, addrBits_bitsNum v⟩⟩
  intro a ha b hb hab
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrFun hab ⟨i, hi⟩
    simp only [addrBits] at this
    cases h1 : a.testBit i <;> cases h2 : b.testBit i <;> simp_all
  · have hn : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (Set.mem_Iio.1 ha) hn),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (Set.mem_Iio.1 hb) hn)]

/-! ### Coefficientwise passes -/

/-- A pointwise integer map whose reduction is `ψ` acts on the coefficient list by `ψ`. -/
theorem coeffList_map (φ : GaussianInt → GaussianInt) (ψ : GR w → GR w)
    (h : ∀ z, red w (φ z) = ψ (red w z)) (Z : ZArr (Fin R × Fin r) n) :
    coeffList w (fun p => φ (Z p)) = (coeffList w Z).map ψ := by
  rw [coeffList_eq_map, coeffList_eq_map, List.map_map]
  exact List.map_congr_left fun p _ => h (Z p)

/-- Several arrays combined pointwise by a map whose reduction is `G`. -/
theorem coeffList_zip {ι : Type} (F : (ι → GaussianInt) → GaussianInt) (G : (ι → GR w) → GR w)
    (h : ∀ z, red w (F z) = G (fun i => red w (z i))) (Z : ι → ZArr (Fin R × Fin r) n) :
    coeffList w (fun p => F (fun i => Z i p)) =
      List.ofFn fun t : Fin (R * 2 ^ n * r) =>
        G (fun i => (coeffList w (Z i))[t]'(by rw [length_coeffList]; exact t.2)) := by
  apply List.ext_getElem
  · simp [length_coeffList]
  · intro t h1 h2
    simp only [coeffList_eq_map, List.getElem_map, List.getElem_ofFn, Fin.getElem_fin, h]

/-- The Gaussian-linear reduction: `glin` of the reductions is the reduction of the integer
combination. -/
theorem red_glin {k l : ℕ} (g : Fin l → Fin k → ℤ × ℤ) (z : Fin k → GaussianInt) (j : Fin l) :
    red w (∑ i, (⟨(g j i).1, (g j i).2⟩ : GaussianInt) * z i) = glin g (fun i => red w (z i)) j := by
  rw [glin_eq_sum_mulG]
  have hs := map_sum (AddMonoidHom.mk' (red w) (red_add w))
    (fun i => (⟨(g j i).1, (g j i).2⟩ : GaussianInt) * z i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  simp only [red_mulG]

/-! ### Row roles -/

/-- The selector of a row role: `u ↦ u % W`. -/
def roleSel (W : ℕ) [NeZero W] (u : ℕ) : Fin W := ⟨u % W, Nat.mod_lt _ (Nat.pos_of_neZero W)⟩

lemma role_lt {W R' g i : ℕ} (hg : g < R') (hi : i < W) : W * g + i < W * R' := by
  have : W * (g + 1) ≤ W * R' := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega

/-- The array of row role `i`: row `g` is row `W g + i` of `Z`. -/
def roleArr (W R' : ℕ) (i : Fin W) (Z : ZArr (Fin (W * R') × Fin r) n) : ZArr (Fin R' × Fin r) n :=
  fun p => Z ((⟨W * p.1.1 + i, role_lt p.1.1.2 i.2⟩, p.1.2), p.2)

/-- Routing the rows by role. -/
theorem blocksTo_roles (W R' : ℕ) [NeZero W] (Z : ZArr (Fin (W * R') × Fin r) n) (i : Fin W) :
    blocksTo (coeffList w Z) (2 ^ n * r) W (W * R') (roleSel W) i = coeffList w (roleArr W R' i Z) := by
  rw [coeffList_eq_rows, coeffList_eq_rows, blocksTo,
    List.filter_congr (q := fun m => decide (m % W = i.val))
      (fun m _ => by simp [roleSel, Fin.ext_iff]),
    filter_range_mod W R' i i.2, List.flatMap_map,
    ← flatMap_range_dite R' (rowCoeffs w (roleArr W R' i Z))]
  refine List.flatMap_congr fun g hg => ?_
  have hg' : g < R' := List.mem_range.1 hg
  rw [dite_eq_left hg', block_flatMap_const _ _ (length_rowCoeffs Z) _ _
    (by rw [List.length_finRange]; exact role_lt hg' i.2)]
  simp [rowCoeffs, roleArr]

/-- Symbol-level form of `blocksTo_roles`. -/
theorem blocksTo_roles_syms (A W R' : ℕ) [NeZero W] (Z : ZArr (Fin (W * R') × Fin r) n) (i : Fin W) :
    blocksTo (encZ A w Z) (2 ^ n * r * w) W (W * R') (roleSel W) i = encZ A w (roleArr W R' i Z) := by
  rw [encZ, encZ, blocksTo_flatMap (coeffSyms A w) w (length_coeffSyms A w), blocksTo_roles]

/-- Reassemble an array from its row roles. -/
def unroles (W R' : ℕ) [NeZero W] (B : Fin W → ZArr (Fin R' × Fin r) n) : ZArr (Fin (W * R') × Fin r) n :=
  fun p => B (roleSel W p.1.1) ((⟨p.1.1 / W, Nat.div_lt_of_lt_mul p.1.1.2⟩,
    p.1.2), p.2)

theorem roleArr_unroles (W R' : ℕ) [NeZero W] (B : Fin W → ZArr (Fin R' × Fin r) n) (i : Fin W) :
    roleArr W R' i (unroles W R' B) = B i := by
  funext p
  have hW : 0 < W := Nat.pos_of_neZero W
  simp only [roleArr, unroles]
  congr 1
  · ext; simp [roleSel, Nat.mod_eq_of_lt i.2]
  · ext
    · simp [Nat.mul_add_div hW, Nat.div_eq_of_lt i.2]
    · rfl
    · rfl

theorem unroles_roleArr (W R' : ℕ) [NeZero W] (Z : ZArr (Fin (W * R') × Fin r) n) :
    unroles W R' (fun i => roleArr W R' i Z) = Z := by
  funext p
  simp only [roleArr, unroles, roleSel]
  congr
  exact Nat.div_add_mod _ _

/-! ### Address permutations inside rows -/

/-- Pull back along a map of addresses applied inside every row. -/
def pullAddr (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (Z : ZArr (Fin R × Fin r) n) :
    ZArr (Fin R × Fin r) n := fun p => Z (p.1, σ p.2)

/-- An address map as a map of address numbers. -/
noncomputable def addrNum (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a : ℕ) : ℕ :=
  ∑ t : Fin n, if σ (addrBits n a) t = 1 then 2 ^ (t : ℕ) else 0

theorem addrNum_lt (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a : ℕ) : addrNum σ a < 2 ^ n :=
  bitsNum_lt _

theorem addrBits_addrNum (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a : ℕ) :
    addrBits n (addrNum σ a) = σ (addrBits n a) :=
  addrBits_bitsNum _

/-- In stream order, record `2^n u + a` of the pulled array is record `2^n u + addrNum σ a` of the
original. -/
theorem recList_pull (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (Z : ZArr (Fin R × Fin r) n)
    (u : ℕ) (hu : u < R) (a : ℕ) (ha : a < 2 ^ n) :
    (recList w (pullAddr σ Z))[2 ^ n * u + a]'(by rw [length_recList]; nlinarith) =
      (recList w Z)[2 ^ n * u + addrNum σ a]'(by
        rw [length_recList]; have := addrNum_lt σ a; nlinarith) := by
  simp only [recList]
  rw [getElem_flatMap_const _ (2 ^ n) (by simp) _ u a (by simpa using hu) ha,
    getElem_flatMap_const _ (2 ^ n) (by simp) _ u (addrNum σ a) (by simpa using hu)
      (addrNum_lt σ a)]
  simp [pullAddr, addrBits_addrNum]

end IntegerMultBounds.MathlibTM2.Layer
