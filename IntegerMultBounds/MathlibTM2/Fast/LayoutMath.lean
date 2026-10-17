module

public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRounds
import Mathlib.Data.Nat.Bitwise

/-!
# The layout of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`: the positional layout permutation `L` of the
record address bits that puts the selected bits of every transform round at a common offset in
consecutive `K`-bit chunks.

## Addresses and moves

The transform has `D = es.length` axes with `aᵢ = ax es i ∈ {ℓ - 1, ℓ}` bits (`LayHyp`), and
`N = es.sum` address bits. Bit `h` of axis `i`, the named slot `(i, h)`, is the logical address
bit `off es i + h` (axis `0` most significant). A layout stores logical bit `j` at physical bit
`L j`, as in `SynthErr.relabel`.

* `layMvFun a b`: the single-bit move from position `a` to position `b`, the positions between
  shifting toward `a` (`layMvFun_lt_lt`: the relative order of the other positions is kept).
* `layXcFun K u w`: the exchange of the `K`-bit chunks at positions `u` and `w`.
* `LayMove`: `bit a b` or `xc u w`; `LayMove.perm K N m` its permutation of `Fin N`;
  `layMovesPerm K N ms` the composite of a list of moves, the head first; `layRun K ms` the same
  map on positions; `layMovesInv ms` the inverse list (`layMovesPerm_inv`).
* `layRec P`: the induced permutation of the `2^N` record addresses (bit `P j` of `layRec P x`
  is bit `j` of `x`); `layRec_trans`, `layRec_symm`. `layRecVal_lt_of`: if `P` keeps the
  relative order of the positions other than `a`, it keeps the order of the records with a common
  bit `a` (used by the single-bit move pass).

## The moves of the layout

With `b = (ℓ - 1) mod K` (`layB`) and `q = ⌊(ℓ - 1)/K⌋` (`layQ`):
* `layPre`: the slots listed for the prefix: `(i, ℓ - 1)` for the long axes in increasing `i`,
  then `(i, h)` for `h = b - 1, …, 0`, increasing `i` within each `h`. `layPreMoves` moves each
  listed slot from its current position (`layPos`) to just below the prefix already formed, at
  the top of the address (`layPos_spec`).
* The remaining slots of each axis form `q` chunks of `K` bits at the bottom
  (`layPos_chunk`). `laySwaps` is the scan of the paper over the target chunk positions, which
  realizes the transposition `layTr D q` (axis-major to chunk-major chunk order) with at most
  `D q - 1` chunk exchanges (`laySwaps_spec`).
* `layMoves`: the prefix moves, then the chunk exchanges; `layPerm es ℓ K` their composite;
  `layMoves_valid`, `layMoves_counts` (at most `D (b + 1)` prefix moves and `D q - 1`
  exchanges).

## Results

* `layRun_chunk`: chunk slot `(i, h)`, `b ≤ h < ℓ - 1`, ends at
  `ρ + K (⌊(h - b)/K⌋ D + (D - 1 - i))` with `ρ = (h - b) mod K`.
* `layRun_top`, `layRun_low`: the prefix slots end at `N - 1 - m`, `m` their index in `layPre`.
* `layPerm_sel_chunk`, `layPerm_sel_chunk_perm`: for `b ≤ h < ℓ - 1` every axis participates
  (`D' = |parts es h| = D`) and the selected bits of the round at `h` are, after the layout,
  `ρ_h + K (c₀_h + j)` for `j < D'`, with `ρ_h = layRho ℓ K h < K` and
  `c₀_h = layC0 es ℓ K h = ⌊(h - b)/K⌋ D`: a common offset in `D` consecutive chunks
  (`layC0_bound`).
* `layPerm_sel_top` (`h = ℓ - 1`, the long axes) and `layPerm_sel_low` (`h < b`) list the
  selected bits of the prefix rounds.
* `lay_relabel_Hl`, `lay_fwdRoundFlatL_eq`, `lay_oppRoundFlatL_eq`: a round of
  `SynthErr.fwdRoundsFlatL` in the layout `L` applies its butterflies on the physical bits
  `(selFin es h).map L`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr

/-! ### Bit position maps -/

/-- The single-bit move from position `a` to position `b`: the bit at `a` goes to `b` and the
bits strictly between shift by one toward `a`, keeping their relative order. -/
def layMvFun (a b x : ℕ) : ℕ :=
  if x = a then b else if a < x ∧ x ≤ b then x - 1 else if b ≤ x ∧ x < a then x + 1 else x

theorem layMvFun_inv (a b x : ℕ) : layMvFun b a (layMvFun a b x) = x := by
  unfold layMvFun; split_ifs <;> omega

theorem layMvFun_lt {a b x N : ℕ} (ha : a < N) (hb : b < N) (hx : x < N) :
    layMvFun a b x < N := by
  unfold layMvFun; split_ifs <;> omega

theorem layMvFun_self (a b : ℕ) : layMvFun a b a = b := by simp [layMvFun]

/-- The move keeps the relative order of every pair of positions other than `a`. -/
theorem layMvFun_lt_lt {a b x y : ℕ} (hxy : x < y) (hx : x ≠ a) (hy : y ≠ a) :
    layMvFun a b x < layMvFun a b y := by
  unfold layMvFun; split_ifs <;> omega

/-- Positions above both `a` and `b` are fixed. -/
theorem layMvFun_of_gt {a b x : ℕ} (ha : a < x) (hb : b < x) : layMvFun a b x = x := by
  unfold layMvFun; split_ifs <;> omega

/-- The exchange of the `K`-bit chunks at positions `u` and `w`. -/
def layXcFun (K u w x : ℕ) : ℕ :=
  if u ≤ x ∧ x < u + K then x - u + w else if w ≤ x ∧ x < w + K then x - w + u else x

theorem layXcFun_invol {K u w : ℕ} (hd : u + K ≤ w ∨ w + K ≤ u) (x : ℕ) :
    layXcFun K u w (layXcFun K u w x) = x := by
  unfold layXcFun; split_ifs <;> omega

theorem layXcFun_lt {K u w x N : ℕ} (hu : u + K ≤ N) (hw : w + K ≤ N) (hx : x < N) :
    layXcFun K u w x < N := by
  unfold layXcFun; split_ifs <;> omega

theorem layXcFun_comm (K u w x : ℕ) (hd : u + K ≤ w ∨ w + K ≤ u) :
    layXcFun K u w x = layXcFun K w u x := by
  unfold layXcFun; split_ifs <;> omega

/-! ### Moves -/

/-- A move of the layout: a single-bit move `bit a b` or the exchange `xc u w` of the chunks at
bit positions `u` and `w`. -/
inductive LayMove
  | bit (a b : ℕ)
  | xc (u w : ℕ)
  deriving DecidableEq

namespace LayMove

/-- The bit position map of a move with chunk width `K`. -/
def fn (K : ℕ) : LayMove → ℕ → ℕ
  | bit a b => layMvFun a b
  | xc u w => layXcFun K u w

/-- The inverse move. -/
def inv : LayMove → LayMove
  | bit a b => bit b a
  | xc u w => xc u w

/-- A move inside an address of `N` bits. -/
def Valid (K N : ℕ) : LayMove → Prop
  | bit a b => a < N ∧ b < N
  | xc u w => u + K ≤ N ∧ w + K ≤ N ∧ (u + K ≤ w ∨ w + K ≤ u)

instance (K N : ℕ) (m : LayMove) : Decidable (m.Valid K N) := by
  cases m <;> unfold Valid <;> infer_instance

theorem Valid.inv {K N : ℕ} {m : LayMove} (h : m.Valid K N) : m.inv.Valid K N := by
  cases m with
  | bit a b => exact ⟨h.2, h.1⟩
  | xc u w => exact h

theorem fn_lt {K N : ℕ} {m : LayMove} (h : m.Valid K N) {x : ℕ} (hx : x < N) : m.fn K x < N := by
  cases m with
  | bit a b => exact layMvFun_lt h.1 h.2 hx
  | xc u w => exact layXcFun_lt h.1 h.2.1 hx

theorem fn_inv {K N : ℕ} {m : LayMove} (h : m.Valid K N) (x : ℕ) : m.inv.fn K (m.fn K x) = x := by
  cases m with
  | bit a b => exact layMvFun_inv a b x
  | xc u w => exact layXcFun_invol h.2.2 x

theorem inv_inv (m : LayMove) : m.inv.inv = m := by cases m <;> rfl

/-- A move as a permutation of the bit positions `Fin N` (the identity for an invalid move). -/
def perm (K N : ℕ) (m : LayMove) : Equiv.Perm (Fin N) :=
  if h : m.Valid K N then
    { toFun := fun x => ⟨m.fn K x, fn_lt h x.isLt⟩
      invFun := fun x => ⟨m.inv.fn K x, fn_lt h.inv x.isLt⟩
      left_inv := fun x => Fin.ext (fn_inv h x)
      right_inv := fun x => Fin.ext (by
        have := fn_inv h.inv (x : ℕ)
        rwa [inv_inv] at this) }
  else 1

theorem perm_apply {K N : ℕ} {m : LayMove} (h : m.Valid K N) (x : Fin N) :
    (m.perm K N x : ℕ) = m.fn K x := by
  simp [perm, h]

theorem perm_inv {K N : ℕ} {m : LayMove} (h : m.Valid K N) : m.inv.perm K N = (m.perm K N).symm := by
  ext x
  rw [perm_apply h.inv]
  have e : (m.perm K N).symm x = ⟨m.inv.fn K x, fn_lt h.inv x.isLt⟩ := by
    simp [perm, h]
  rw [e]

end LayMove

/-- A list of moves, the head first, as a permutation of `Fin N`. -/
def layMovesPerm (K N : ℕ) : List LayMove → Equiv.Perm (Fin N)
  | [] => 1
  | m :: ms => (m.perm K N).trans (layMovesPerm K N ms)

/-- A list of moves, the head first, as a map of positions. -/
def layRun (K : ℕ) : List LayMove → ℕ → ℕ
  | [], x => x
  | m :: ms, x => layRun K ms (m.fn K x)

theorem layMovesPerm_append (K N : ℕ) (ms ms' : List LayMove) :
    layMovesPerm K N (ms ++ ms') = (layMovesPerm K N ms).trans (layMovesPerm K N ms') := by
  induction ms with
  | nil => ext x; rfl
  | cons m ms ih => rw [List.cons_append, layMovesPerm, layMovesPerm, ih]; rfl

theorem layRun_append (K : ℕ) (ms ms' : List LayMove) (x : ℕ) :
    layRun K (ms ++ ms') x = layRun K ms' (layRun K ms x) := by
  induction ms generalizing x with
  | nil => rfl
  | cons m ms ih => exact ih _

theorem layMovesPerm_apply {K N : ℕ} :
    ∀ {ms : List LayMove}, (∀ m ∈ ms, m.Valid K N) → ∀ x : Fin N,
      (layMovesPerm K N ms x : ℕ) = layRun K ms x
  | [], _, _ => rfl
  | m :: ms, h, x => by
      show (layMovesPerm K N ms (m.perm K N x) : ℕ) = layRun K ms (m.fn K x)
      rw [layMovesPerm_apply (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')),
        LayMove.perm_apply (h m List.mem_cons_self)]

/-- The inverse move list: the inverse moves in reverse order. -/
def layMovesInv (ms : List LayMove) : List LayMove := (ms.map LayMove.inv).reverse

theorem layMovesPerm_inv {K N : ℕ} :
    ∀ {ms : List LayMove}, (∀ m ∈ ms, m.Valid K N) →
      layMovesPerm K N (layMovesInv ms) = (layMovesPerm K N ms).symm
  | [], _ => by ext x; rfl
  | m :: ms, h => by
      rw [layMovesInv, List.map_cons, List.reverse_cons, layMovesPerm_append, ← layMovesInv,
        layMovesPerm_inv (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')), layMovesPerm,
        layMovesPerm, LayMove.perm_inv (h m List.mem_cons_self)]
      ext x
      rfl

theorem layMovesInv_valid {K N : ℕ} {ms : List LayMove} (h : ∀ m ∈ ms, m.Valid K N) :
    ∀ m ∈ layMovesInv ms, m.Valid K N := by
  intro m hm
  simp only [layMovesInv, List.mem_reverse, List.mem_map] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  exact (h m' hm').inv

/-! ### Record addresses under a bit permutation -/

section Rec

variable {n : ℕ}

theorem lay_decide_toBits (x : ℕ) (q : Fin n) : decide (toBits n x q = 1) = x.testBit q := by
  unfold toBits
  cases x.testBit q <;> decide

/-- The address whose bit `P j` is bit `j` of `x`: the record at address `x` moves to
`layRecVal P x` when the address bits are permuted by `P`. -/
def layRecVal (P : Equiv.Perm (Fin n)) (x : ℕ) : ℕ := ofBits fun j : Fin n => toBits n x (P.symm j)

theorem layRecVal_lt (P : Equiv.Perm (Fin n)) (x : ℕ) : layRecVal P x < 2 ^ n := ofBits_lt _

theorem testBit_layRecVal (P : Equiv.Perm (Fin n)) (x j : ℕ) :
    (layRecVal P x).testBit j = if h : j < n then x.testBit (P.symm ⟨j, h⟩) else false := by
  rw [layRecVal, testBit_ofBits]
  split_ifs with h
  · exact lay_decide_toBits x _
  · rfl

theorem testBit_layRecVal_apply (P : Equiv.Perm (Fin n)) (x : ℕ) (j : Fin n) :
    (layRecVal P x).testBit (P j) = x.testBit j := by
  simp only [testBit_layRecVal, (P j).isLt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]

theorem layRecVal_symm (P : Equiv.Perm (Fin n)) {x : ℕ} (hx : x < 2 ^ n) :
    layRecVal P.symm (layRecVal P x) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_layRecVal]
  split_ifs with h
  · simp only [Equiv.symm_symm]
    exact testBit_layRecVal_apply P x ⟨j, h⟩
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

theorem layRecVal_trans (P Q : Equiv.Perm (Fin n)) (x : ℕ) :
    layRecVal (P.trans Q) x = layRecVal Q (layRecVal P x) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_layRecVal, testBit_layRecVal]
  split_ifs with h
  · simp only [testBit_layRecVal, (Q.symm ⟨j, h⟩).isLt, ↓reduceDIte, Fin.eta]
    rfl
  · rfl

/-- The permutation of the `2^n` record addresses induced by the bit permutation `P`. -/
def layRec (P : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 ^ n)) where
  toFun x := ⟨layRecVal P x, layRecVal_lt P x⟩
  invFun x := ⟨layRecVal P.symm x, layRecVal_lt P.symm x⟩
  left_inv x := Fin.ext (layRecVal_symm P x.isLt)
  right_inv x := Fin.ext (by simpa using layRecVal_symm P.symm x.isLt)

@[simp] theorem layRec_val (P : Equiv.Perm (Fin n)) (x : Fin (2 ^ n)) :
    (layRec P x : ℕ) = layRecVal P x := rfl

theorem layRec_trans (P Q : Equiv.Perm (Fin n)) :
    layRec (P.trans Q) = (layRec P).trans (layRec Q) := by
  ext x
  simp [layRecVal_trans]

theorem layRec_symm (P : Equiv.Perm (Fin n)) : layRec P.symm = (layRec P).symm := by
  ext x
  rfl

theorem layRec_one : layRec (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x
  show layRecVal 1 x = x
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_layRecVal]
  split_ifs with h
  · rfl
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

/-- The most significant differing bit of `x < y`. -/
theorem lay_exists_msb {x y : ℕ} (hxy : x < y) :
    ∃ i, x.testBit i = false ∧ y.testBit i = true ∧ ∀ j, i < j → x.testBit j = y.testBit j := by
  have hne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.2 (Nat.ne_of_lt hxy)
  obtain ⟨i, hi, hj⟩ := Nat.exists_most_significant_bit hne
  rw [Nat.testBit_xor] at hi
  have hj' : ∀ j, i < j → x.testBit j = y.testBit j := fun j h => by
    have := hj j h
    rw [Nat.testBit_xor] at this
    revert this
    cases x.testBit j <;> cases y.testBit j <;> simp
  refine ⟨i, ?_, ?_, hj'⟩ <;>
  · cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
    exact absurd hxy (Nat.not_lt.2 (Nat.le_of_lt (Nat.lt_of_testBit i hy hx
      (fun j h => (hj' j h).symm))))

/-- A bit permutation keeping the relative order of the positions other than `a` keeps the order
of the records with a common bit `a`. -/
theorem layRecVal_lt_of {P : Equiv.Perm (Fin n)} {a : Fin n}
    (hP : ∀ x y : Fin n, x < y → x ≠ a → y ≠ a → P x < P y) {x y : ℕ} (hxy : x < y)
    (hy : y < 2 ^ n) (hab : x.testBit a = y.testBit a) : layRecVal P x < layRecVal P y := by
  obtain ⟨i, hxi, hyi, hj⟩ := lay_exists_msb hxy
  have hin : i < n := by
    by_contra hc
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num)
      (by omega)))] at hyi
    exact Bool.false_ne_true hyi
  set ii : Fin n := ⟨i, hin⟩
  have hia : ii ≠ a := by
    intro e
    have h1 : x.testBit a = false := by rw [← e]; exact hxi
    have h2 : y.testBit a = true := by rw [← e]; exact hyi
    rw [h1, h2] at hab
    exact Bool.false_ne_true hab
  refine Nat.lt_of_testBit (P ii) ?_ ?_ ?_
  · rw [testBit_layRecVal_apply]; exact hxi
  · rw [testBit_layRecVal_apply]; exact hyi
  · intro j hj'
    rw [testBit_layRecVal, testBit_layRecVal]
    split_ifs with h
    · set j' := P.symm ⟨j, h⟩ with hj''
      by_cases hja : j' = a
      · rw [hja]; exact hab
      · apply hj
        have hPj : P j' = ⟨j, h⟩ := by simp [hj'']
        by_contra hle
        rcases Nat.lt_or_eq_of_le (Nat.not_lt.1 hle) with hlt | heq
        · have := hP j' ii (Fin.lt_def.2 hlt) hja hia
          rw [hPj, Fin.lt_def] at this
          simp only at this
          omega
        · have : j' = ii := Fin.ext heq
          rw [this] at hPj
          have : (P ii : ℕ) = j := by rw [hPj]
          omega
    · rfl

end Rec

/-! ### Moving a list of positions to the top -/

section Prefix

variable (N : ℕ) (pre : List ℕ)

/-- The positions after the first `k` prefix moves: move `k` takes the slot `pre[k]` from its
current position to `N - 1 - k`, just below the prefix already formed. -/
def layPos : ℕ → ℕ → ℕ
  | 0 => id
  | k + 1 => layMvFun (layPos k (pre.getD k 0)) (N - 1 - k) ∘ layPos k

/-- The first `k` prefix moves. -/
def layPreMovesK (k : ℕ) : List LayMove :=
  (List.range k).map fun j => .bit (layPos N pre j (pre.getD j 0)) (N - 1 - j)

/-- The prefix moves of the slot list `pre`. -/
def layPreMoves : List LayMove := layPreMovesK N pre pre.length

theorem layRun_preMovesK (K : ℕ) : ∀ (k x : ℕ), layRun K (layPreMovesK N pre k) x = layPos N pre k x
  | 0, x => rfl
  | k + 1, x => by
      rw [layPreMovesK, List.range_succ, List.map_append, layRun_append, ← layPreMovesK,
        layRun_preMovesK K k x]
      rfl

variable {N pre}

/-- The invariant of the prefix moves after `k` moves: the positions form a permutation of
`[0, N)`, the moved slot `pre[m]` sits at `N - 1 - m`, and the slots not yet moved keep their
relative order. -/
theorem layPos_spec (hnd : pre.Nodup) (hlt : ∀ s ∈ pre, s < N) (hP : pre.length ≤ N) :
    ∀ k ≤ pre.length,
      (∀ x < N, layPos N pre k x < N) ∧
      (∀ x < N, ∀ y < N, layPos N pre k x = layPos N pre k y → x = y) ∧
      (∀ m < k, layPos N pre k (pre.getD m 0) = N - 1 - m) ∧
      (∀ x < N, ∀ y < N, x < y → x ∉ pre.take k → y ∉ pre.take k →
        layPos N pre k x < layPos N pre k y)
  | 0, _ => ⟨fun x hx => hx, fun x _ y _ h => h, fun m hm => absurd hm (Nat.not_lt_zero _),
      fun x _ y _ hxy _ _ => hxy⟩
  | k + 1, hk => by
      obtain ⟨h1, h2, h3, h4⟩ := layPos_spec hnd hlt hP k (by omega)
      have hkl : k < pre.length := by omega
      have hs : pre.getD k 0 = pre[k] := List.getD_eq_getElem _ _ hkl
      have hsN : pre.getD k 0 < N := by rw [hs]; exact hlt _ (List.getElem_mem hkl)
      set a := layPos N pre k (pre.getD k 0) with ha_def
      have haN : a < N := h1 _ hsN
      have ha : a ≤ N - 1 - k := by
        by_contra hc
        have hm : N - 1 - a < k := by omega
        have e := h3 (N - 1 - a) hm
        rw [show N - 1 - (N - 1 - a) = a by omega] at e
        have hmN : pre.getD (N - 1 - a) 0 < N := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact hlt _ (List.getElem_mem _)
        have := h2 _ hmN _ hsN (e.trans ha_def)
        rw [hs, List.getD_eq_getElem _ _ (by omega)] at this
        have := (hnd.getElem_inj_iff).1 this
        omega
      have hbN : N - 1 - k < N := by omega
      have hstep : ∀ x, layPos N pre (k + 1) x = layMvFun a (N - 1 - k) (layPos N pre k x) :=
        fun x => rfl
      refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun m hm => ?_, fun x hx y hy hxy hx' hy' => ?_⟩
      · rw [hstep]; exact layMvFun_lt haN hbN (h1 x hx)
      · rw [hstep, hstep] at hxy
        have := congrArg (layMvFun (N - 1 - k) a) hxy
        rw [layMvFun_inv, layMvFun_inv] at this
        exact h2 x hx y hy this
      · rw [hstep]
        rcases Nat.lt_or_ge m k with hmk | hmk
        · rw [h3 m hmk]; exact layMvFun_of_gt (by omega) (by omega)
        · rw [show m = k by omega]; exact layMvFun_self _ _
      · have hsub := List.take_subset_take_left pre (Nat.le_succ k)
        have hmem : pre.getD k 0 ∈ pre.take (k + 1) := by
          rw [hs, List.mem_take_iff_getElem]; exact ⟨k, by omega, rfl⟩
        have hxs : x ≠ pre.getD k 0 := fun e => hx' (e ▸ hmem)
        have hys : y ≠ pre.getD k 0 := fun e => hy' (e ▸ hmem)
        rw [hstep, hstep]
        exact layMvFun_lt_lt (h4 x hx y hy hxy (fun h => hx' (hsub h)) (fun h => hy' (hsub h)))
          (fun e => hxs (h2 x hx _ hsN e)) (fun e => hys (h2 y hy _ hsN e))

/-- The prefix moves are valid moves of an address of `N` bits. -/
theorem layPreMoves_valid (K : ℕ) (hnd : pre.Nodup) (hlt : ∀ s ∈ pre, s < N)
    (hP : pre.length ≤ N) : ∀ m ∈ layPreMoves N pre, m.Valid K N := by
  intro m hm
  simp only [layPreMoves, layPreMovesK, List.mem_map, List.mem_range] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  have hjN : pre.getD j 0 < N := by
    rw [List.getD_eq_getElem _ _ hj]; exact hlt _ (List.getElem_mem _)
  exact ⟨(layPos_spec hnd hlt hP j hj.le).1 _ hjN, by omega⟩

/-- After all prefix moves the slots outside `pre` occupy the positions below `N - |pre|`. -/
theorem layPos_nonpre (hnd : pre.Nodup) (hlt : ∀ s ∈ pre, s < N) (hP : pre.length ≤ N)
    {x : ℕ} (hx : x < N) (hxp : x ∉ pre) : layPos N pre pre.length x < N - pre.length := by
  obtain ⟨h1, h2, h3, _⟩ := layPos_spec hnd hlt hP pre.length le_rfl
  by_contra hc
  have hm : N - 1 - layPos N pre pre.length x < pre.length := by have := h1 x hx; omega
  have e := h3 _ hm
  rw [show N - 1 - (N - 1 - layPos N pre pre.length x) = layPos N pre pre.length x by
    have := h1 x hx; omega] at e
  have hmN : pre.getD (N - 1 - layPos N pre pre.length x) 0 < N := by
    rw [List.getD_eq_getElem _ _ hm]; exact hlt _ (List.getElem_mem _)
  have := h2 _ hmN _ hx e
  rw [List.getD_eq_getElem _ _ hm] at this
  exact hxp (this ▸ List.getElem_mem _)

end Prefix

/-- A strictly increasing map of `[0, n)` into itself is the identity. -/
theorem lay_strictMono_id {n : ℕ} (f : ℕ → ℕ) (hf : ∀ y < n, f y < n)
    (hm : ∀ y y', y < y' → y' < n → f y < f y') : ∀ y < n, f y = y := by
  have hge : ∀ y < n, y ≤ f y := by
    intro y
    induction y with
    | zero => intro _; exact Nat.zero_le _
    | succ y ih => intro hy; have := hm y (y + 1) (by omega) hy; have := ih (by omega); omega
  have hle : ∀ d y, y + d + 1 = n → f y ≤ y := by
    intro d
    induction d with
    | zero => intro y hy; have := hf y (by omega); omega
    | succ d ih =>
        intro y hy
        have := ih (y + 1) (by omega)
        have := hm y (y + 1) (by omega) (by omega)
        omega
  intro y hy
  exact le_antisymm (hle (n - 1 - y) y (by omega)) (hge y hy)

/-! ### Chunk permutations and their exchanges -/

section Chunks

variable (K : ℕ) {m : ℕ}

/-- The bit map induced by the permutation `σ` of the `m` chunks of `K` bits at the bottom of
the address: bit `ρ` of chunk `c` goes to bit `ρ` of chunk `σ c`. -/
def layChunkFun (σ : Equiv.Perm (Fin m)) (x : ℕ) : ℕ :=
  if h : x < K * m then (σ ⟨x / K, Nat.div_lt_of_lt_mul h⟩ : ℕ) * K + x % K else x

theorem lay_chunk_lt {c m ρ : ℕ} (hc : c < m) (hρ : ρ < K) : c * K + ρ < K * m := by
  have : (c + 1) * K ≤ m * K := Nat.mul_le_mul_right K hc
  rw [Nat.mul_comm K m]; rw [Nat.add_mul] at this; omega

theorem layChunkFun_lt (σ : Equiv.Perm (Fin m)) {x : ℕ} (h : x < K * m) :
    layChunkFun K σ x < K * m := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.zero_mul] at h; omega
    · exact h0
  simp only [layChunkFun, h, ↓reduceDIte]
  exact lay_chunk_lt K (σ _).isLt (Nat.mod_lt _ hK)

theorem layChunkFun_of_ge (σ : Equiv.Perm (Fin m)) {x : ℕ} (h : K * m ≤ x) :
    layChunkFun K σ x = x := by
  simp only [layChunkFun, show ¬ x < K * m by omega, ↓reduceDIte]

theorem layChunkFun_chunk (σ : Equiv.Perm (Fin m)) {c ρ : ℕ} (hc : c < m) (hρ : ρ < K) :
    layChunkFun K σ (c * K + ρ) = (σ ⟨c, hc⟩ : ℕ) * K + ρ := by
  have hK : 0 < K := by omega
  have h := lay_chunk_lt K hc hρ
  have e1 : (c * K + ρ) / K = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hρ, Nat.zero_add]
  have e2 : (c * K + ρ) % K = ρ := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hρ]
  simp only [layChunkFun, h, ↓reduceDIte, e1, e2]

/-- Every position below `K m` is `c K + ρ` with `c < m`, `ρ < K`. -/
theorem lay_chunk_decomp {x : ℕ} (h : x < K * m) : ∃ c ρ, c < m ∧ ρ < K ∧ x = c * K + ρ := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.zero_mul] at h; omega
    · exact h0
  exact ⟨x / K, x % K, Nat.div_lt_of_lt_mul h, Nat.mod_lt _ hK, (Nat.div_add_mod' x K).symm⟩

theorem layChunkFun_trans (σ τ : Equiv.Perm (Fin m)) (x : ℕ) :
    layChunkFun K (σ.trans τ) x = layChunkFun K τ (layChunkFun K σ x) := by
  by_cases h : x < K * m
  · obtain ⟨c, ρ, hc, hρ, rfl⟩ := lay_chunk_decomp K h
    rw [layChunkFun_chunk K _ hc hρ, layChunkFun_chunk K _ hc hρ,
      layChunkFun_chunk K _ (σ _).isLt hρ]
    rfl
  · rw [layChunkFun_of_ge K σ (x := x) (by omega), layChunkFun_of_ge K τ (x := x) (by omega),
      layChunkFun_of_ge K (σ.trans τ) (x := x) (by omega)]

theorem layChunkFun_one (x : ℕ) : layChunkFun K (1 : Equiv.Perm (Fin m)) x = x := by
  by_cases h : x < K * m
  · obtain ⟨c, ρ, hc, hρ, rfl⟩ := lay_chunk_decomp K h
    rw [layChunkFun_chunk K _ hc hρ]
    rfl
  · exact layChunkFun_of_ge K _ (by omega)

/-- The exchange of chunks `p ≠ k` is `layXcFun` at the bit positions `p K` and `k K`. -/
theorem layChunkFun_swap {p k : ℕ} (hp : p < m) (hk : k < m) (hpk : p ≠ k) (x : ℕ) :
    layChunkFun K (Equiv.swap (⟨p, hp⟩ : Fin m) ⟨k, hk⟩) x = layXcFun K (p * K) (k * K) x := by
  by_cases h : x < K * m
  · obtain ⟨c, ρ, hc, hρ, rfl⟩ := lay_chunk_decomp K h
    rw [layChunkFun_chunk K _ hc hρ]
    have hsw : ((Equiv.swap (⟨p, hp⟩ : Fin m) ⟨k, hk⟩ ⟨c, hc⟩ : Fin m) : ℕ) =
        if c = p then k else if c = k then p else c := by
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2 h3 h4 <;> simp_all [Fin.ext_iff]
    rw [hsw]
    have key : ∀ c' : ℕ, (c' * K ≤ c * K + ρ ∧ c * K + ρ < c' * K + K) ↔ c' = c := by
      intro c'
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_trichotomy c' c with hlt | heq | hgt
        · have : (c' + 1) * K ≤ c * K := Nat.mul_le_mul_right K hlt
          rw [Nat.add_mul] at this; omega
        · exact heq
        · have : (c + 1) * K ≤ c' * K := Nat.mul_le_mul_right K hgt
          rw [Nat.add_mul] at this; omega
      · rintro rfl; omega
    unfold layXcFun
    by_cases hcp : c = p
    · subst hcp
      have h1 := (key c).2 rfl
      simp only [h1, and_self, ↓reduceIte]
      omega
    · have h1 : ¬ (p * K ≤ c * K + ρ ∧ c * K + ρ < p * K + K) := fun h' => hcp ((key p).1 h').symm
      simp only [h1, hcp, ↓reduceIte]
      by_cases hck : c = k
      · subst hck
        have h2 := (key c).2 rfl
        simp only [h2, and_self, ↓reduceIte]
        omega
      · have h2 : ¬ (k * K ≤ c * K + ρ ∧ c * K + ρ < k * K + K) :=
          fun h' => hck ((key k).1 h').symm
        simp only [h2, hck, ↓reduceIte]
  · rw [layChunkFun_of_ge K _ (by omega)]
    unfold layXcFun
    have h1 : (p + 1) * K ≤ m * K := Nat.mul_le_mul_right K hp
    have h2 : (k + 1) * K ≤ m * K := Nat.mul_le_mul_right K hk
    rw [Nat.add_mul] at h1 h2
    rw [Nat.mul_comm K m] at h
    split_ifs <;> omega

/-- The scan of the paper over the chunk positions `k - 1, …, 0` (left to right): when the chunk
required at position `j` sits at another position `p = σ⁻¹ j`, exchange positions `p` and `j`,
then continue with the remaining permutation. -/
def laySwaps : ℕ → Equiv.Perm (Fin m) → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, σ =>
      if hk : k < m then
        if (σ.symm ⟨k, hk⟩ : ℕ) = k then laySwaps k σ
        else ((σ.symm ⟨k, hk⟩ : ℕ), k) ::
          laySwaps k (σ * Equiv.swap (σ.symm ⟨k, hk⟩) ⟨k, hk⟩)
      else laySwaps k σ

/-- The exchange moves of a list of chunk pairs. -/
def layXcMoves (xs : List (ℕ × ℕ)) : List LayMove := xs.map fun e => .xc (e.1 * K) (e.2 * K)

/-- The scan realizes `σ` with at most `k - 1` exchanges of chunk pairs `p < j < k`. -/
theorem laySwaps_spec : ∀ (k : ℕ) (σ : Equiv.Perm (Fin m)), k ≤ m →
    (∀ c : Fin m, k ≤ (c : ℕ) → σ c = c) →
    (∀ x, layRun K (layXcMoves K (laySwaps k σ)) x = layChunkFun K σ x) ∧
      (laySwaps k σ).length ≤ k - 1 ∧ ∀ e ∈ laySwaps k σ, e.1 < e.2 ∧ e.2 < k
  | 0, σ, _, hfix => by
      have : σ = 1 := by ext c; simp [hfix c (Nat.zero_le _)]
      subst this
      exact ⟨fun x => (layChunkFun_one K x).symm, by simp [laySwaps], by simp [laySwaps]⟩
  | k + 1, σ, hk, hfix => by
      have hkm : k < m := by omega
      set p := σ.symm ⟨k, hkm⟩ with hp
      have hpk : (p : ℕ) ≤ k := by
        by_contra hc
        have h1 : σ p = p := hfix p (by omega)
        have h2 : σ p = ⟨k, hkm⟩ := by rw [hp, Equiv.apply_symm_apply]
        rw [h1] at h2
        rw [h2] at hc
        simp at hc
      by_cases hpe : (p : ℕ) = k
      · have hfix' : ∀ c : Fin m, k ≤ (c : ℕ) → σ c = c := by
          intro c hc
          rcases Nat.lt_or_eq_of_le hc with hlt | heq
          · exact hfix c (by omega)
          · have hc' : c = p := Fin.ext (by rw [hpe]; exact heq.symm)
            rw [hc', hp, Equiv.apply_symm_apply]
            apply Fin.ext
            rw [← hp]
            exact hpe.symm
        obtain ⟨h1, h2, h3⟩ := laySwaps_spec k σ (by omega) hfix'
        simp only [laySwaps, hkm, ↓reduceDIte, ← hp, hpe, ↓reduceIte]
        exact ⟨h1, by omega, fun e he => ⟨(h3 e he).1, by have := (h3 e he).2; omega⟩⟩
      · set σ' := σ * Equiv.swap p ⟨k, hkm⟩ with hσ'
        have hfix' : ∀ c : Fin m, k ≤ (c : ℕ) → σ' c = c := by
          intro c hc
          have hpk' : (p : ℕ) < k := by omega
          rcases Nat.lt_or_eq_of_le hc with hlt | heq
          · have hcp : c ≠ p := fun e => by rw [e] at hlt; omega
            have hck : c ≠ ⟨k, hkm⟩ := fun e => by rw [e] at hlt; simp at hlt
            rw [hσ', Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hcp hck]
            exact hfix c (by omega)
          · have hc' : c = ⟨k, hkm⟩ := Fin.ext heq.symm
            rw [hc', hσ', Equiv.Perm.mul_apply, Equiv.swap_apply_right, hp, Equiv.apply_symm_apply]
        obtain ⟨h1, h2, h3⟩ := laySwaps_spec k σ' (by omega) hfix'
        simp only [laySwaps, hkm, ↓reduceDIte, ← hp, hpe, ↓reduceIte]
        refine ⟨fun x => ?_, ?_, ?_⟩
        · show layRun K (layXcMoves K (laySwaps k σ')) (layXcFun K (p * K) (k * K) x) = _
          rw [h1, ← layChunkFun_swap K p.isLt hkm hpe, ← layChunkFun_trans]
          congr 1
          ext c
          simp [hσ']
        · have h2' : (laySwaps k (σ * Equiv.swap p ⟨k, hkm⟩)).length ≤ k - 1 := h2
          simp only [List.length_cons]; omega
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · show (p : ℕ) < k ∧ k < k + 1
            exact ⟨by omega, by omega⟩
          · exact ⟨(h3 e he).1, by have := (h3 e he).2; omega⟩

/-- The transposition of a `D × q` array of chunks: chunk `i q + t` goes to `t D + i`. -/
def layTr (D q : ℕ) : Equiv.Perm (Fin (D * q)) where
  toFun c := ⟨(c % q) * D + c / q, by
    have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; have := c.isLt; simp at this)
    have h1 : (c : ℕ) / q < D := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq c.isLt (Nat.mul_comm D q))
    have h2 := Nat.mod_lt (c : ℕ) hq
    calc (c : ℕ) % q * D + c / q < (c % q) * D + D := by omega
      _ = (c % q + 1) * D := by ring
      _ ≤ q * D := Nat.mul_le_mul_right D h2
      _ = D * q := Nat.mul_comm _ _⟩
  invFun c := ⟨(c % D) * q + c / D, by
    have hD : 0 < D := Nat.pos_of_ne_zero (by rintro rfl; have := c.isLt; simp at this)
    have h1 : (c : ℕ) / D < q := Nat.div_lt_of_lt_mul c.isLt
    have h2 := Nat.mod_lt (c : ℕ) hD
    calc (c : ℕ) % D * q + c / D < (c % D) * q + q := by omega
      _ = (c % D + 1) * q := by ring
      _ ≤ D * q := Nat.mul_le_mul_right q h2⟩
  left_inv c := by
    have h1 : (c : ℕ) / q < D := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq c.isLt (Nat.mul_comm D q))
    have hD : 0 < D := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    apply Fin.ext
    show ((c : ℕ) % q * D + c / q) % D * q + ((c : ℕ) % q * D + c / q) / D = c
    have e1 : ((c : ℕ) % q * D + c / q) % D = c / q := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    have e2 : ((c : ℕ) % q * D + c / q) / D = c % q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt h1, Nat.zero_add]
    rw [e1, e2]
    exact Nat.div_add_mod' (c : ℕ) q
  right_inv c := by
    have h1 : (c : ℕ) / D < q := Nat.div_lt_of_lt_mul c.isLt
    have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    apply Fin.ext
    show ((c : ℕ) % D * q + c / D) % q * D + ((c : ℕ) % D * q + c / D) / q = c
    have e1 : ((c : ℕ) % D * q + c / D) % q = c / D := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    have e2 : ((c : ℕ) % D * q + c / D) / q = c % D := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt h1, Nat.zero_add]
    rw [e1, e2]
    exact Nat.div_add_mod' (c : ℕ) D

theorem layTr_apply (D q : ℕ) {i t : ℕ} (hi : i < D) (ht : t < q) :
    (layTr D q ⟨i * q + t, by
      calc i * q + t < i * q + q := by omega
        _ = (i + 1) * q := by ring
        _ ≤ D * q := Nat.mul_le_mul_right q hi⟩ : ℕ) = t * D + i := by
  show (i * q + t) % q * D + (i * q + t) / q = t * D + i
  have hq : 0 < q := by omega
  rw [Nat.add_comm (i * q), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht,
    Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, Nat.zero_add]

end Chunks

/-! ### The layout of the synthetic transforms -/

section Layout

variable (es : List ℕ) (ℓ K : ℕ)

/-- `b = (ℓ - 1) mod K`: the named positions `h < b` go to the prefix. -/
def layB : ℕ := (ℓ - 1) % K

/-- `q = ⌊(ℓ - 1)/K⌋`: the number of full chunks per axis. -/
def layQ : ℕ := (ℓ - 1) / K

/-- The long axes (`aᵢ = ℓ`), increasing. -/
def layLongs : List ℕ := (List.range es.length).filter fun i => ax es i = ℓ

/-- The number of long axes before axis `i`. -/
def layLrank (i : ℕ) : ℕ := ((List.range i).filter fun j => ax es j = ℓ).length

/-- The slots listed for the prefix, in the order of the paper: the top slot `(i, ℓ - 1)` of
each long axis, increasing in `i`; then `(i, h)` for `h = b - 1, …, 0`, increasing in `i` within
each `h`. Slot `(i, h)` is the address bit `off es i + h`. -/
def layPre : List ℕ :=
  (layLongs es ℓ).map (fun i => off es i + (ℓ - 1)) ++
    (List.range (layB ℓ K * es.length)).map fun m =>
      off es (m % es.length) + (layB ℓ K - 1 - m / es.length)

/-- The moves of the layout: the prefix moves, then the chunk exchanges of the scan that turns
the axis-major chunk order into the chunk-major order. -/
def layMoves : List LayMove :=
  layPreMoves es.sum (layPre es ℓ K) ++
    layXcMoves K (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K)))

/-- **The layout `L`** of the synthetic transforms: logical address bit `j` (bit `h` of axis `i`
is `j = off es i + h`) is stored at physical bit `layPerm es ℓ K j`. It is the composition of
the moves `layMoves`. -/
def layPerm : Equiv.Perm (Fin es.sum) := layMovesPerm K es.sum (layMoves es ℓ K)

/-- The parameter conditions: every axis has `ℓ - 1` or `ℓ` bits and `1 ≤ K ≤ ℓ - 1`. -/
structure LayHyp : Prop where
  widths : ∀ e ∈ es, e = ℓ - 1 ∨ e = ℓ
  K_pos : 1 ≤ K
  K_le : K ≤ ℓ - 1

variable {es ℓ K}

namespace LayHyp

variable (H : LayHyp es ℓ K)
include H

theorem ax_of_lt {i : ℕ} (hi : i < es.length) :
    IntegerMultBounds.MathlibTM2.Mult.Rounds.ax es i = ℓ - 1 ∨ IntegerMultBounds.MathlibTM2.Mult.Rounds.ax es i = ℓ :=
  H.widths _ (ax_mem es hi)

theorem ℓ_ge : 2 ≤ ℓ := by have := H.K_pos; have := H.K_le; omega

theorem ax_ge {i : ℕ} (hi : i < es.length) : ℓ - 1 ≤ IntegerMultBounds.MathlibTM2.Mult.Rounds.ax es i := by
  rcases H.ax_of_lt hi with h | h <;> omega

theorem b_lt : layB ℓ K < K := Nat.mod_lt _ (by have := H.K_pos; omega)

theorem q_pos : 1 ≤ layQ ℓ K := by
  unfold layQ
  exact (Nat.one_le_div_iff (by have := H.K_pos; omega)).2 H.K_le

end LayHyp

theorem lay_bqK : layB ℓ K + layQ ℓ K * K = ℓ - 1 := by
  unfold layB layQ
  have := Nat.mod_add_div (ℓ - 1) K
  rw [Nat.mul_comm] at this
  omega

/-- Two slot names `(i, h)`, `(i', h')` with `h < aᵢ`, `h' < aᵢ'` with the same address bit are
equal. -/
theorem lay_off_inj {i i' h h' : ℕ} (hh : h < ax es i) (hh' : h' < ax es i')
    (e : off es i + h = off es i' + h') : i = i' ∧ h = h' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have := off_le_of_lt es hlt; omega
  · subst heq; omega
  · have := off_le_of_lt es hgt; omega

theorem lay_sum_range (c : ℕ) (f : ℕ → ℕ) :
    ∀ D, (∀ i < D, f i = c ∨ f i = c + 1) →
      ((List.range D).map f).sum = D * c + ((List.range D).filter fun i => f i = c + 1).length
  | 0, _ => by simp
  | D + 1, hf => by
      rw [List.range_succ, List.map_append, List.sum_append, List.filter_append,
        List.length_append, lay_sum_range c f D (fun i hi => hf i (by omega))]
      rcases hf D (by omega) with h | h
      · simp [h]; ring
      · simp [h]; ring

theorem layPre_length :
    (layPre es ℓ K).length = (layLongs es ℓ).length + layB ℓ K * es.length := by
  simp [layPre]

theorem mem_layLongs {i : ℕ} : i ∈ layLongs es ℓ ↔ i < es.length ∧ ax es i = ℓ := by
  simp [layLongs]

variable (H : LayHyp es ℓ K)
include H

/-- `N = D (ℓ - 1) + #long`. -/
theorem lay_sum : es.sum = es.length * (ℓ - 1) + (layLongs es ℓ).length := by
  have h1 := sum_range_getD es
  rw [← list_sum_range] at h1
  rw [← h1, layLongs]
  have h2 := lay_sum_range (ℓ - 1) (ax es) es.length (fun i hi => by
    rcases H.ax_of_lt hi with h | h
    · exact Or.inl h
    · exact Or.inr (by have := H.ℓ_ge; omega))
  rw [h2]
  congr 3
  funext i
  have := H.ℓ_ge
  simp only [show ℓ - 1 + 1 = ℓ by omega]

theorem layPre_lt : ∀ s ∈ layPre es ℓ K, s < es.sum := by
  intro s hs
  simp only [layPre, List.mem_append, List.mem_map, List.mem_range] at hs
  rcases hs with ⟨i, hi, rfl⟩ | ⟨m, hm, rfl⟩
  · rw [mem_layLongs] at hi
    have := off_add_ax_le es i
    have := H.ℓ_ge
    omega
  · have hD : 0 < es.length := by
      rcases Nat.eq_zero_or_pos es.length with h0 | h0
      · rw [h0, Nat.mul_zero] at hm; omega
      · exact h0
    have hi : m % es.length < es.length := Nat.mod_lt _ hD
    have := off_add_ax_le es (m % es.length)
    have := H.ax_ge hi
    have := H.b_lt
    have := H.K_le
    generalize m / es.length = j
    omega

theorem layPre_nodup : (layPre es ℓ K).Nodup := by
  have hb := H.b_lt
  have hKl := H.K_le
  rw [layPre, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
    intro i hi i' hi' e
    rw [mem_layLongs] at hi hi'
    exact (lay_off_inj (by omega) (by omega) e).1
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro m hm m' hm' e
    rw [List.mem_range] at hm hm'
    have hD : 0 < es.length := by
      rcases Nat.eq_zero_or_pos es.length with h0 | h0
      · rw [h0, Nat.mul_zero] at hm; omega
      · exact h0
    have h1 := H.ax_ge (Nat.mod_lt m hD)
    have h2 := H.ax_ge (Nat.mod_lt m' hD)
    have d1 : m / es.length < layB ℓ K := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have d2 : m' / es.length < layB ℓ K := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hq : m / es.length = m' / es.length ∧ m % es.length = m' % es.length := by
      revert e h1 h2 d1 d2
      generalize m / es.length = j
      generalize m' / es.length = j'
      intro e h1 h2 d1 d2
      obtain ⟨e1, e2⟩ := lay_off_inj (by omega) (by omega) e
      exact ⟨by omega, e1⟩
    rw [← Nat.div_add_mod m es.length, ← Nat.div_add_mod m' es.length, hq.1, hq.2]
  · intro x hx y hy hxy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨m, hm, rfl⟩ := hy
    rw [mem_layLongs] at hi
    have hD : 0 < es.length := by
      rcases Nat.eq_zero_or_pos es.length with h0 | h0
      · rw [h0, Nat.mul_zero] at hm; omega
      · exact h0
    have h1 := H.ax_ge (Nat.mod_lt m hD)
    revert hxy h1
    generalize m / es.length = j
    intro hxy h1
    have := (lay_off_inj (by omega) (by omega) hxy).2
    omega

theorem layPre_length_le : (layPre es ℓ K).length ≤ es.sum := by
  rw [layPre_length, lay_sum H]
  have := H.b_lt
  have := H.K_le
  have : layB ℓ K * es.length ≤ es.length * (ℓ - 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The chunk slots `(i, h)`, `b ≤ h < ℓ - 1`, are not listed for the prefix. -/
theorem lay_not_mem_pre {i h : ℕ} (hi : i < es.length) (hbh : layB ℓ K ≤ h) (hh : h < ℓ - 1) :
    off es i + h ∉ layPre es ℓ K := by
  intro hs
  simp only [layPre, List.mem_append, List.mem_map, List.mem_range] at hs
  have := H.ax_ge hi
  rcases hs with ⟨i', hi', e⟩ | ⟨m, hm, e⟩
  · rw [mem_layLongs] at hi'
    have := (lay_off_inj (by omega) (by omega) e).2
    omega
  · have hD : 0 < es.length := by omega
    have h1 := H.ax_ge (Nat.mod_lt m hD)
    have := H.b_lt
    have := H.K_le
    have hb0 : 0 < layB ℓ K := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at hm; omega)
    revert e h1
    generalize m / es.length = j
    intro e h1
    have := (lay_off_inj (by omega) (by omega) e).2
    omega

/-- `N - |pre| = D q K`: the chunk region. -/
theorem lay_chunk_size : es.sum - (layPre es ℓ K).length = K * (es.length * layQ ℓ K) := by
  rw [layPre_length, lay_sum H]
  have := (lay_bqK (ℓ := ℓ) (K := K))
  have : es.length * (ℓ - 1) = layB ℓ K * es.length + K * (es.length * layQ ℓ K) := by
    rw [← this]; ring
  omega

/-- After the prefix moves, chunk slot `(i, h)` sits at `(D - 1 - i) q K + (h - b)`: the axes in
order from the top, each a run of `q` chunks. -/
theorem layPos_chunk {i h : ℕ} (hi : i < es.length) (hbh : layB ℓ K ≤ h) (hh : h < ℓ - 1) :
    layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length (off es i + h) =
      (es.length - 1 - i) * (layQ ℓ K * K) + (h - layB ℓ K) := by
  set D := es.length
  set b := layB ℓ K
  set W := layQ ℓ K * K with hW
  have hWpos : 0 < W := Nat.mul_pos H.q_pos H.K_pos
  have hbq := (lay_bqK (ℓ := ℓ) (K := K))
  have hhb : h - b < W := by omega
  set pre := layPre es ℓ K
  set N := es.sum
  obtain ⟨_, _, _, hmono⟩ := layPos_spec ((layPre_nodup H)) ((layPre_lt H)) ((layPre_length_le H))
    pre.length le_rfl
  rw [List.take_length] at hmono
  have hsize : N - pre.length = D * W := by rw [(lay_chunk_size H)]; rw [hW]; ring
  -- the slot at chunk-region position `y`
  let ψ : ℕ → ℕ := fun y => off es (D - 1 - y / W) + (b + y % W)
  have hψ : ∀ y < D * W, D - 1 - y / W < D ∧ b ≤ b + y % W ∧ b + y % W < ℓ - 1 := by
    intro y hy
    have h1 : y / W < D := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have h2 := Nat.mod_lt y hWpos
    generalize y / W = u at *
    generalize y % W = v at *
    omega
  have hψN : ∀ y < D * W, ψ y < N := by
    intro y hy
    obtain ⟨h1, _, h3⟩ := hψ y hy
    have := off_add_ax_le es (D - 1 - y / W)
    have := H.ax_ge h1
    show off es (D - 1 - y / W) + (b + y % W) < es.sum
    omega
  have hψpre : ∀ y < D * W, ψ y ∉ pre := fun y hy =>
    (lay_not_mem_pre H) (hψ y hy).1 (hψ y hy).2.1 (hψ y hy).2.2
  have hψmono : ∀ y y', y < y' → y' < D * W → ψ y < ψ y' := by
    intro y y' hyy hy'
    have hy : y < D * W := by omega
    have hdiv : y / W ≤ y' / W := Nat.div_le_div_right hyy.le
    rcases Nat.lt_or_eq_of_le hdiv with hlt | heq
    · have hlt' : D - 1 - y' / W < D - 1 - y / W := by
        have : y' / W < D := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        generalize y / W = u at *
        generalize y' / W = u' at *
        omega
      have := off_le_of_lt es hlt'
      have := H.ax_ge (hψ y hy).1
      have := Nat.mod_lt y hWpos
      show off es (D - 1 - y / W) + (b + y % W) < off es (D - 1 - y' / W) + (b + y' % W)
      omega
    · have hmod : y % W < y' % W := by
        have e1 := Nat.div_add_mod y W
        have e2 := Nat.div_add_mod y' W
        rw [heq] at e1
        omega
      show off es (D - 1 - y / W) + (b + y % W) < off es (D - 1 - y' / W) + (b + y' % W)
      rw [heq]
      omega
  have hid := lay_strictMono_id (n := D * W) (fun y => layPos N pre pre.length (ψ y))
    (fun y hy => by
      have := layPos_nonpre (layPre_nodup H) (layPre_lt H) (layPre_length_le H) (hψN y hy) (hψpre y hy)
      rw [hsize] at this; exact this)
    (fun y y' hyy hy' => hmono _ (hψN y (by omega)) _ (hψN y' hy') (hψmono y y' hyy hy')
      (hψpre y (by omega)) (hψpre y' hy'))
  set y := (D - 1 - i) * W + (h - b) with hy
  have hyl : y < D * W := by
    have : (D - 1 - i + 1) * W ≤ D * W := Nat.mul_le_mul_right W (by omega)
    rw [Nat.add_mul] at this; omega
  have hdiv : y / W = D - 1 - i := by
    rw [hy, Nat.add_comm, Nat.add_mul_div_right _ _ hWpos, Nat.div_eq_of_lt hhb, Nat.zero_add]
  have hmod : y % W = h - b := by
    rw [hy, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hhb]
  have hψy : ψ y = off es i + h := by
    show off es (D - 1 - y / W) + (b + y % W) = off es i + h
    rw [hdiv, hmod, show D - 1 - (D - 1 - i) = i by omega, show b + (h - b) = h by omega]
  have := hid y hyl
  rw [hψy] at this
  exact this

omit H in
theorem layXcMoves_valid {m N : ℕ} (hK : 1 ≤ K) (hm : K * m ≤ N) {xs : List (ℕ × ℕ)}
    (hxs : ∀ e ∈ xs, e.1 < e.2 ∧ e.2 < m) : ∀ mv ∈ layXcMoves K xs, mv.Valid K N := by
  intro mv hmv
  simp only [layXcMoves, List.mem_map] at hmv
  obtain ⟨e, he, rfl⟩ := hmv
  obtain ⟨h1, h2⟩ := hxs e he
  have a1 : (e.1 + 1) * K ≤ e.2 * K := Nat.mul_le_mul_right K h1
  have a2 : (e.2 + 1) * K ≤ m * K := Nat.mul_le_mul_right K h2
  rw [Nat.add_mul] at a1 a2
  rw [Nat.mul_comm K m] at hm
  exact ⟨by omega, by omega, Or.inl (by omega)⟩

omit H in
/-- The chunk exchanges of the layout. -/
theorem laySwaps_layTr_spec :
    (∀ x, layRun K (layXcMoves K (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K)))) x =
      layChunkFun K (layTr es.length (layQ ℓ K)) x) ∧
    (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K))).length ≤
      es.length * layQ ℓ K - 1 ∧
    ∀ e ∈ laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K)),
      e.1 < e.2 ∧ e.2 < es.length * layQ ℓ K :=
  laySwaps_spec K _ _ le_rfl (fun c hc => absurd c.isLt (by omega))

theorem layMoves_valid : ∀ m ∈ layMoves es ℓ K, m.Valid K es.sum := by
  intro m hm
  rw [layMoves, List.mem_append] at hm
  rcases hm with hm | hm
  · exact layPreMoves_valid K (layPre_nodup H) (layPre_lt H) (layPre_length_le H) m hm
  · refine layXcMoves_valid H.K_pos ?_ (laySwaps_layTr_spec (es := es) (ℓ := ℓ) (K := K)).2.2 m hm
    have := lay_chunk_size H
    omega

omit H in
/-- The layout map of positions: the prefix moves, then the chunk transposition. -/
theorem layRun_moves (x : ℕ) :
    layRun K (layMoves es ℓ K) x =
      layChunkFun K (layTr es.length (layQ ℓ K))
        (layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length x) := by
  rw [layMoves, layRun_append, layPreMoves, layRun_preMovesK,
    (laySwaps_layTr_spec (es := es) (ℓ := ℓ) (K := K)).1]

theorem layPerm_apply (x : Fin es.sum) :
    (layPerm es ℓ K x : ℕ) = layRun K (layMoves es ℓ K) x :=
  layMovesPerm_apply (layMoves_valid H) x

/-- The chunk slot `(i, h)`, `b ≤ h < ℓ - 1`, ends at offset `ρ = (h - b) mod K` of chunk
`⌊(h - b)/K⌋ D + (D - 1 - i)`. -/
theorem layRun_chunk {i h : ℕ} (hi : i < es.length) (hbh : layB ℓ K ≤ h) (hh : h < ℓ - 1) :
    layRun K (layMoves es ℓ K) (off es i + h) =
      (h - layB ℓ K) % K + K * ((h - layB ℓ K) / K * es.length + (es.length - 1 - i)) := by
  rw [layRun_moves, layPos_chunk H hi hbh hh]
  have hbq := lay_bqK (ℓ := ℓ) (K := K)
  set D := es.length
  set q := layQ ℓ K
  set b := layB ℓ K
  have hK := H.K_pos
  have hhb : h - b < q * K := by omega
  have ht : (h - b) / K < q := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hρ : (h - b) % K < K := Nat.mod_lt _ (by omega)
  have hc : (D - 1 - i) * q + (h - b) / K < D * q := by
    have : (D - 1 - i + 1) * q ≤ D * q := Nat.mul_le_mul_right q (by omega)
    rw [Nat.add_mul] at this; omega
  have e : (D - 1 - i) * (q * K) + (h - b) = ((D - 1 - i) * q + (h - b) / K) * K + (h - b) % K := by
    have := Nat.div_add_mod' (h - b) K
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, this]
  rw [e, layChunkFun_chunk K _ hc hρ]
  have hTr := layTr_apply D q (i := D - 1 - i) (t := (h - b) / K) (by omega) ht
  rw [show ((layTr D q ⟨(D - 1 - i) * q + (h - b) / K, hc⟩ : Fin (D * q)) : ℕ) =
    (h - b) / K * D + (D - 1 - i) from hTr]
  ring

/-- The listed slot `pre[m]` ends at the top position `N - 1 - m`. -/
theorem layRun_pre {m : ℕ} (hm : m < (layPre es ℓ K).length) :
    layRun K (layMoves es ℓ K) ((layPre es ℓ K).getD m 0) = es.sum - 1 - m := by
  rw [layRun_moves, (layPos_spec (layPre_nodup H) (layPre_lt H) (layPre_length_le H) _ le_rfl).2.2.1 m hm]
  apply layChunkFun_of_ge
  have := lay_chunk_size H
  omega

omit H in
theorem layLongs_getElem? {i : ℕ} (hi : i < es.length) (hl : ax es i = ℓ) :
    (layLongs es ℓ)[layLrank es ℓ i]? = some i := by
  have e : List.range es.length = List.range i ++ i :: (List.range (es.length - (i + 1))).map
      (fun x => i + 1 + x) := by
    have := @List.range_add (i + 1) (es.length - (i + 1))
    rw [show i + 1 + (es.length - (i + 1)) = es.length by omega] at this
    rw [this, List.range_succ, List.append_assoc]
    rfl
  rw [layLongs, layLrank, e, List.filter_append, List.filter_cons_of_pos (by simpa using hl),
    List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero]

omit H in
theorem layPre_getD_long {i : ℕ} (hi : i < es.length) (hl : ax es i = ℓ) :
    (layPre es ℓ K).getD (layLrank es ℓ i) 0 = off es i + (ℓ - 1) := by
  have h1 := layLongs_getElem? hi hl
  have hlt : layLrank es ℓ i < (layLongs es ℓ).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h1
    exact absurd h1 (by simp)
  rw [List.getD_eq_getElem?_getD, layPre, List.getElem?_append_left (by simpa using hlt),
    List.getElem?_map, h1]
  rfl

omit H in
theorem layPre_getD_low {i h : ℕ} (hi : i < es.length) (hh : h < layB ℓ K) :
    (layPre es ℓ K).getD ((layLongs es ℓ).length + ((layB ℓ K - 1 - h) * es.length + i)) 0 =
      off es i + h := by
  set D := es.length
  set b := layB ℓ K
  have hj : (b - 1 - h) * D + i < b * D := by
    have : (b - 1 - h + 1) * D ≤ b * D := Nat.mul_le_mul_right D (by omega)
    rw [Nat.add_mul] at this; omega
  rw [List.getD_eq_getElem?_getD, layPre, List.getElem?_append_right (by simp),
    List.length_map, Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]
  have hD : 0 < D := by omega
  have e1 : ((b - 1 - h) * D + i) % D = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have e2 : ((b - 1 - h) * D + i) / D = b - 1 - h := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hi, Nat.zero_add]
  rw [e1, e2, show b - 1 - (b - 1 - h) = h by omega]

/-- The top slot `(i, ℓ - 1)` of the long axis `i` ends at `N - 1 - (its rank among the long
axes)`. -/
theorem layRun_top {i : ℕ} (hi : i < es.length) (hl : ax es i = ℓ) :
    layRun K (layMoves es ℓ K) (off es i + (ℓ - 1)) = es.sum - 1 - layLrank es ℓ i := by
  rw [← layPre_getD_long hi hl]
  apply layRun_pre H
  have h1 := layLongs_getElem? hi hl
  have hlt : layLrank es ℓ i < (layLongs es ℓ).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h1
    exact absurd h1 (by simp)
  rw [layPre_length]; omega

/-- The bottom slot `(i, h)`, `h < b`, ends at `N - 1 - (#long + (b - 1 - h) D + i)`. -/
theorem layRun_low {i h : ℕ} (hi : i < es.length) (hh : h < layB ℓ K) :
    layRun K (layMoves es ℓ K) (off es i + h) =
      es.sum - 1 - ((layLongs es ℓ).length + ((layB ℓ K - 1 - h) * es.length + i)) := by
  rw [← layPre_getD_low hi hh]
  apply layRun_pre H
  rw [layPre_length]
  have : (layB ℓ K - 1 - h + 1) * es.length ≤ layB ℓ K * es.length :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at this; omega

/-! ### The selected bits of every round in the layout -/

omit H in
theorem layPerm_sel_eq (h : ℕ) (L : Equiv.Perm (Fin es.sum)) (f : ℕ → ℕ)
    (hf : ∀ x : Fin es.sum, (L x : ℕ) = f x) :
    (selFin es h).map (fun x => (L x : ℕ)) = (parts es h).map fun i => f (off es i + h) := by
  have e1 : (selFin es h).map (fun x => (L x : ℕ)) = ((selFin es h).map Fin.val).map f := by
    rw [List.map_map]; exact List.map_congr_left fun x _ => hf x
  rw [e1, selFin_map_val, selBits, List.map_map]
  rfl

theorem lay_parts_all {h : ℕ} (hh : h < ℓ - 1) : parts es h = List.range es.length := by
  unfold parts
  apply List.filter_eq_self.2
  intro i hi
  have := H.ax_ge (List.mem_range.1 hi)
  simp only [decide_eq_true_eq]
  omega

theorem lay_parts_top : parts es (ℓ - 1) = layLongs es ℓ := by
  unfold parts layLongs
  apply List.filter_congr
  intro i hi
  have := H.ax_of_lt (List.mem_range.1 hi)
  have := H.ℓ_ge
  simp only [decide_eq_decide]
  omega

/-- The common offset `ρ = (h - b) mod K` of the round at named position `h`. -/
def layRho (ℓ K h : ℕ) : ℕ := (h - layB ℓ K) % K

/-- The first chunk `c₀ = ⌊(h - b)/K⌋ D` of the round at named position `h`. -/
def layC0 (es : List ℕ) (ℓ K h : ℕ) : ℕ := (h - layB ℓ K) / K * es.length

/-- **Chunk rounds.** For `b ≤ h < ℓ - 1` all `D` axes participate, and after the layout the
selected bit of axis `i` is bit `ρ` of chunk `c₀ + (D - 1 - i)`: the selected bits are
`ρ + K (c₀ + j)`, `j < D`, at a common offset in `D` consecutive chunks. -/
theorem layPerm_sel_chunk {h : ℕ} (hbh : layB ℓ K ≤ h) (hh : h < ℓ - 1) :
    (selFin es h).map (fun x => (layPerm es ℓ K x : ℕ)) =
      (List.range es.length).map fun i =>
        layRho ℓ K h + K * (layC0 es ℓ K h + (es.length - 1 - i)) := by
  rw [layPerm_sel_eq h _ _ (layPerm_apply H), lay_parts_all H hh]
  refine List.map_congr_left fun i hi => ?_
  rw [layRun_chunk H (List.mem_range.1 hi) hbh hh]
  rfl

omit H in
theorem lay_map_range_rev (f : ℕ → ℕ) (D : ℕ) :
    (List.range D).map (fun i => f (D - 1 - i)) = ((List.range D).map f).reverse := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
    List.length_range]

/-- The chunk rounds as a set: `D' = |parts| = D` positions `ρ + K (c₀ + j)`, `j < D'`. -/
theorem layPerm_sel_chunk_perm {h : ℕ} (hbh : layB ℓ K ≤ h) (hh : h < ℓ - 1) :
    ((selFin es h).map (fun x => (layPerm es ℓ K x : ℕ))).Perm
      ((List.range (parts es h).length).map fun j => layRho ℓ K h + K * (layC0 es ℓ K h + j)) := by
  rw [layPerm_sel_chunk H hbh hh, lay_parts_all H hh, List.length_range,
    lay_map_range_rev (fun j => layRho ℓ K h + K * (layC0 es ℓ K h + j))]
  exact List.reverse_perm _

/-- The chunks of a chunk round lie inside the chunk region: `ρ < K` and
`c₀ + D ≤ D q`. -/
theorem layC0_bound {h : ℕ} (hbh : layB ℓ K ≤ h) (hh : h < ℓ - 1) :
    layRho ℓ K h < K ∧ layC0 es ℓ K h + es.length ≤ es.length * layQ ℓ K ∧
      K * (es.length * layQ ℓ K) ≤ es.sum := by
  have hK := H.K_pos
  have hbq := lay_bqK (ℓ := ℓ) (K := K)
  have ht : (h - layB ℓ K) / K < layQ ℓ K := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; omega)
  refine ⟨Nat.mod_lt _ (by omega), ?_, by have := lay_chunk_size H; omega⟩
  unfold layC0
  have : ((h - layB ℓ K) / K + 1) * es.length ≤ layQ ℓ K * es.length :=
    Nat.mul_le_mul_right _ ht
  rw [Nat.add_mul] at this
  rw [Nat.mul_comm es.length]; omega

/-- **The top round** `h = ℓ - 1` involves the long axes; long axis `i` has its selected bit at
`N - 1 - (its rank among the long axes)`. -/
theorem layPerm_sel_top :
    (selFin es (ℓ - 1)).map (fun x => (layPerm es ℓ K x : ℕ)) =
      (layLongs es ℓ).map fun i => es.sum - 1 - layLrank es ℓ i := by
  rw [layPerm_sel_eq _ _ _ (layPerm_apply H), lay_parts_top H]
  refine List.map_congr_left fun i hi => ?_
  rw [mem_layLongs] at hi
  exact layRun_top H hi.1 hi.2

/-- **The bottom rounds** `h < b` involve all axes; axis `i` has its selected bit at
`N - 1 - (#long + (b - 1 - h) D + i)`. -/
theorem layPerm_sel_low {h : ℕ} (hh : h < layB ℓ K) :
    (selFin es h).map (fun x => (layPerm es ℓ K x : ℕ)) =
      (List.range es.length).map fun i =>
        es.sum - 1 - ((layLongs es ℓ).length + ((layB ℓ K - 1 - h) * es.length + i)) := by
  have hb := H.b_lt
  have hKl := H.K_le
  rw [layPerm_sel_eq _ _ _ (layPerm_apply H), lay_parts_all H (by omega)]
  refine List.map_congr_left fun i hi => ?_
  exact layRun_low H (List.mem_range.1 hi) hh

omit H in
/-- At most `D (b + 1)` prefix moves and at most `D q - 1` chunk exchanges. -/
theorem layMoves_counts :
    (layPreMoves es.sum (layPre es ℓ K)).length ≤ es.length * (layB ℓ K + 1) ∧
      (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K))).length ≤
        es.length * layQ ℓ K - 1 := by
  refine ⟨?_, (laySwaps_layTr_spec (es := es) (ℓ := ℓ) (K := K)).2.1⟩
  rw [layPreMoves, layPreMovesK, List.length_map, List.length_range, layPre_length]
  have : (layLongs es ℓ).length ≤ es.length := by
    rw [layLongs]; exact (List.length_filter_le _ _).trans (by simp)
  rw [Nat.mul_add, Nat.mul_comm (layB ℓ K)]
  omega

end Layout

/-! ### Rounds in a layout: the physical butterflies -/

section Relabel

open IntegerMultBounds.MathlibTM2.Layer

variable {X : Type} {N : ℕ}

theorem lay_flip_comp (L : Equiv.Perm (Fin N)) (q : Fin N) (b : Fin N → ZMod 2) :
    Layer.flip q (b ∘ L) = (Layer.flip (L q) b) ∘ L := by
  funext j
  simp only [Layer.flip, Pi.add_apply, Function.comp_apply, Pi.single_apply,
    L.injective.eq_iff]

theorem lay_relabel_hBit (L : Equiv.Perm (Fin N)) (q : Fin N) (f : Arr X N) :
    relabel L (hBit q f) = hBit (L q) (relabel L f) := by
  funext p
  obtain ⟨c, b⟩ := p
  simp only [relabel, hBit, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [lay_flip_comp]

/-- Butterflies on the logical bits `l` of an array stored in the layout `L` are the butterflies
on the physical bits `l.map L`. -/
theorem lay_relabel_Hl (L : Equiv.Perm (Fin N)) (l : List (Fin N)) (f : Arr X N) :
    relabel L (Hl X l (relabel L.symm f)) = Hl X (l.map L) f := by
  induction l generalizing f with
  | nil =>
      simp only [Hl, List.map_nil, List.prod_nil, Module.End.one_apply]
      exact relabel_relabel_symm L f
  | cons q l ih =>
      rw [Hl_cons, List.map_cons, Hl_cons, lay_relabel_hBit, ← ih]

variable {r : ℕ} [NeZero r]

/-- The forward round in the layout `L`: the butterflies on the physical bits
`(selFin es h).map L`, then the twiddle read through the layout. -/
theorem lay_fwdRoundFlatL_eq (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (h : ℕ)
    (f : Arr (Fin r) es.sum) :
    fwdRoundFlatL es L h f =
      relabel L (twFwdFlat es h (relabel L.symm (Hl (Fin r) ((selFin es h).map L) f))) := by
  rw [fwdRoundFlatL, fwdRoundFlat, ← lay_relabel_Hl, relabel_symm_relabel]

omit [NeZero r] in
/-- The opposite round in the layout `L`: the twiddle read through the layout, then the
butterflies on the physical bits `(selFin es h).map L`. -/
theorem lay_oppRoundFlatL_eq (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (h : ℕ)
    (f : Arr (Fin r) es.sum) :
    oppRoundFlatL es L h f =
      Hl (Fin r) ((selFin es h).map L) (relabel L (twOppFlat es h (relabel L.symm f))) := by
  rw [oppRoundFlatL, oppRoundFlat, ← lay_relabel_Hl, relabel_symm_relabel]

end Relabel

end IntegerMultBounds.MathlibTM2.Fast
