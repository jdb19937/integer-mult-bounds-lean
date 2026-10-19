module

public import IntegerMultBounds.MathlibTM2.M8.ReversedExchange
public import IntegerMultBounds.MathlibTM2.M8.GenericBasis
public import IntegerMultBounds.Swap.PivotRank
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Generic projectors have reversed pivots

A factorization `A = E₁ Π E₂` with lower-triangular invertible `E₁`, `E₂` keeps the rank of
every northeast rectangle: rows before `i` and columns from `j` on. That rank is the number of
pivots in the rectangle (`rank_mask`). In a generic basis, `P C` has northeast rectangles of rank
`min(i, m - j, r)` (`rank_mask_rev`), and those counts force the pivots to be `revPivots m r`
(`pivots_forced`). So every factorization of `P C` (`Swap.LowerTriangular.factorization`) has
the reversed pivots (`exists_rev_factor`). This is the factorization `revExchange_factor` needs,
so a generic projector's reversed exchange is lower-triangular transformations, shears and the
`r` reversed interchanges of one reversed child (`revExchange_generic`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.ReversedPivots

noncomputable section
open Matrix
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix)
open ReversedExchange (rev revPivots)

variable {m : ℕ}

/-- The rows before `i`. -/
def rowsBefore (i : ℕ) : Matrix (Fin m) (Fin m) ℚ := diagonal fun k => if k.val < i then 1 else 0

/-- The columns from `j` on. -/
def colsFrom (j : ℕ) : Matrix (Fin m) (Fin m) ℚ := diagonal fun k => if j ≤ k.val then 1 else 0

theorem rowsBefore_idem (i : ℕ) : rowsBefore (m := m) i * rowsBefore i = rowsBefore i := by
  rw [rowsBefore, diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp

theorem colsFrom_idem (j : ℕ) : colsFrom (m := m) j * colsFrom j = colsFrom j := by
  rw [colsFrom, diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp

theorem rowsBefore_lower {E : Matrix (Fin m) (Fin m) ℚ} (hE : LowerTriangular E) (i : ℕ) :
    rowsBefore i * E * rowsBefore i = rowsBefore i * E := by
  ext a c
  simp only [rowsBefore, diagonal_mul, mul_diagonal]
  by_cases ha : a.val < i
  · by_cases hc : c.val < i
    · simp [ha, hc]
    · have hlt : a < c := by rw [Fin.lt_def]; omega
      simp [ha, hc, hE a c hlt]
  · simp [ha]

theorem colsFrom_lower {E : Matrix (Fin m) (Fin m) ℚ} (hE : LowerTriangular E) (j : ℕ) :
    colsFrom j * E * colsFrom j = E * colsFrom j := by
  ext a b
  simp only [colsFrom, diagonal_mul, mul_diagonal]
  by_cases hb : j ≤ b.val
  · by_cases ha : j ≤ a.val
    · simp [ha, hb]
    · have hlt : a < b := by rw [Fin.lt_def]; omega
      simp [ha, hb, hE a b hlt]
  · simp [hb]

/-- The restriction of a lower-triangular invertible matrix to the rows before `i`, completed by
the identity, is invertible. -/
theorem isUnit_rows {E E' : Matrix (Fin m) (Fin m) ℚ} (hE : LowerTriangular E)
    (hE' : LowerTriangular E') (hinv : E * E' = 1) (i : ℕ) :
    IsUnit (rowsBefore i * E * rowsBefore i + (1 - rowsBefore i)).det := by
  set Ri := rowsBefore (m := m) i
  have hRi : Ri * Ri = Ri := rowsBefore_idem i
  have h1 : (Ri * E * Ri + (1 - Ri)) * (Ri * E' * Ri + (1 - Ri)) = 1 := by
    have e1 : Ri * E * Ri * (Ri * E' * Ri) = Ri := by
      calc Ri * E * Ri * (Ri * E' * Ri) = Ri * E * (Ri * Ri * E' * Ri) := by
              simp only [Matrix.mul_assoc]
        _ = Ri * E * (Ri * E') := by rw [hRi, rowsBefore_lower hE' i]
        _ = (Ri * E * Ri) * E' := by rw [← Matrix.mul_assoc, rowsBefore_lower hE i]
        _ = Ri := by rw [rowsBefore_lower hE i, Matrix.mul_assoc, hinv, Matrix.mul_one]
    have e2 : Ri * E * Ri * (1 - Ri) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc _ Ri Ri, hRi, sub_self]
    have e3 : (1 - Ri) * (Ri * E' * Ri) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      simp only [← Matrix.mul_assoc, hRi, sub_self]
    have e4 : (1 - Ri) * (1 - Ri) = 1 - Ri := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hRi, sub_self, sub_zero]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4]
    abel
  exact IsUnit.of_mul_eq_one _ (by rw [← det_mul, h1, det_one])

/-- The restriction to the columns from `j` on, completed by the identity, is invertible. -/
theorem isUnit_cols {E E' : Matrix (Fin m) (Fin m) ℚ} (hE : LowerTriangular E)
    (hE' : LowerTriangular E') (hinv : E * E' = 1) (j : ℕ) :
    IsUnit (colsFrom j * E * colsFrom j + (1 - colsFrom j)).det := by
  set Cj := colsFrom (m := m) j
  have hCj : Cj * Cj = Cj := colsFrom_idem j
  have h1 : (Cj * E * Cj + (1 - Cj)) * (Cj * E' * Cj + (1 - Cj)) = 1 := by
    have e1 : Cj * E * Cj * (Cj * E' * Cj) = Cj := by
      calc Cj * E * Cj * (Cj * E' * Cj) = Cj * E * Cj * (E' * Cj) := by
              rw [colsFrom_lower hE' j]
        _ = Cj * (E * Cj) * (E' * Cj) := by rw [Matrix.mul_assoc Cj E Cj]
        _ = Cj * (Cj * E * Cj) * (E' * Cj) := by rw [colsFrom_lower hE j]
        _ = Cj * E * (Cj * E' * Cj) := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc Cj Cj, hCj]
        _ = Cj * E * (E' * Cj) := by rw [colsFrom_lower hE' j]
        _ = Cj := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hinv, Matrix.one_mul, hCj]
    have e2 : Cj * E * Cj * (1 - Cj) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc _ Cj Cj, hCj, sub_self]
    have e3 : (1 - Cj) * (Cj * E' * Cj) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      simp only [← Matrix.mul_assoc, hCj, sub_self]
    have e4 : (1 - Cj) * (1 - Cj) = 1 - Cj := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hCj, sub_self, sub_zero]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4]
    abel
  exact IsUnit.of_mul_eq_one _ (by rw [← det_mul, h1, det_one])

/-- The pivots in a northeast rectangle. -/
def inRect (i j : ℕ) (p : Fin m × Fin m) : Bool := decide (p.1.val < i ∧ j ≤ p.2.val)

theorem mask_pivotMatrix (L : List (Fin m × Fin m)) (hL : L.Nodup) (i j : ℕ) :
    rowsBefore i * pivotMatrix L * colsFrom j = pivotMatrix (L.filter (inRect i j)) := by
  ext a b
  rw [IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ (hL.filter _)]
  simp only [rowsBefore, colsFrom, diagonal_mul, mul_diagonal,
    IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ hL, List.mem_filter, inRect,
    decide_eq_true_eq]
  by_cases ha : a.val < i <;> by_cases hb : j ≤ b.val <;> by_cases hm : (a, b) ∈ L <;> simp [ha, hb, hm]

/-- **Northeast ranks.** Under `A = E₁ Π E₂` with lower-triangular invertible factors, the rank of
the northeast rectangle (rows before `i`, columns from `j` on) is its number of pivots. -/
theorem rank_mask (E₁ E₁' E₂ E₂' : Matrix (Fin m) (Fin m) ℚ) (hl₁ : LowerTriangular E₁)
    (hl₁' : LowerTriangular E₁') (hl₂ : LowerTriangular E₂) (hl₂' : LowerTriangular E₂')
    (hinv₁ : E₁ * E₁' = 1) (hinv₂ : E₂ * E₂' = 1) (L : List (Fin m × Fin m))
    (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup) (i j : ℕ) :
    (rowsBefore i * (E₁ * pivotMatrix L * E₂) * colsFrom j).rank =
      (L.filter (inRect i j)).length := by
  set Ri := rowsBefore (m := m) i
  set Cj := colsFrom (m := m) j
  set G := Ri * E₁ * Ri + (1 - Ri)
  set H := Cj * E₂ * Cj + (1 - Cj)
  have hG : Ri * E₁ = G * Ri := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ Ri Ri,
      rowsBefore_idem, sub_self, add_zero, rowsBefore_lower hl₁]
  have hH : E₂ * Cj = Cj * H := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Cj, colsFrom_idem, sub_self, add_zero]
    rw [colsFrom_lower hl₂]
  have hL : L.Nodup := h₁.of_map _
  have he : Ri * (E₁ * pivotMatrix L * E₂) * Cj = G * (Ri * pivotMatrix L * Cj) * H := by
    calc Ri * (E₁ * pivotMatrix L * E₂) * Cj = (Ri * E₁) * pivotMatrix L * (E₂ * Cj) := by
            simp only [Matrix.mul_assoc]
      _ = G * (Ri * pivotMatrix L * Cj) * H := by
            rw [hG, hH]
            simp only [Matrix.mul_assoc]
  rw [he, rank_mul_eq_left_of_isUnit_det H _ (isUnit_cols hl₂ hl₂' hinv₂ j),
    rank_mul_eq_right_of_isUnit_det G _ (isUnit_rows hl₁ hl₁' hinv₁ i), mask_pivotMatrix L hL]
  apply IntegerMultBounds.Swap.PivotRank.rank_pivotMatrix
  · exact h₁.sublist ((List.filter_sublist).map _)
  · exact h₂.sublist ((List.filter_sublist).map _)

/-! ### The counts force the reversed pivots -/

theorem length_filter_eq_sum (L : List (Fin m × Fin m)) (i j : ℕ) :
    ((L.filter (inRect i j)).length : ℤ) =
      (L.map fun p => if p.1.val < i ∧ j ≤ p.2.val then (1 : ℤ) else 0).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h : p.1.val < i ∧ j ≤ p.2.val
    · have hp : inRect i j p = true := by simp [inRect, h]
      simp only [hp, h, ↓reduceIte, List.length_cons, Nat.cast_succ, ih, and_self]
      ring
    · have hp : inRect i j p = false := by simp [inRect, h]
      simp only [hp, h, Bool.false_eq_true, ↓reduceIte, zero_add, ih]

/-- The four rectangle counts around a cell count the pivots at the cell. -/
theorem cell_count (L : List (Fin m × Fin m)) (hL : L.Nodup) (a b : Fin m) :
    ((L.filter (inRect (a.val + 1) b.val)).length : ℤ) - (L.filter (inRect a.val b.val)).length -
      (L.filter (inRect (a.val + 1) (b.val + 1))).length + (L.filter (inRect a.val (b.val + 1))).length =
      if (a, b) ∈ L then 1 else 0 := by
  simp only [length_filter_eq_sum]
  have hcell : ∀ p : Fin m × Fin m,
      ((if p.1.val < a.val + 1 ∧ b.val ≤ p.2.val then (1 : ℤ) else 0) -
        (if p.1.val < a.val ∧ b.val ≤ p.2.val then 1 else 0) -
        (if p.1.val < a.val + 1 ∧ b.val + 1 ≤ p.2.val then 1 else 0) +
        (if p.1.val < a.val ∧ b.val + 1 ≤ p.2.val then 1 else 0)) =
      if p = (a, b) then 1 else 0 := by
    rintro ⟨x, y⟩
    simp only [Prod.mk.injEq, Fin.ext_iff]
    split_ifs <;> omega
  have hsum : ∀ l : List (Fin m × Fin m),
      (l.map fun p => if p.1.val < a.val + 1 ∧ b.val ≤ p.2.val then (1 : ℤ) else 0).sum -
        (l.map fun p => if p.1.val < a.val ∧ b.val ≤ p.2.val then (1 : ℤ) else 0).sum -
        (l.map fun p => if p.1.val < a.val + 1 ∧ b.val + 1 ≤ p.2.val then (1 : ℤ) else 0).sum +
        (l.map fun p => if p.1.val < a.val ∧ b.val + 1 ≤ p.2.val then (1 : ℤ) else 0).sum =
      (l.map fun p => if p = (a, b) then (1 : ℤ) else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← hcell p, ← ih]
      ring
  rw [hsum]
  have hcount : ∀ l : List (Fin m × Fin m), l.Nodup →
      (l.map fun p => if p = (a, b) then (1 : ℤ) else 0).sum = if (a, b) ∈ l then 1 else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons p l ih =>
      have hl' := List.nodup_cons.mp hl
      simp only [List.map_cons, List.sum_cons, List.mem_cons, ih hl'.2]
      by_cases hp : p = (a, b)
      · subst hp
        simp [hl'.1]
      · simp only [hp, ↓reduceIte, zero_add]
        by_cases hm : (a, b) ∈ l
        · simp [hm]
        · simp [hm, Ne.symm hp]
  exact hcount L hL

/-- **Forced pivots.** If every northeast rectangle (rows before `i`, columns from `j` on) holds
`min(i, m - j, r)` pivots, the pivots are `(k, m-1-k)` for `k < r`. -/
theorem pivots_forced (L : List (Fin m × Fin m)) (hL : L.Nodup) (r : ℕ)
    (hc : ∀ i j, (L.filter (inRect i j)).length = min i (min (m - j) r)) (p : Fin m × Fin m) :
    p ∈ L ↔ p.1.val < r ∧ p.2 = p.1.rev := by
  obtain ⟨a, b⟩ := p
  have h := cell_count L hL a b
  rw [hc, hc, hc, hc] at h
  have hb : b = a.rev ↔ b.val = m - 1 - a.val := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  simp only [hb]
  have ha := a.isLt
  have hb' := b.isLt
  by_cases hm : (a, b) ∈ L
  · simp only [hm, ↓reduceIte, Nat.cast_min] at h
    simp only [hm, true_iff]
    omega
  · simp only [hm, ↓reduceIte, Nat.cast_min] at h
    simp only [hm, false_iff, not_and]
    omega

/-! ### Northeast ranks of a generic projector -/

theorem rank_rowsBefore_le (i : ℕ) : (rowsBefore (m := m) i).rank ≤ i := by
  rw [rowsBefore, rank_diagonal]
  calc Fintype.card {k : Fin m // (if k.val < i then (1 : ℚ) else 0) ≠ 0}
      ≤ Fintype.card (Fin i) := by
        apply Fintype.card_le_of_injective (fun k => ⟨k.1.val, by
          have := k.2
          split_ifs at this with h
          · exact h
          · exact absurd rfl this⟩)
        intro x y hxy
        exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val hxy))
    _ = i := Fintype.card_fin i

theorem rank_colsFrom_le (j : ℕ) : (colsFrom (m := m) j).rank ≤ m - j := by
  rw [colsFrom, rank_diagonal]
  calc Fintype.card {k : Fin m // (if j ≤ k.val then (1 : ℚ) else 0) ≠ 0}
      ≤ Fintype.card (Fin (m - j)) := by
        apply Fintype.card_le_of_injective (fun k => ⟨k.1.val - j, by
          have := k.2
          have hk := k.1.isLt
          split_ifs at this with h
          · omega
          · exact absurd rfl this⟩)
        intro x y hxy
        have hx := x.2
        have hy := y.2
        split_ifs at hx hy with h1 h2 h2
        · exact Subtype.ext (Fin.ext (by have := congrArg Fin.val hxy; simp at this; omega))
        all_goals simp_all
    _ = m - j := Fintype.card_fin _

theorem rev_apply (P : Matrix (Fin m) (Fin m) ℚ) (a b : Fin m) :
    (P * rev m : Matrix (Fin m) (Fin m) ℚ) a b = P a b.rev := by
  rw [mul_apply, Finset.sum_eq_single b.rev]
  · simp [rev]
  · intro k _ hk
    have hne : ¬ b = k.rev := by intro h; exact hk (by rw [h, Fin.rev_rev])
    simp only [rev, of_apply, hne, ↓reduceIte, mul_zero]
  · simp

theorem isUnit_det_rev : IsUnit (rev m : Matrix (Fin m) (Fin m) ℚ).det :=
  IsUnit.of_mul_eq_one _ (by rw [← det_mul, ReversedExchange.rev_mul_rev, det_one])

/-- **Northeast ranks of a generic projector.** In a basis where `P` is generic up to its rank
`r`, the northeast rectangle of `P C` with rows before `i` and columns from `j` on has rank
`min(i, m - j, r)`. -/
theorem rank_mask_rev (P : Matrix (Fin m) (Fin m) ℚ) (hgen : GenericBasis.Generic P P.rank)
    (i j : ℕ) :
    (rowsBefore i * (P * rev m) * colsFrom j).rank = min i (min (m - j) P.rank) := by
  apply le_antisymm
  · refine le_min ?_ (le_min ?_ ?_)
    · exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans (rank_rowsBefore_le i))
    · exact (rank_mul_le_right _ _).trans (rank_colsFrom_le j)
    · refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans ?_)
      rw [rank_mul_eq_left_of_isUnit_det _ _ isUnit_det_rev]
  · set k := min i (min (m - j) P.rank) with hk
    have hkm : k ≤ m := by
      have := rank_le_width P
      omega
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    have hsub : (rowsBefore i * (P * rev m) * colsFrom j).submatrix (Fin.castLE hkm)
        (fun c => (Fin.castLE hkm c).rev) =
        P.submatrix (Fin.castLE hkm) (Fin.castLE hkm) := by
      ext a c
      simp only [submatrix_apply, rowsBefore, colsFrom, diagonal_mul, mul_diagonal, rev_apply,
        Fin.rev_rev]
      have ha : (a : ℕ) < i := by have := a.isLt; omega
      have hc : j ≤ m - ((c : ℕ) + 1) := by have := c.isLt; omega
      simp [ha, hc]
    have hmin : GenericBasis.minor P ⟨k, Nat.lt_succ_of_le hkm⟩ ≠ 0 := by
      apply hgen
      simp only [GenericBasis.sizes, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hunit : IsUnit (P.submatrix (Fin.castLE hkm) (Fin.castLE hkm)) := by
      rw [isUnit_iff_isUnit_det]
      exact Ne.isUnit hmin
    have h1 := rank_submatrix_le (rowsBefore i * (P * rev m) * colsFrom j) (Fin.castLE hkm)
      (fun c => (Fin.castLE hkm c).rev)
    rw [hsub, rank_of_isUnit _ hunit, Fintype.card_fin] at h1
    exact h1

/-! ### The reversed factorization -/

/-- **Reversed factorization.** In a basis where `P` is generic up to its rank `r`, `P C` factors
as `E₁ Π_r E₂` with lower-triangular invertible `E₁`, `E₂` and the reversed pivots. -/
theorem exists_rev_factor (P : Matrix (Fin m) (Fin m) ℚ) (hgen : GenericBasis.Generic P P.rank) :
    ∃ E₁ E₁' E₂ E₂' : Matrix (Fin m) (Fin m) ℚ,
      LowerTriangular E₁ ∧ LowerTriangular E₁' ∧ LowerTriangular E₂ ∧ LowerTriangular E₂' ∧
      E₁ * E₁' = 1 ∧ E₁' * E₁ = 1 ∧ E₂ * E₂' = 1 ∧ E₂' * E₂ = 1 ∧
      P * rev m = E₁ * pivotMatrix (revPivots m P.rank) * E₂ := by
  obtain ⟨f⟩ := IntegerMultBounds.Swap.LowerTriangular.factorization (P * rev m)
  have hL : f.L.Nodup := f.nodup₁.of_map _
  have hc : ∀ i j, (f.L.filter (inRect i j)).length = min i (min (m - j) P.rank) := by
    intro i j
    rw [← rank_mask f.E₁ f.E₁' f.E₂ f.E₂' f.lower₁ f.lower₁' f.lower₂ f.lower₂' f.inv₁ f.inv₂ f.L
      f.nodup₁ f.nodup₂ i j, ← f.eq]
    exact rank_mask_rev P hgen i j
  have hpiv : pivotMatrix f.L = (pivotMatrix (revPivots m P.rank) : Matrix (Fin m) (Fin m) ℚ) := by
    have hR : (revPivots m P.rank).Nodup := (ReversedExchange.revPivots_fst m P.rank).of_map _
    ext a b
    rw [IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ hL,
      IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ hR]
    have hm := (pivots_forced f.L hL P.rank hc (a, b)).trans (ReversedExchange.mem_revPivots m P.rank a b).symm
    by_cases h : (a, b) ∈ f.L
    · simp only [h, hm.mp h, ↓reduceIte]
    · have h' : (a, b) ∉ revPivots m P.rank := fun h' => h (hm.mpr h')
      simp only [h, h', ↓reduceIte]
  exact ⟨f.E₁, f.E₁', f.E₂, f.E₂', f.lower₁, f.lower₁', f.lower₂, f.lower₂', f.inv₁, f.inv₁', f.inv₂,
    f.inv₂', f.eq.trans (by rw [hpiv])⟩

open IntegerMultBounds.Swap.Shear (State run) in
open Exchange (transform cross swaps kMat) in
/-- **One reversed child per projector.** For an idempotent `P` generic up to its rank `r`, the
reversed exchange `D'_P` is a lower-triangular transformation, a shear, the `r` reversed
interchanges `h_k ↔ d_{m-1-k}`, the opposite shear and the inverse transformation. -/
theorem revExchange_generic (P : Matrix (Fin m) (Fin m) ℚ) (hidem : P * P = P)
    (hgen : GenericBasis.Generic P P.rank) :
    ∃ L L' R' R'' : Matrix (Fin m) (Fin m) ℚ,
      LowerTriangular L ∧ LowerTriangular L' ∧ LowerTriangular R' ∧ LowerTriangular R'' ∧
      ∀ s : State (Fin m) ℚ,
        transform L R'' (cross (-kMat (pivotMatrix (revPivots m P.rank)) (R' * rev m * L))
          (run (swaps (revPivots m P.rank))
            (cross (kMat (pivotMatrix (revPivots m P.rank)) (R' * rev m * L)) (transform L' R' s)))) =
        ReversedExchange.revExchange P s := by
  obtain ⟨L, L', R', R'', hL, hL', hR, hR', h₁, h₁', h₂, h₂', hP⟩ := exists_rev_factor P hgen
  exact ⟨L, L', R', R'', hL, hL', hR, hR', fun s =>
    ReversedExchange.revExchange_factor L L' R' R'' P.rank h₁ h₁' h₂ h₂' P hP hidem s⟩

end
end IntegerMultBounds.MathlibTM2.M8.ReversedPivots
