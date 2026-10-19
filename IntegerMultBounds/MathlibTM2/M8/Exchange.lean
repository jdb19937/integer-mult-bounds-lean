module

public import IntegerMultBounds.Swap.PivotRank
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Exchange frames as cheap passes around cross swaps

For an idempotent `U`, the partial swap `D_U (h, d) = ((1 - U) h + U d, U h + (1 - U) d)`
exchanges the `U`-parts of the two address fields. Given a factorization `U = E₁ Π E₂` with
invertible `E₁`, `E₂` and a pivot matrix `Π` with distinct rows and columns, `D_U` is
`transform E₁ E₂⁻¹ ∘ cross (-K) ∘ swaps L ∘ cross K ∘ transform E₁⁻¹ E₂` (`exchange_factor`),
where `cross K` is the shear `d ← d + K h`, `swaps L` exchanges `h_i` with `d_j` for every pivot
`(i, j)`, `M = E₂ E₁` and `K = M Π Πᵀ - Πᵀ Π M + Πᵀ Π M Π Πᵀ - Πᵀ` (`kMat`). The swaps are
exactly the `L.length` interchanges; every other step is a transformation within one field or a
shear of the later field by the earlier one. The identities hold over every commutative ring.

* `swaps_run`: the swaps act as `(h + Π d - Π Πᵀ h, d + Πᵀ h - Πᵀ Π d)`.
* `pivot_facts`: `Π Πᵀ Π = Π` and `Πᵀ Π Πᵀ = Πᵀ`.
* `kMat_facts`: if `Π M Π = Π`, then `Π K = Π Πᵀ - Π M`, `K Π = M Π - Πᵀ Π` and
  `K Π Πᵀ = M Π Πᵀ - Πᵀ`.
* `exchange_factor`: the factorization of `D_U`.

Nested frames: for idempotents `A ≤ B` (`A B = B A = A`), `D_A ∘ D_B = D_{B - A}`
(`exchange_comp`), `B - A` is idempotent, and over `ℚ` its rank is `rank B - rank A`
(`rank_sub_add`), since the rank of an idempotent is its trace (`rank_eq_trace`). The Kronecker
product of idempotents is idempotent with the product rank (`rank_kronecker`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Exchange

open Matrix Finset
open scoped Kronecker
open IntegerMultBounds.Swap.Shear (State Op run pivotMatrix)
open IntegerMultBounds.Swap.PivotRank (pivotMatrix_apply)

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The partial swap on an idempotent `U`. -/
def exchange (U : Matrix ι ι R) (s : State ι R) : State ι R :=
  ((1 - U) *ᵥ s.1 + U *ᵥ s.2, U *ᵥ s.1 + (1 - U) *ᵥ s.2)

/-- A transformation within each field: `h ← A h`, `d ← B d`. -/
def transform (A B : Matrix ι ι R) (s : State ι R) : State ι R := (A *ᵥ s.1, B *ᵥ s.2)

/-- The cross shear `d ← d + K h`. -/
def cross (K : Matrix ι ι R) (s : State ι R) : State ι R := (s.1, s.2 + K *ᵥ s.1)

/-- The interchanges of a pivot list, one per pivot. -/
def swaps (L : List (ι × ι)) : List (Op ι R) := L.map fun p => .interchange p.1 p.2

/-- The indicator of a set of coordinates, as a diagonal matrix. -/
def indicator (l : List ι) : Matrix ι ι R := diagonal fun k => if k ∈ l then 1 else 0

/-! ### Pivot matrices -/

section Pivots

variable (L : List (ι × ι))

omit [Fintype ι] in
lemma pivot_row_zero {i : ι} (hi : i ∉ L.map Prod.fst) (hL : L.Nodup) (j : ι) :
    (pivotMatrix L : Matrix ι ι R) i j = 0 := by
  rw [pivotMatrix_apply L hL, ite_eq_right]
  intro h
  exact hi (List.mem_map.mpr ⟨(i, j), h, rfl⟩)

omit [Fintype ι] in
lemma pivot_col_zero {j : ι} (hj : j ∉ L.map Prod.snd) (hL : L.Nodup) (i : ι) :
    (pivotMatrix L : Matrix ι ι R) i j = 0 := by
  rw [pivotMatrix_apply L hL, ite_eq_right]
  intro h
  exact hj (List.mem_map.mpr ⟨(i, j), h, rfl⟩)

omit [Fintype ι] in
lemma pivotMatrix_swap (hL : L.Nodup) :
    (pivotMatrix (L.map Prod.swap) : Matrix ι ι R) = (pivotMatrix L)ᵀ := by
  have hL' : (L.map Prod.swap).Nodup := hL.map Prod.swap_injective
  ext i j
  rw [transpose_apply, pivotMatrix_apply _ hL', pivotMatrix_apply _ hL]
  congr 1
  apply propext
  constructor
  · intro h
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
    have : p = (j, i) := by
      rw [← Prod.swap_swap p, hpe]; rfl
    exact this ▸ hp
  · intro h
    exact List.mem_map.mpr ⟨(j, i), h, rfl⟩

/-- `Πᵀ Π` is the indicator of the pivot columns. -/
theorem transpose_mul_pivot (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup) :
    (pivotMatrix L : Matrix ι ι R)ᵀ * pivotMatrix L = indicator (L.map Prod.snd) := by
  have hL : L.Nodup := h₁.of_map _
  ext j j'
  rw [mul_apply, indicator]
  simp only [transpose_apply, pivotMatrix_apply L hL]
  by_cases hjj : j = j'
  · subst hjj
    rw [diagonal_apply_eq]
    by_cases hj : j ∈ L.map Prod.snd
    · rw [ite_eq_left hj]
      obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hj
      have hpe : (p.1, j) = p := Prod.ext rfl hpj.symm
      rw [sum_eq_single p.1]
      · rw [hpe, ite_eq_left hp, mul_one]
      · intro i _ hi
        rw [ite_eq_right, zero_mul]
        intro hij
        have := List.inj_on_of_nodup_map h₂ hij hp (by rw [← hpj])
        exact hi (congrArg Prod.fst this)
      · intro h
        exact absurd (mem_univ _) h
    · rw [ite_eq_right hj]
      apply sum_eq_zero
      intro i _
      rw [ite_eq_right, zero_mul]
      intro hij
      exact hj (List.mem_map.mpr ⟨(i, j), hij, rfl⟩)
  · rw [diagonal_apply_ne _ hjj]
    apply sum_eq_zero
    intro i _
    by_cases h1 : (i, j) ∈ L
    · by_cases h2 : (i, j') ∈ L
      · exfalso
        have := List.inj_on_of_nodup_map h₁ h1 h2 rfl
        exact hjj (congrArg Prod.snd this)
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- `Π Πᵀ` is the indicator of the pivot rows. -/
theorem pivot_mul_transpose (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup) :
    (pivotMatrix L : Matrix ι ι R) * (pivotMatrix L)ᵀ = indicator (L.map Prod.fst) := by
  have hL : L.Nodup := h₁.of_map _
  have h₁' : ((L.map Prod.swap).map Prod.fst).Nodup := by
    rw [List.map_map]; exact h₂
  have h₂' : ((L.map Prod.swap).map Prod.snd).Nodup := by
    rw [List.map_map]; exact h₁
  have h := transpose_mul_pivot (R := R) (L.map Prod.swap) h₁' h₂'
  rw [pivotMatrix_swap L hL, transpose_transpose, List.map_map] at h
  exact h

lemma indicator_mul_pivot (hL : L.Nodup) :
    indicator (L.map Prod.fst) * (pivotMatrix L : Matrix ι ι R) = pivotMatrix L := by
  ext i j
  rw [indicator, diagonal_mul]
  by_cases hi : i ∈ L.map Prod.fst
  · rw [ite_eq_left hi, one_mul]
  · rw [ite_eq_right hi, zero_mul, pivot_row_zero L hi hL]

/-- The two pivot identities. -/
theorem pivot_facts (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup) :
    (pivotMatrix L : Matrix ι ι R) * (pivotMatrix L)ᵀ * pivotMatrix L = pivotMatrix L ∧
      (pivotMatrix L : Matrix ι ι R)ᵀ * pivotMatrix L * (pivotMatrix L)ᵀ = (pivotMatrix L)ᵀ := by
  have hL : L.Nodup := h₁.of_map _
  have h := indicator_mul_pivot (R := R) L hL
  rw [← pivot_mul_transpose L h₁ h₂] at h
  refine ⟨h, ?_⟩
  have h' := congrArg transpose h
  rw [transpose_mul, transpose_mul, transpose_transpose] at h'
  rw [Matrix.mul_assoc]
  exact h'

end Pivots

/-! ### The interchanges of a pivot list -/

lemma mulVec_update_col {A : Matrix ι ι R} {j : ι} (hA : ∀ k, A k j = 0) (v : ι → R) (x : R) :
    A *ᵥ Function.update v j x = A *ᵥ v := by
  funext k
  exact IntegerMultBounds.Swap.Shear.mulVec_update_of_zero A (hA k) v x

lemma mulVec_indicator (l : List ι) (v : ι → R) (k : ι) :
    (indicator l *ᵥ v) k = if k ∈ l then v k else 0 := by
  rw [indicator, mulVec_diagonal]
  split_ifs <;> simp

/-- The interchanges of a pivot list with distinct rows and columns. -/
theorem swaps_run (L : List (ι × ι)) (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup)
    (s : State ι R) :
    run (swaps L) s = (s.1 + pivotMatrix L *ᵥ s.2 - indicator (L.map Prod.fst) *ᵥ s.1,
      s.2 + (pivotMatrix L)ᵀ *ᵥ s.1 - indicator (L.map Prod.snd) *ᵥ s.2) := by
  induction L generalizing s with
  | nil =>
    have h0 : (indicator ([] : List ι) : Matrix ι ι R) = 0 := by
      ext i j; simp [indicator, diagonal]
    simp [swaps, pivotMatrix, h0]
  | cons p rest ih =>
    obtain ⟨i, j⟩ := p
    rw [List.map_cons, List.nodup_cons] at h₁ h₂
    have hr : rest.Nodup := h₁.2.of_map _
    have hi : ∀ k, (pivotMatrix rest : Matrix ι ι R) i k = 0 := pivot_row_zero rest h₁.1 hr
    have hj : ∀ k, (pivotMatrix rest : Matrix ι ι R) k j = 0 := fun k => pivot_col_zero rest h₂.1 hr k
    change run (swaps rest) (Op.run (.interchange i j) s) = _
    rw [ih h₁.2 h₂.2]
    obtain ⟨h, d⟩ := s
    simp only [Op.run]
    have hP : (pivotMatrix ((i, j) :: rest) : Matrix ι ι R) = single i j 1 + pivotMatrix rest := rfl
    rw [hP, mulVec_update_col hj, transpose_add, transpose_single,
      mulVec_update_col (A := (pivotMatrix rest)ᵀ) (fun k => hi k)]
    refine Prod.ext ?_ ?_
    · funext k
      simp only [Pi.add_apply, Pi.sub_apply, add_mulVec, single_mulVec, mulVec_indicator,
        List.map_cons, List.mem_cons]
      by_cases hk : k = i
      · subst hk
        have h0 : (pivotMatrix rest *ᵥ d) k = 0 := by
          simp only [mulVec, dotProduct, hi, zero_mul, sum_const_zero]
        simp [h₁.1, h0]
      · simp [hk]
    · funext k
      simp only [Pi.add_apply, Pi.sub_apply, add_mulVec, single_mulVec, mulVec_indicator,
        List.map_cons, List.mem_cons]
      by_cases hk : k = j
      · subst hk
        have h0 : ((pivotMatrix rest)ᵀ *ᵥ h) k = 0 := by
          simp only [mulVec, dotProduct, transpose_apply, hj, zero_mul, sum_const_zero]
        simp [h₂.1, h0]
      · simp [hk]

/-! ### The correction shear -/

/-- The correction `K = M Π Πᵀ - Πᵀ Π M + Πᵀ Π M Π Πᵀ - Πᵀ`. -/
def kMat (P M : Matrix ι ι R) : Matrix ι ι R :=
  M * (P * Pᵀ) - Pᵀ * P * M + Pᵀ * P * M * (P * Pᵀ) - Pᵀ

omit [DecidableEq ι] in
/-- The three identities of the correction, from `Π Πᵀ Π = Π`, `Πᵀ Π Πᵀ = Πᵀ` and `Π M Π = Π`. -/
theorem kMat_facts (P M : Matrix ι ι R) (F1 : P * Pᵀ * P = P) (F2 : Pᵀ * P * Pᵀ = Pᵀ)
    (F3 : P * M * P = P) :
    P * kMat P M = P * Pᵀ - P * M ∧ kMat P M * P = M * P - Pᵀ * P ∧
      kMat P M * (P * Pᵀ) = M * (P * Pᵀ) - Pᵀ := by
  have G1 : P * (Pᵀ * P) = P := by rw [← Matrix.mul_assoc, F1]
  have G1' : ∀ Z : Matrix ι ι R, P * (Pᵀ * (P * Z)) = P * Z := by
    intro Z; rw [← Matrix.mul_assoc Pᵀ P Z, ← Matrix.mul_assoc P (Pᵀ * P) Z, G1]
  have G2 : Pᵀ * (P * Pᵀ) = Pᵀ := by rw [← Matrix.mul_assoc, F2]
  have G2' : ∀ Z : Matrix ι ι R, Pᵀ * (P * (Pᵀ * Z)) = Pᵀ * Z := by
    intro Z; rw [← Matrix.mul_assoc P Pᵀ Z, ← Matrix.mul_assoc Pᵀ (P * Pᵀ) Z, G2]
  have G3 : P * (M * P) = P := by rw [← Matrix.mul_assoc, F3]
  have G3' : ∀ Z : Matrix ι ι R, P * (M * (P * Z)) = P * Z := by
    intro Z; rw [← Matrix.mul_assoc M P Z, ← Matrix.mul_assoc P (M * P) Z, G3]
  refine ⟨?_, ?_, ?_⟩
  · simp only [kMat, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc, G1', G3']
    abel
  · simp only [kMat, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, G1, G3, G3']
    abel
  · simp only [kMat, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, G2, G3']
    abel

/-! ### The factorization of the exchange -/

/-- **The exchange program.** For `U = E₁ Π E₂` idempotent, with `E₁`, `E₂` invertible, the
exchange `D_U` is the transformation by `E₁⁻¹` and `E₂`, the shear by `K`, the interchanges of the
pivots, the shear by `-K`, and the transformation by `E₁` and `E₂⁻¹`. -/
theorem exchange_factor (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup)
    (hinv₁ : E₁ * E₁' = 1) (hinv₁' : E₁' * E₁ = 1) (hinv₂ : E₂ * E₂' = 1) (hinv₂' : E₂' * E₂ = 1)
    (U : Matrix ι ι R) (hU : U = E₁ * pivotMatrix L * E₂) (hidem : U * U = U) (s : State ι R) :
    transform E₁ E₂' (cross (-kMat (pivotMatrix L) (E₂ * E₁))
      (run (swaps L) (cross (kMat (pivotMatrix L) (E₂ * E₁)) (transform E₁' E₂ s)))) =
      exchange U s := by
  set P : Matrix ι ι R := pivotMatrix L with hPdef
  set M : Matrix ι ι R := E₂ * E₁ with hM
  set K := kMat P M with hK
  obtain ⟨F1, F2⟩ := pivot_facts (R := R) L h₁ h₂
  rw [← hPdef] at F1 F2
  have F3 : P * M * P = P := by
    have e := congrArg (fun X => E₁' * X * E₂') hidem
    simp only [hU] at e
    have e1 : E₁' * (E₁ * P * E₂ * (E₁ * P * E₂)) * E₂' = P * M * P := by
      simp only [hM, ← Matrix.mul_assoc, hinv₁', Matrix.one_mul]
      rw [Matrix.mul_assoc _ E₂ E₂', hinv₂, Matrix.mul_one]
    have e2 : E₁' * (E₁ * P * E₂) * E₂' = P := by
      simp only [← Matrix.mul_assoc, hinv₁', Matrix.one_mul]
      rw [Matrix.mul_assoc _ E₂ E₂', hinv₂, Matrix.mul_one]
    exact e1.symm.trans (e.trans e2)
  obtain ⟨K1, K2, K3⟩ := kMat_facts P M F1 F2 F3
  rw [← hK] at K1 K2 K3
  have hrow : indicator (L.map Prod.fst) = P * Pᵀ := (pivot_mul_transpose L h₁ h₂).symm
  have hcol : indicator (L.map Prod.snd) = Pᵀ * P := (transpose_mul_pivot L h₁ h₂).symm
  obtain ⟨h, d⟩ := s
  simp only [transform, cross]
  rw [swaps_run L h₁ h₂, ← hPdef, hrow, hcol]
  simp only [exchange]
  -- the coefficients of `h` and `d` in both fields
  have A1 : E₁ * E₁' - E₁ * (P * Pᵀ) * E₁' + E₁ * (P * K) * E₁' = 1 - U := by
    rw [K1, hU, hM]
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hinv₁]
    rw [Matrix.mul_assoc _ E₁ E₁', hinv₁, Matrix.mul_one]
    abel
  have B1 : E₁ * P * E₂ = U := hU.symm
  have A2 : E₂' * (Pᵀ - Pᵀ * P * K - K * P * K + K * (P * Pᵀ)) * E₁' = U := by
    have : Pᵀ - Pᵀ * P * K - K * P * K + K * (P * Pᵀ) = M * P * M := by
      rw [K2, K3, Matrix.sub_mul, Matrix.mul_assoc M P K, K1]
      simp only [Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this, hU, hM]
    simp only [← Matrix.mul_assoc, hinv₂', Matrix.one_mul]
    rw [Matrix.mul_assoc _ E₁ E₁', hinv₁, Matrix.mul_one]
  have B2 : E₂' * (1 - Pᵀ * P - K * P) * E₂ = 1 - U := by
    have : 1 - Pᵀ * P - K * P = 1 - M * P := by rw [K2]; abel
    rw [this, hU, hM]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv₂', ← Matrix.mul_assoc,
      Matrix.one_mul]
  refine Prod.ext ?_ ?_
  · rw [← A1, ← B1]
    simp only [mulVec_add, mulVec_sub, add_mulVec, sub_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    abel
  · rw [← B2, ← A2]
    simp only [mulVec_add, mulVec_sub, mulVec_neg, add_mulVec, sub_mulVec, neg_mulVec,
      mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.neg_mul]
    abel

/-! ### Nested frames -/

/-- For `A B = A`, the exchange on `B` followed by the exchange on `A` is the exchange on
`B - A`. -/
theorem exchange_comp (A B : Matrix ι ι R) (hAB : A * B = A) (s : State ι R) :
    exchange A (exchange B s) = exchange (B - A) s := by
  obtain ⟨h, d⟩ := s
  have e1 : (1 - A) * (1 - B) + A * B = 1 - (B - A) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hAB]; abel
  have e2 : (1 - A) * B + A * (1 - B) = B - A := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hAB]; abel
  simp only [exchange, mulVec_add, mulVec_mulVec]
  refine Prod.ext ?_ ?_
  · rw [← e1, ← e2]; simp only [add_mulVec]; abel
  · rw [← e1, ← e2]; simp only [add_mulVec]; abel

omit [DecidableEq ι] in
theorem sub_idempotent (A B : Matrix ι ι R) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = A)
    (hBA : B * A = A) : (B - A) * (B - A) = B - A := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, hA, hB, hAB, hBA]; abel

section Rank

/-- The rank of a rational idempotent is its trace. -/
theorem rank_eq_trace (U : Matrix ι ι ℚ) (hU : U * U = U) : (U.rank : ℚ) = U.trace := by
  have he : IsIdempotentElem (Matrix.toLin' U) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hU]
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ he).trace]
  rfl

/-- **Nested ranks.** For rational idempotents `A ≤ B`, `rank (B - A) + rank A = rank B`. -/
theorem rank_sub_add (A B : Matrix ι ι ℚ) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = A)
    (hBA : B * A = A) : (B - A).rank + A.rank = B.rank := by
  have h := rank_eq_trace (B - A) (sub_idempotent A B hA hB hAB hBA)
  rw [trace_sub, ← rank_eq_trace A hA, ← rank_eq_trace B hB] at h
  exact_mod_cast (show ((B - A).rank : ℚ) + A.rank = B.rank by rw [h]; ring)

/-- The Kronecker product of idempotents is idempotent, with the product rank. -/
theorem rank_kronecker {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℚ)
    (B : Matrix κ κ ℚ) (hA : A * A = A) (hB : B * B = B) :
    A ⊗ₖ B * A ⊗ₖ B = A ⊗ₖ B ∧ (A ⊗ₖ B).rank = A.rank * B.rank := by
  have hK : A ⊗ₖ B * A ⊗ₖ B = A ⊗ₖ B := by
    rw [← Matrix.mul_kronecker_mul, hA, hB]
  refine ⟨hK, ?_⟩
  have h := rank_eq_trace _ hK
  rw [Matrix.trace_kronecker, ← rank_eq_trace A hA, ← rank_eq_trace B hB] at h
  exact_mod_cast h

end Rank

end IntegerMultBounds.MathlibTM2.M8.Exchange
