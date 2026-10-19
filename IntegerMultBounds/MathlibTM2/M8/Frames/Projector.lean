module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Form-orthogonal projectors

For a form `G` and a matrix `B` whose Gram matrix `Bᵀ G B` is invertible,
`proj G B = B (Bᵀ G B)⁻¹ Bᵀ G` is the `G`-orthogonal projector onto the column space of `B`. It
fixes the columns (`proj_mul_self`), satisfies `Bᵀ G · proj G B = Bᵀ G` (`form_mul_proj`), is
idempotent (`proj_idem`) and has rank the number of columns (`proj_rank`). For `B = B' C`, a
column space inside that of `B'`, the projectors nest: `proj G B' · proj G B = proj G B` and
`proj G B · proj G B' = proj G B` (`proj_nest_left`, `proj_nest_right`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Matrix

variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']

/-- The `G`-orthogonal projector onto the column space of `B`. -/
noncomputable def proj (G : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) : Matrix ι ι ℚ :=
  B * (Bᵀ * G * B)⁻¹ * Bᵀ * G

variable {G : Matrix ι ι ℚ} {B : Matrix ι κ ℚ}

theorem proj_mul_self (hB : IsUnit (Bᵀ * G * B).det) : proj G B * B = B := by
  unfold proj
  rw [show B * (Bᵀ * G * B)⁻¹ * Bᵀ * G * B = B * ((Bᵀ * G * B)⁻¹ * (Bᵀ * G * B)) by
    simp only [Matrix.mul_assoc], nonsing_inv_mul _ hB, Matrix.mul_one]

theorem form_mul_proj (hB : IsUnit (Bᵀ * G * B).det) : Bᵀ * G * proj G B = Bᵀ * G := by
  unfold proj
  rw [show Bᵀ * G * (B * (Bᵀ * G * B)⁻¹ * Bᵀ * G) = (Bᵀ * G * B * (Bᵀ * G * B)⁻¹) * (Bᵀ * G) by
    simp only [Matrix.mul_assoc], mul_nonsing_inv _ hB, Matrix.one_mul]

theorem proj_eq_mul : proj G B = B * ((Bᵀ * G * B)⁻¹ * Bᵀ * G) := by
  unfold proj; simp only [Matrix.mul_assoc]

theorem proj_idem (hB : IsUnit (Bᵀ * G * B).det) : proj G B * proj G B = proj G B := by
  calc proj G B * proj G B = (proj G B * B) * ((Bᵀ * G * B)⁻¹ * Bᵀ * G) := by
        conv_lhs => arg 2; rw [proj_eq_mul]
        simp only [Matrix.mul_assoc]
    _ = proj G B := by rw [proj_mul_self hB, ← proj_eq_mul]

/-- The projector has rank the number of columns. -/
theorem proj_rank (hB : IsUnit (Bᵀ * G * B).det) : (proj G B).rank = Fintype.card κ := by
  have hX : ((Bᵀ * G * B)⁻¹ * Bᵀ * G) * B = 1 := by
    rw [show (Bᵀ * G * B)⁻¹ * Bᵀ * G * B = (Bᵀ * G * B)⁻¹ * (Bᵀ * G * B) by
      simp only [Matrix.mul_assoc], nonsing_inv_mul _ hB]
  apply le_antisymm
  · rw [proj_eq_mul]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width B)
  · have h1 : Fintype.card κ = (((Bᵀ * G * B)⁻¹ * Bᵀ * G) * B).rank := by
      rw [hX, rank_one]
    have h2 : B.rank ≤ (proj G B).rank :=
      calc B.rank = (proj G B * B).rank := by rw [proj_mul_self hB]
        _ ≤ (proj G B).rank := rank_mul_le_left _ _
    rw [h1]
    exact (rank_mul_le_right _ _).trans h2

variable {B' : Matrix ι κ' ℚ}

/-- The larger projector fixes the smaller one. -/
theorem proj_nest_left (hB' : IsUnit (B'ᵀ * G * B').det) {C : Matrix κ' κ ℚ} (hC : B = B' * C) :
    proj G B' * proj G B = proj G B := by
  have hfix : proj G B' * B = B := by
    rw [hC, ← Matrix.mul_assoc, proj_mul_self hB']
  rw [proj_eq_mul (B := B), ← Matrix.mul_assoc, hfix]

/-- The smaller projector absorbs the larger one. -/
theorem proj_nest_right (hB' : IsUnit (B'ᵀ * G * B').det) {C : Matrix κ' κ ℚ} (hC : B = B' * C) :
    proj G B * proj G B' = proj G B := by
  have hform : Bᵀ * G * proj G B' = Bᵀ * G := by
    rw [hC, transpose_mul, show Cᵀ * B'ᵀ * G * proj G B' = Cᵀ * (B'ᵀ * G * proj G B') by
      simp only [Matrix.mul_assoc], form_mul_proj hB', Matrix.mul_assoc]
  unfold proj
  rw [show B * (Bᵀ * G * B)⁻¹ * Bᵀ * G * (B' * (B'ᵀ * G * B')⁻¹ * B'ᵀ * G) =
      B * (Bᵀ * G * B)⁻¹ * (Bᵀ * G * proj G B') by unfold proj; simp only [Matrix.mul_assoc],
    hform]
  simp only [Matrix.mul_assoc]

end IntegerMultBounds.MathlibTM2.M8.Frames
