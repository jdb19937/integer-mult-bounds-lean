module

public import IntegerMultBounds.Networks.TripleNeighborPermutation
public import IntegerMultBounds.Networks.GlobalLabelsNondegenerate
public import IntegerMultBounds.Networks.ProjectionTrace

/-! The actual rational tensor-label join for reuse of stage-one scratch at
stage three. The selected neighbor permutation proves nesting in the concrete
right-associated cube. This is a label/rank lemma, not a reused schedule. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Shared50ReuseLabels

open scoped TensorProduct
open Module NeighborCounts TensorSubspace

noncomputable section

abbrev Factor := Fin 50 → ℚ
abbrev Ambient := StageLabels.Ambient ℚ Factor
abbrev D := Labels.rational 50
abbrev vector (T : Triple 50) : Factor := Labels.indicator T.val
abbrev pi := TripleNeighborPermutation.permutation50
abbrev pairForm := TensorSubspace.form D D
abbrev cubeForm := TensorSubspace.form D pairForm

theorem factor_symm : D.IsSymm := ⟨Labels.form_symm (1 / 9)⟩
theorem factor_nondegenerate : D.Nondegenerate := Labels.rational_nondegenerate (by decide)
theorem pair_symm : pairForm.IsSymm := LinearMap.BilinForm.isSymm_iff.mpr
  ((LinearMap.BilinForm.isSymm_iff.mp factor_symm).tmul (LinearMap.BilinForm.isSymm_iff.mp factor_symm))
theorem pair_nondegenerate : pairForm.Nondegenerate :=
  Labels.tmul_nondegenerate _ _ factor_nondegenerate factor_nondegenerate
theorem cube_symm : cubeForm.IsSymm := LinearMap.BilinForm.isSymm_iff.mpr
  ((LinearMap.BilinForm.isSymm_iff.mp factor_symm).tmul (LinearMap.BilinForm.isSymm_iff.mp pair_symm))
theorem cube_nondegenerate : cubeForm.Nondegenerate :=
  Labels.tmul_nondegenerate _ _ factor_nondegenerate pair_nondegenerate

theorem vector_norm (T : Triple 50) : D (vector T) (vector T) ≠ 0 := by
  rw [Labels.rational_self T.val T.property]
  norm_num

theorem pair_vector_norm (S T : Triple 50) :
    pairForm (vector S ⊗ₜ[ℚ] vector T) (vector S ⊗ₜ[ℚ] vector T) ≠ 0 := by
  simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using
    mul_ne_zero (vector_norm T) (vector_norm S)

/-- Last stage-one scratch label for fixed future triples `(A,B)`. -/
def tail (A B : Triple 50) : Submodule ℚ Ambient :=
  space (⊤ : Submodule ℚ Factor) (space (ℚ ∙ vector A) (ℚ ∙ vector B))

/-- First stage-three scratch label for fixed earlier triples `(B,pi(A))`.
The associator places the two-factor complement in the common cube ambient. -/
def head (A B : Triple 50) : Submodule ℚ Ambient :=
  (space (pairForm.orthogonal (ℚ ∙ (vector B ⊗ₜ[ℚ] vector (pi A))))
    (⊤ : Submodule ℚ Factor)).map StageLabels.secondEquiv.toLinearMap

/-- These are the existing stage-one full scratch labels, including their
actual future tensor lift and empty-prefix coordinate identification. -/
theorem tail_boundary (A B : Triple 50) :
    GlobalLabels.firstLabel vector (A,B)
      (StageLabels.firstGeometry D factor_symm factor_nondegenerate).full = tail A B := by
  change (space (space (⊤ : Submodule ℚ ℚ) (⊤ : Submodule ℚ Factor))
    (ℚ ∙ (vector A ⊗ₜ[ℚ] vector B))).map StageLabels.firstEquiv.toLinearMap = _
  rw [StageLabels.first_space, ← StageLabels.space_lines]
  rfl

/-- The reuse head is the existing stage-three common scratch label, not an
assumed annotation for a replacement schedule. -/
theorem head_boundary (A B : Triple 50) :
    GlobalLabels.thirdLabel (B,pi A)
      (StageLabels.thirdGeometry D factor_symm factor_nondegenerate
        (vector B) (vector (pi A)) (vector_norm B) (vector_norm (pi A))).common = head A B := by
  change (space (space (pairForm.orthogonal (ℚ ∙ (vector B ⊗ₜ[ℚ] vector (pi A))))
    (⊤ : Submodule ℚ Factor)) (ℚ ∙ (1 : ℚ))).map StageLabels.thirdEquiv.toLinearMap = _
  rw [StageLabels.scalar_line_one, StageLabels.third_space]
  rfl

/-- The Hall-selected triple permutation supplies the required rational
orthogonality, using the actual intersection-one indicator pairing. -/
theorem neighbors_orthogonal (A : Triple 50) : D (vector A) (vector (pi A)) = 0 :=
  Labels.rational_neighbors A.val (pi A).val A.property (pi A).property
    (TripleNeighborPermutation.permutation50_intersection A)

/-- The join is nested in the actual tensor coordinates: the second factor
of the old tail is orthogonal to the second factor of the new prefix line. -/
theorem tail_le_head (A B : Triple 50) : tail A B ≤ head A B := by
  have hl : (ℚ ∙ vector A) ≤ D.orthogonal (ℚ ∙ vector (pi A)) :=
    (StageLabels.firstGeometry D factor_symm factor_nondegenerate).neighbor_line
      (vector A) (vector (pi A)) (neighbors_orthogonal A)
  have hp : space (⊤ : Submodule ℚ Factor) (ℚ ∙ vector A) ≤
      pairForm.orthogonal (ℚ ∙ (vector B ⊗ₜ[ℚ] vector (pi A))) := by
    rw [← StageLabels.space_lines]
    exact TensorSubspace.orthogonal_right D D ⊤ (ℚ ∙ vector B) hl
  have hh := Submodule.map_mono (f := StageLabels.secondEquiv.toLinearMap)
    (TensorSubspace.mono hp (show (ℚ ∙ vector B) ≤ ⊤ from le_top))
  simpa only [StageLabels.secondEquiv, StageLabels.space_assoc, tail, head] using hh

end

end IntegerMultBounds.Networks.Shared50ReuseLabels
