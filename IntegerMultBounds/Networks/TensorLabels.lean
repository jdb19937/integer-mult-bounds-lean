module

public import IntegerMultBounds.Networks.Labels
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Tensor label spaces for the three-coordinate motifs. Nondegeneracy is
proved from the Kronecker matrix of the tensor form, over either label field.
These are actual tensor spaces, not an assumed dimension or rank interface. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Labels

open scoped TensorProduct Kronecker
open Module

section Tensor
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]

/-- Tensoring finite nondegenerate forms preserves nondegeneracy, including
over characteristic two; no positive-definiteness assumption is used. -/
theorem tmul_nondegenerate (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) : (B.tmul C).Nondegenerate := by
  classical
  let b := Module.finBasis K E
  let c := Module.finBasis K F
  have hm : LinearMap.BilinForm.toMatrix (b.tensorProduct c) (B.tmul C) =
      (LinearMap.BilinForm.toMatrix b B) ⊗ₖ (LinearMap.BilinForm.toMatrix c C) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Module.Basis.tensorProduct_apply',
      LinearMap.BilinForm.tmul, smul_eq_mul, mul_comm]
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (B.tmul C) (b.tensorProduct c)
  rw [hm, Matrix.det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB))
    (pow_ne_zero _ ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp hC))

end Tensor

abbrev Cube (K : Type*) [CommRing K] (h : ℕ) :=
  (Fin h → K) ⊗[K] ((Fin h → K) ⊗[K] (Fin h → K))

def cubeForm {K : Type*} [CommRing K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) : LinearMap.BilinForm K (Cube K h) :=
  B.tmul (B.tmul B)

theorem cube_nondegenerate {K : Type*} [Field K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) (hB : B.Nondegenerate) :
    (cubeForm B).Nondegenerate := tmul_nondegenerate B _ hB (tmul_nondegenerate B B hB hB)

theorem cube_symm {K : Type*} [CommRing K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) (hs : B.IsSymm) : (cubeForm B).IsSymm := by
  have hs' := LinearMap.BilinForm.isSymm_iff.mp hs
  exact LinearMap.BilinForm.isSymm_iff.mpr (hs'.tmul (hs'.tmul hs'))

end IntegerMultBounds.Networks.Labels
