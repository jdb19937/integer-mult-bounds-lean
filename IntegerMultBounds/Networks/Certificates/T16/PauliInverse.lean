module

public import IntegerMultBounds.Networks.Certificates.T16.PauliSource

/-! Inverse primitive realizations and an explicit global-phase operator. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

noncomputable def permutationInverseRealization
    (G : Geometry.Address ≃ₗ[F] Geometry.Address) : Realization where
  scalar := (permutation G).symm
  label := permuteInverseLabel G
  binary := (Tableau.perm G).symm
  projects _ := rfl
  conjugates := permutation_inverse_conjugates G

noncomputable def diagonalInverseRealization (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i)) : Realization where
  scalar := (diagonalGate Q alpha).symm
  label := diagonalInverseLabel Q alpha
  binary := Tableau.diagonal Q.mulVecLin
  projects _ := rfl
  conjugates := diagonalGate_inverse_conjugates Q alpha hQ ha

end IntegerMultBounds.Networks.Certificates.T16.Pauli
