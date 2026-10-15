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

noncomputable def cInverseRealization (q : Geometry.Address) : Realization where
  scalar := (cGate q).symm
  label := cInverseLabel q
  binary := cBinary q
  projects := cInverseLabel_binary q
  conjugates := cGate_inverse_conjugates q

noncomputable def diagonalInverseRealization (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i)) : Realization where
  scalar := (diagonalGate Q alpha).symm
  label := diagonalInverseLabel Q alpha
  binary := Tableau.diagonal Q.mulVecLin
  projects _ := rfl
  conjugates := diagonalGate_inverse_conjugates Q alpha hQ ha

/-- A global phase is retained by the scalar operator even though Pauli conjugation cannot see it. -/
noncomputable def globalPhase (q : ZMod 4) : State ≃ₗ[ℂ] State :=
  phaseDiagonal (fun _ => q)

theorem globalPhase_conjugates (q : ZMod 4) (p : Label) (f : State) :
    globalPhase q (operator p ((globalPhase q).symm f)) = operator p f := by
  ext x
  change BinaryPhase.phase q * operator p ((globalPhase q).symm f) x = operator p f x
  rw [operator_apply, operator_apply]
  change BinaryPhase.phase q * (BinaryPhase.phase p.phase * chi p.z (x+p.x) *
    (BinaryPhase.phase (-q) * f (x+p.x))) = _
  calc
    _ = (BinaryPhase.phase (-q) * BinaryPhase.phase q) *
        (BinaryPhase.phase p.phase * chi p.z (x+p.x) * f (x+p.x)) := by ring
    _ = _ := by rw [phase_neg_mul, one_mul]

noncomputable def globalPhaseRealization (q : ZMod 4) : Realization where
  scalar := globalPhase q
  label := id
  binary := LinearEquiv.refl F PhaseAddress
  projects _ := rfl
  conjugates := globalPhase_conjugates q

end IntegerMultBounds.Networks.Certificates.T16.Pauli
