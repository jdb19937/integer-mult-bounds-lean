module

public import IntegerMultBounds.Networks.Certificates.T16.PauliC

/-! Explicit phase-bearing generator interfaces and their binary projections. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

noncomputable def permuteInverseLabel (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (p : Label) : Label := ⟨G.symm p.x, Tableau.transpose G p.z, p.phase⟩

theorem permuteLabel_inverse (G : Geometry.Address ≃ₗ[F] Geometry.Address) (p : Label) :
    permuteLabel G (permuteInverseLabel G p) = p := by
  cases p
  simp [permuteLabel, permuteInverseLabel]

theorem permutation_inverse_conjugates (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (p : Label) (f : State) : (permutation G).symm (operator p (permutation G f)) =
      operator (permuteInverseLabel G p) f := by
  apply (permutation G).injective
  rw [LinearEquiv.apply_symm_apply, permutation_intertwines, permuteLabel_inverse]

/-- Binary rank-one shear for the source's arbitrary-direction C gate. -/
def cBinary (q : Geometry.Address) : PhaseAddress ≃ₗ[F] PhaseAddress :=
  let R := (Tableau.dot q).smulRight q
  { toFun p := (p.1 + R p.2,p.2)
    invFun p := (p.1 - R p.2,p.2)
    left_inv p := by ext <;> simp
    right_inv p := by ext <;> simp
    map_add' p u := by ext <;> simp [add_comm, add_left_comm, add_assoc]
    map_smul' c p := by ext <;> simp [smul_add] }

theorem cLabel_binary (q : Geometry.Address) (p : Label) :
    (cLabel q p).binary = cBinary q p.binary := rfl

def xGenerator (i : Fin 9) : Label := ⟨Pi.single i 1,0,0⟩
def zGenerator (i : Fin 9) : Label := ⟨0,Pi.single i 1,0⟩

end IntegerMultBounds.Networks.Certificates.T16.Pauli
