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

theorem cInverseLabel_binary (q : Geometry.Address) (p : Label) :
    (cInverseLabel q p).binary = cBinary q p.binary := rfl

def xGenerator (i : Fin 9) : Label := ⟨Pi.single i 1,0,0⟩
def zGenerator (i : Fin 9) : Label := ⟨0,Pi.single i 1,0⟩

theorem cLabel_xGenerator (q : Geometry.Address) (i : Fin 9) :
    cLabel q (xGenerator i) = xGenerator i := by
  simp [cLabel, xGenerator]

theorem cLabel_zGenerator (q : Geometry.Address) (i : Fin 9) :
    cLabel q (zGenerator i) = ⟨q i • q, Pi.single i 1, -bitLift (q i)⟩ := by
  simp [cLabel, zGenerator, Tableau.dot, Labels.binary, Labels.form_single]

theorem cInverseLabel_zGenerator (q : Geometry.Address) (i : Fin 9) :
    cInverseLabel q (zGenerator i) = ⟨q i • q, Pi.single i 1, bitLift (q i)⟩ := by
  simp [cInverseLabel, zGenerator, Tableau.dot, Labels.binary, Labels.form_single]

/-- The source's stored forward exponent is exactly 3 on affected Z generators. -/
theorem cLabel_zGenerator_one (q : Geometry.Address) (i : Fin 9) (h : q i = 1) :
    cLabel q (zGenerator i) = ⟨q,Pi.single i 1,3⟩ := by
  rw [cLabel_zGenerator, h]
  simp only [one_smul, bitLift_one]
  rfl

theorem cLabel_zGenerator_zero (q : Geometry.Address) (i : Fin 9) (h : q i = 0) :
    cLabel q (zGenerator i) = zGenerator i := by
  rw [cLabel_zGenerator, h]
  simp [zGenerator]

theorem permuteLabel_xGenerator (G : Geometry.Address ≃ₗ[F] Geometry.Address) (i : Fin 9) :
    permuteLabel G (xGenerator i) = ⟨G (Pi.single i 1),0,0⟩ := by
  simp [permuteLabel, xGenerator]

theorem permuteLabel_zGenerator (G : Geometry.Address ≃ₗ[F] Geometry.Address) (i : Fin 9) :
    permuteLabel G (zGenerator i) = ⟨0,(Tableau.transpose G).symm (Pi.single i 1),0⟩ := by
  simp [permuteLabel, zGenerator]

end IntegerMultBounds.Networks.Certificates.T16.Pauli
