module

public import IntegerMultBounds.Networks.Certificates.T16.Pauli

/-! Phase-exact source C-generator conjugation on genuine complex arrays. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

theorem chi_sq (b x : Geometry.Address) : chi b x ^ 2 = 1 := by
  rw [pow_two, ← chi_add, Tableau.address_add_self, chi_zero_right]

theorem operator_multiply (p q : Label) (f : State) :
    operator p (operator q f) = operator (multiply p q) f := by
  ext x
  simp only [operator_apply, multiply, phase_add, phase_doubleLift,
    chi_add_left, chi_add]
  rw [show sign (Tableau.dot p.z q.x) = chi p.z q.x from rfl]
  simp only [add_assoc]
  ring_nf
  rw [chi_sq]
  ring

/-- Source forward C action: each anticommuting Pauli acquires phase -i. -/
def cLabel (q : Geometry.Address) (p : Label) : Label :=
  ⟨p.x + Tableau.dot q p.z • q, p.z,
    p.phase - bitLift (Tableau.dot q p.z)⟩

/-- Source inverse C action: the same binary map, with opposite phase correction. -/
def cInverseLabel (q : Geometry.Address) (p : Label) : Label :=
  ⟨p.x + Tableau.dot q p.z • q, p.z,
    p.phase + bitLift (Tableau.dot q p.z)⟩

theorem cGate_intertwines (q : Geometry.Address) (p : Label) (f : State) :
    cGate q (operator p f) = operator (cLabel q p) (cGate q f) := by
  ext x
  simp only [cGate_apply, operator_apply, cLabel]
  have hd : Tableau.dot q p.z = 0 ∨ Tableau.dot q p.z = 1 := by
    generalize Tableau.dot q p.z = d
    fin_cases d
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc : chi p.z q = sign (Tableau.dot q p.z) := by
    rw [chi, Labels.binary, Labels.form_symm]
    rfl
  rcases hd with hd | hd
  · simp only [hd, bitLift_zero, zero_smul, add_zero, sub_zero]
    simp only [chi_add, hc, hd, sign_zero, mul_one]
    simp only [add_left_comm, add_comm]
    ring
  · simp only [hd, bitLift_one, one_smul, sub_eq_add_neg, phase_add, phase_neg_one]
    simp only [chi_add, hc, hd, sign_one]
    simp only [add_left_comm, add_comm]
    ring_nf
    have ht : (2 : Geometry.Address) = 0 := by ext i; change (2 : ZMod 2) = 0; decide
    simp [ht, Complex.I_sq]
    ring

theorem cGate_conjugates (q : Geometry.Address) (p : Label) (f : State) :
    cGate q (operator p ((cGate q).symm f)) = operator (cLabel q p) f := by
  rw [cGate_intertwines, LinearEquiv.apply_symm_apply]

theorem cLabel_inverse (q : Geometry.Address) (p : Label) :
    cLabel q (cInverseLabel q p) = p := by
  cases p
  simp [cLabel, cInverseLabel, add_assoc, ← add_smul, CharTwo.add_self_eq_zero]

theorem cGate_inverse_conjugates (q : Geometry.Address) (p : Label) (f : State) :
    (cGate q).symm (operator p (cGate q f)) = operator (cInverseLabel q p) f := by
  apply (cGate q).injective
  rw [LinearEquiv.apply_symm_apply, cGate_intertwines, cLabel_inverse]

end IntegerMultBounds.Networks.Certificates.T16.Pauli
