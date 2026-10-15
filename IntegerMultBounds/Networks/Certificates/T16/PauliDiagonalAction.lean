module

public import IntegerMultBounds.Networks.Certificates.T16.PauliDiagonal

/-! Exact complex realization of the source D tableau, including all phases. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

def diagonalLabel (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (p : Label) : Label :=
  ⟨p.x, p.z + Q.mulVecLin p.x, p.phase + qValue Q alpha p.x⟩

def diagonalInverseLabel (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (p : Label) : Label :=
  ⟨p.x, p.z + Q.mulVecLin p.x, p.phase - qValue Q alpha p.x⟩

theorem diagonalGate_intertwines (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i))
    (p : Label) (f : State) : diagonalGate Q alpha (operator p f) =
      operator (diagonalLabel Q alpha p) (diagonalGate Q alpha f) := by
  ext x
  have hp := qValue_polar Q alpha hQ ha (x+p.x) p.x
  have hx : (x+p.x)+p.x = x := by rw [add_assoc, Tableau.address_add_self, add_zero]
  rw [hx] at hp
  change BinaryPhase.phase (qValue Q alpha x) * operator p f x =
    operator (diagonalLabel Q alpha p) (diagonalGate Q alpha f) x
  rw [operator_apply, operator_apply]
  change BinaryPhase.phase (qValue Q alpha x) *
      (BinaryPhase.phase p.phase * chi p.z (x+p.x) * f (x+p.x)) =
    BinaryPhase.phase (p.phase + qValue Q alpha p.x) *
      chi (p.z + Q.mulVecLin p.x) (x+p.x) *
      (BinaryPhase.phase (qValue Q alpha (x+p.x)) * f (x+p.x))
  rw [hp]
  simp only [phase_add, phase_doubleLift, chi_add_left]
  have hc : sign (Tableau.dot (x+p.x) (Q.mulVecLin p.x)) =
      chi (Q.mulVecLin p.x) (x+p.x) := by rw [chi, Tableau.dot_symm]
  rw [hc]
  ring

theorem diagonalGate_conjugates (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i))
    (p : Label) (f : State) :
    diagonalGate Q alpha (operator p ((diagonalGate Q alpha).symm f)) =
      operator (diagonalLabel Q alpha p) f := by
  rw [diagonalGate_intertwines Q alpha hQ ha, LinearEquiv.apply_symm_apply]

theorem diagonalLabel_inverse (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (p : Label) :
    diagonalLabel Q alpha (diagonalInverseLabel Q alpha p) = p := by
  cases p
  simp [diagonalLabel, diagonalInverseLabel, add_assoc, Tableau.address_add_self]

theorem diagonalGate_inverse_conjugates (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i))
    (p : Label) (f : State) :
    (diagonalGate Q alpha).symm (operator p (diagonalGate Q alpha f)) =
      operator (diagonalInverseLabel Q alpha p) f := by
  apply (diagonalGate Q alpha).injective
  rw [LinearEquiv.apply_symm_apply, diagonalGate_intertwines Q alpha hQ ha,
    diagonalLabel_inverse]

theorem diagonalLabel_binary (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (p : Label) :
    (diagonalLabel Q alpha p).binary = Tableau.diagonal Q.mulVecLin p.binary := rfl

theorem qValue_zero (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) : qValue Q alpha 0 = 0 := by
  simp [qValue, quadraticPart]

theorem qValue_single (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (i : Fin 9) :
    qValue Q alpha (Pi.single i 1) = alpha i := by
  have hb (j : Fin 9) : bitLift (if j = i then 1 else 0) =
      (if j = i then 1 else 0 : ZMod 4) := by split <;> rfl
  simp [qValue, quadraticPart, upper, Pi.single_apply, hb]

theorem diagonalLabel_zGenerator (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (i : Fin 9) :
    diagonalLabel Q alpha (zGenerator i) = zGenerator i := by
  simp [diagonalLabel, zGenerator, qValue_zero]

theorem diagonalLabel_xGenerator (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (i : Fin 9) :
    diagonalLabel Q alpha (xGenerator i) = ⟨Pi.single i 1, (fun j => Q i j), alpha i⟩ := by
  have hc : Q.mulVecLin (Pi.single i 1) = fun j => Q i j := by
    ext j
    simp [hQ]
  simp [diagonalLabel, xGenerator, qValue_single, hc]

/-- The source's default alpha is the zero-or-one lift of the diagonal bit. -/
def defaultAlpha (Q : BinaryMatrix) (i : Fin 9) : ZMod 4 := bitLift (Q i i)

theorem defaultAlpha_compatible (Q : BinaryMatrix) (i : Fin 9) :
    2 * defaultAlpha Q i = doubleLift (Q i i) := rfl

/-- The source alpha parity test is exactly the compatibility used above. -/
theorem alpha_compatible_iff (a : ZMod 4) (b : ZMod 2) :
    2*a = doubleLift b ↔ a.val % 2 = b.val := by
  fin_cases a <;> fin_cases b <;> decide

end IntegerMultBounds.Networks.Certificates.T16.Pauli
