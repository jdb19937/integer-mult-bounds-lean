module

public import IntegerMultBounds.Networks.Certificates.T16.PauliGenerators
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Source diagonal quadratic phases, with their exact polarization over Z/4. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

abbrev BinaryMatrix := Matrix (Fin 9) (Fin 9) F

def upper (Q : BinaryMatrix) (i j : Fin 9) : F := if i < j then Q i j else 0

def quadraticPart (H : BinaryMatrix) (x : Geometry.Address) : F :=
  ∑ i, ∑ j, H i j * x i * x j

def crossPart (H : BinaryMatrix) (x y : Geometry.Address) : F :=
  ∑ i, ∑ j, H i j * (x i * y j + y i * x j)

/-- Exact source polynomial: diagonal Z/4 coefficients plus twice the upper quadratic part. -/
def qValue (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (x : Geometry.Address) : ZMod 4 :=
  (∑ i, alpha i * bitLift (x i)) + doubleLift (quadraticPart (upper Q) x)

theorem quadraticPart_add (H : BinaryMatrix) (x y : Geometry.Address) :
    quadraticPart H (x+y) = quadraticPart H x + quadraticPart H y + crossPart H x y := by
  have hterm (i j : Fin 9) : H i j * (x i + y i) * (x j + y j) =
      H i j * x i * x j + H i j * y i * y j + H i j * (x i * y j + y i * x j) := by ring
  simp only [quadraticPart, crossPart, Pi.add_apply, hterm, Finset.sum_add_distrib]

theorem scalar_phase_polar (a : ZMod 4) (d x y : ZMod 2)
    (h : 2*a = doubleLift d) :
    a * bitLift (x+y) = a * bitLift x + a * bitLift y + doubleLift (d*x*y) := by
  fin_cases a <;> fin_cases d <;> fin_cases x <;> fin_cases y <;> revert h <;> decide

theorem linearPhase_polar (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (h : ∀ i, 2*alpha i = doubleLift (Q i i)) (x y : Geometry.Address) :
    (∑ i, alpha i * bitLift ((x+y) i)) =
      (∑ i, alpha i * bitLift (x i)) + (∑ i, alpha i * bitLift (y i)) +
        doubleLift (∑ i, Q i i * x i * y i) := by
  simp only [Pi.add_apply, scalar_phase_polar _ _ _ _ (h _), Finset.sum_add_distrib, map_sum]

/-- Symmetry reconstructs the full bilinear matrix from diagonal and upper terms. -/
theorem matrix_polar (Q : BinaryMatrix) (hQ : ∀ i j, Q i j = Q j i)
    (x y : Geometry.Address) :
    (∑ i, Q i i * x i * y i) + crossPart (upper Q) x y =
      Tableau.dot x (Q.mulVecLin y) := by
  have hentry (i j : Fin 9) : Q i j * x i * y j =
      (if i = j then Q i i * x i * y i else 0) +
        upper Q i j * x i * y j + upper Q j i * x i * y j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [upper, hij, ne_of_lt hij, not_lt_of_gt hij]
    · subst j; simp [upper]
    · simp [upper, hij, ne_of_gt hij, not_lt_of_gt hij, hQ i j]
  have htranspose : (∑ i, ∑ j, upper Q j i * x i * y j) =
      ∑ i, ∑ j, upper Q i j * y i * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Tableau.dot, Labels.binary, Labels.form_apply, zero_mul,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hcomm (i j : Fin 9) : x i * (Q i j * y j) = Q i j * x i * y j := by ring
  simp_rw [hcomm]
  have hsum : (∑ i, ∑ j, Q i j * x i * y j) =
      ∑ i, ∑ j, ((if i = j then Q i i * x i * y i else 0) +
        upper Q i j * x i * y j + upper Q j i * x i * y j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hentry i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hdiag : (∑ i, ∑ j : Fin 9, if i = j then Q i i * x i * y i else 0) =
      ∑ i, Q i i * x i * y i := by simp
  rw [hdiag, htranspose]
  simp [crossPart, mul_add, Finset.sum_add_distrib, mul_assoc, add_assoc]

theorem qValue_polar (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i))
    (x y : Geometry.Address) :
    qValue Q alpha (x+y) = qValue Q alpha x + qValue Q alpha y +
      doubleLift (Tableau.dot x (Q.mulVecLin y)) := by
  change (∑ i, alpha i * bitLift ((x+y) i)) + doubleLift (quadraticPart (upper Q) (x+y)) =
    ((∑ i, alpha i * bitLift (x i)) + doubleLift (quadraticPart (upper Q) x)) +
    ((∑ i, alpha i * bitLift (y i)) + doubleLift (quadraticPart (upper Q) y)) + _
  rw [linearPhase_polar Q alpha ha, quadraticPart_add (upper Q) x y,
    ← matrix_polar Q hQ x y]
  simp only [map_add]
  ring

/-- Actual complex source D gate, including its original diagonal phases. -/
noncomputable def diagonalGate (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) :
    State ≃ₗ[ℂ] State := phaseDiagonal (qValue Q alpha)

end IntegerMultBounds.Networks.Certificates.T16.Pauli
