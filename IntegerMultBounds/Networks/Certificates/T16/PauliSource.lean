module

public import IntegerMultBounds.Networks.Certificates.T16.PauliDiagonalAction

/-! Source-format phase polynomial and composition of proved complex realizations. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

theorem doubleLift_product (a b c : ZMod 2) :
    doubleLift (a*b*c) = 2 * bitLift a * bitLift b * bitLift c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem doubleLift_sum (f : Fin 9 → F) :
    doubleLift (∑ i, f i) = ∑ i, doubleLift (f i) := map_sum doubleLift f Finset.univ

/-- Exactly the source's diagonal polynomial, using its literal 0/1 integer lifts. -/
theorem qValue_source (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (x : Geometry.Address) :
    qValue Q alpha x = (∑ i, alpha i * bitLift (x i)) +
      ∑ i, ∑ j, if i < j then 2 * bitLift (Q i j) * bitLift (x i) * bitLift (x j) else 0 := by
  change (∑ i, alpha i * bitLift (x i)) +
      doubleLift (∑ i, ∑ j, upper Q i j * x i * x j) = _
  rw [doubleLift_sum]
  apply congrArg (fun t : ZMod 4 => (∑ i, alpha i * bitLift (x i)) + t)
  apply Finset.sum_congr rfl
  intro i _
  rw [doubleLift_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · simp only [upper, h, ite_true]
    exact doubleLift_product _ _ _
  · simp [upper, h]

/-- A genuine operator/label realization with a proved binary projection.
The label map includes its full Z/4 phase; this is not tableau completeness. -/
structure Realization where
  scalar : State ≃ₗ[ℂ] State
  label : Label → Label
  binary : PhaseAddress ≃ₗ[F] PhaseAddress
  projects : ∀ p, (label p).binary = binary p.binary
  conjugates : ∀ p f, scalar (operator p (scalar.symm f)) = operator (label p) f

noncomputable def Realization.identity : Realization where
  scalar := LinearEquiv.refl ℂ State
  label := id
  binary := LinearEquiv.refl F PhaseAddress
  projects _ := rfl
  conjugates _ _ := rfl

/-- Apply the first realization and then the second, matching source `then`. -/
noncomputable def Realization.then (a b : Realization) : Realization where
  scalar := a.scalar.trans b.scalar
  label := b.label ∘ a.label
  binary := a.binary.trans b.binary
  projects p := by
    change (b.label (a.label p)).binary = b.binary (a.binary p.binary)
    rw [b.projects, a.projects]
  conjugates p f := by
    change b.scalar (a.scalar (operator p (a.scalar.symm (b.scalar.symm f)))) =
      operator (b.label (a.label p)) f
    rw [a.conjugates, b.conjugates]

noncomputable def permutationRealization (G : Geometry.Address ≃ₗ[F] Geometry.Address) : Realization where
  scalar := permutation G
  label := permuteLabel G
  binary := Tableau.perm G
  projects := permuteLabel_binary G
  conjugates := permutation_conjugates G

noncomputable def cRealization (q : Geometry.Address) : Realization where
  scalar := cGate q
  label := cLabel q
  binary := cBinary q
  projects := cLabel_binary q
  conjugates := cGate_conjugates q

noncomputable def diagonalRealization (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2*alpha i = doubleLift (Q i i)) : Realization where
  scalar := diagonalGate Q alpha
  label := diagonalLabel Q alpha
  binary := Tableau.diagonal Q.mulVecLin
  projects := diagonalLabel_binary Q alpha
  conjugates := diagonalGate_conjugates Q alpha hQ ha

/-- Any finite word of proved realizations remains exact, including all accumulated phases. -/
noncomputable def realizeWord : List Realization → Realization
  | [] => Realization.identity
  | g :: gs => g.then (realizeWord gs)

end IntegerMultBounds.Networks.Certificates.T16.Pauli
