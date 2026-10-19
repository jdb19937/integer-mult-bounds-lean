module

import IntegerMultBounds.Machine.ActivePrefixStageSingletonInverseData
public import IntegerMultBounds.Machine.ActivePrefixStageInverseMachine
public import IntegerMultBounds.Machine.ActivePrefixStageRuntimeProgram
public import IntegerMultBounds.Machine.ActivePrefixStageRuntimeData
import IntegerMultBounds.Machine.ActivePrefixStageDispatchSelected
import Mathlib.Tactic.Positivity.Finset

/-! The complete fixed width-and-direction program executes its own inverse.
Both runtime flags and every private tape are restored on each return. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeData (Packed result cost)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

theorem involutive (d : Inputs s) : Function.Involutive (result d) := by
  intro x
  by_cases h : 1<d.stage.f
  · simp only [result,dite_eq_left h]
    exact ActivePrefixStageDispatchSelected.involutive d x
  · simp only [result,dite_eq_right h]
    exact ActivePrefixStageSingletonInverseData.dispatch (ActivePrefixStageRuntimeData.singleton d h) x

def pairProgramFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActivePrefixStageInverseMachine.twice (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
def pairProgram := pairProgramFor .tPure .tNegative .uPure .uNegative .pure .pure .pure

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
