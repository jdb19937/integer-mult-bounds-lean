module

public import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankPlaced
public import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersErase
public import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersAfterBudget
import Mathlib.Tactic.Positivity.Finset

/-! The real original-header consumer installation and the final generated
header erasure both have paid linear original payload-volume contracts. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankAfterBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersAfterBudget
open ActiveRepairLayoutRecordsHeadersSchedule ActiveRepairLayoutRecordsHeadersCount
open ActiveRepairRankHeadersCommands
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem ready_bound (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) : Bounded (ready d) (2*volume s rows+1) := by
  intro i
  have hh := counted_bound d hrows hp hfit i
  fin_cases i
  all_goals first | exact hh | (change 0≤_; omega)

def eraseConstant := 4*(300*3^ActiveRepairLayoutRecordsHeadersErase.schedule.length)

theorem erase_runtime_linear (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    ActiveRepairLayoutRecordsHeadersErase.runtime d≤eraseConstant*volume s rows := by
  have hv : 0<volume s rows := by unfold volume Shape.recordWidth; positivity
  have hh := scheduleCost_bounded ActiveRepairLayoutRecordsHeadersErase.schedule (ready d)
    (2*volume s rows+1) (ready_bound d hrows hp hfit)
  unfold ActiveRepairLayoutRecordsHeadersErase.runtime eraseConstant
  nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankAfterBudget
