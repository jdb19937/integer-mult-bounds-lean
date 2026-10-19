module

public import IntegerMultBounds.Machine.ActivePrefixStageHeadersSchedule
import Mathlib.Tactic.Positivity.Finset

/-! An actual fixed physical arithmetic schedule generates all numeric stage
geometry from the original thirteen retained words and clears its scratch. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData ActivePrefixStageHeadersSchedule
open ActivePrefixStageHeadersOps
variable {a : ℕ} {s : Shape}

def program (order : Order) := (compile (a := a) (schedule order)).2
def cost (order : Order) (v : Stage s) (rows : ℕ) := scheduleCost (schedule order) (initial v rows)

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard)
    (horder : Ordered order v) :
    HoareTime (program (a := a) order)
      (fun x => x=ActiveRepairRankHeadersCommands.bank (initial v rows))
      (fun x => x=ActiveRepairRankHeadersCommands.bank (finished order v rows)) (cost order v rows) := by
  have h := schedule_runs (a := a) (schedule order) (initial v rows) (schedule_valid order v rows hG horder)
  simpa only [execute_eq order v rows hG,program,cost] using h

theorem scratch_blank (order : Order) (v : Stage s) (rows : ℕ) (i : Fin 28) (hi : 22 ≤ i.val) :
    finished order v rows i=none := by simp [finished,show ¬ i.val<13 by omega,show ¬ i.val<22 by omega]

end
end IntegerMultBounds.Machine.ActivePrefixStageHeadersRun
