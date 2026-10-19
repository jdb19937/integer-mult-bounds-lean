module

public import IntegerMultBounds.Machine.ActiveRepairRankFieldsGeometry
public import IntegerMultBounds.Machine.ActiveRepairRankFieldsRun
import Mathlib.Tactic.Positivity.Finset

/-! Actual original-layout parsing endpoint: V/T/U/full source and selected
source bits are physically extracted from the genuine short record counter.
Record payload width is separate; the address shape has payload one. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsEndpoint
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankFieldsGeometry ActiveRepairRankFieldsBank
open BinaryAddressTableData (row)

def beforeStarts (s : Shape) (w m before after offset : ℕ) : Fin 4 → ℕ :=
  ![targetStart s after,tStart s w m before after,uStart s w m before after,prefixStart s m after+offset]
def afterStarts (s : Shape) (w m before after offset : ℕ) : Fin 4 → ℕ :=
  ![targetStart s after,tStart s w m before after,uStart s w m before after,tailBits s+offset]
def widths (w m sourceWidth : ℕ) : Fin 4 → ℕ := ![m,w,w,sourceWidth]

def expected (s : Shape) (w m before after rows : ℕ) (x : Address s w m before after rows)
    (xs : List Bool) (q rho n : ℕ) : Fin 5 → List Bool :=
  ![row m x.target.val,row w x.t.val,row w x.u.val,xs,SelectedSourceBitsData.selected xs q rho n]

variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (hactive : before+m+after=s.active*s.chunk) (hp : s.payload=1)
variable (x : Address s w m before after rows) (cs : List Bool)
variable (hcs : Counter.value cs=(index s w m before after rows hw hactive x).val)

include hw hactive in
theorem before_fits (offset sourceWidth : ℕ) (hplace : offset+sourceWidth≤before) :
    ∀ i, beforeStarts s w m before after offset i+widths w m sourceWidth i≤s.bits := by
  intro i
  fin_cases i
  all_goals dsimp [beforeStarts,widths,targetStart,tStart,uStart,prefixStart,tailBits,Shape.bits]
  all_goals omega

include hw hactive in
theorem after_fits (offset sourceWidth : ℕ) (hplace : offset+sourceWidth≤after) :
    ∀ i, afterStarts s w m before after offset i+widths w m sourceWidth i≤s.bits := by
  intro i
  fin_cases i
  all_goals dsimp [afterStarts,widths,targetStart,tStart,uStart,prefixStart,tailBits,Shape.bits]
  all_goals omega

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsEndpoint
