module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildInvariant
public import IntegerMultBounds.Machine.CompactComplexChildAlignmentBudget

/-! Actual return-side accounting Paths at scheduled sibling calls. The
before ledger is paid by the genuine child-entry Path. A stopped child uses
that same Path; a completed nonleaf node uses its actual final literal child's
Path, with the last missing sibling volume paid by that node's real frame. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildProgress
noncomputable section
open CompactComplexRecursiveGeometry (arity)
open CompactComplexDenominatorCapacity (ledger)
open CompactRecursiveDependencyBudget (Path precedingCalls)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule childNames Event)
open Networks.ComplexRecursiveCallSchema (Call calls)
open CompactComplexChildAlignmentBudget (Progress)
attribute [local instance] Classical.propDecidable
local instance : DecidableEq Call := Classical.typeDecidableEq _
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  schedule calls CompactComplexDenominatorCapacity.scalarRows Networks.ComplexFramedExecution.rows

/-- Account with symbolic volumes before specializing to the actual arity.
The new dependency level pays used scalar rows; the real enclosing frame pays
the stopped child's one-volume denominator advance. -/
theorem stopped_ledger_arithmetic
    (rowBound baselineLive dependencyLevels frameVolume returnedVolume usedRows
      parentLive childVolume parentVolume : ℕ)
    (rowsUsedBound : usedRows ≤ rowBound)
    (childFitsParent : childVolume ≤ parentVolume)
    (parentLedger : parentLive ≤ ledger rowBound baselineLive dependencyLevels
      frameVolume returnedVolume usedRows) :
    parentLive + childVolume ≤ ledger rowBound baselineLive (dependencyLevels + 1)
      (frameVolume + parentVolume) returnedVolume 0 := by
  unfold ledger at *
  simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero]
  omega

/-- A completed node's last child's genuine Path pays the complete sibling
counter: its enclosing frame covers the last double return charge. -/
theorem completed_ledger_arithmetic
    (rowBound baselineLive dependencyLevels frameVolume entryReturned usedRows
      completedLive childVolume parentVolume callCount lastOrdinal : ℕ)
    (rowsUsedBound : usedRows ≤ rowBound)
    (ordinalEquation : lastOrdinal + 1 = callCount)
    (framePaysReturn : 2 * childVolume ≤ parentVolume)
    (completedLedger : completedLive ≤ ledger rowBound baselineLive dependencyLevels
      frameVolume (entryReturned + callCount * childVolume) usedRows) :
    completedLive ≤ ledger rowBound baselineLive (dependencyLevels + 1)
      (frameVolume + parentVolume) (entryReturned + lastOrdinal * childVolume) 0 := by
  rw [← ordinalEquation] at completedLedger
  unfold ledger at *
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.add_zero] at *
  omega

private theorem returned_cursor_eq (entryReturned eventIndex childVolume : ℕ) :
    returnedCursor entryReturned eventIndex childVolume=
      entryReturned+(childNames (schedule.take eventIndex)).length*childVolume := rfl

/-- The completed scheduled child advances its parent's real cursor by exactly
one child volume, providing the next event's original-entry accounting index. -/
theorem returned_cursor_successor (entryReturned eventIndex childVolume : ℕ) (call : Call)
    (eventBound : eventIndex < schedule.length)
    (eventEquation : schedule[eventIndex] = Event.child call) :
    returnedCursor entryReturned (eventIndex + 1) childVolume =
      returnedCursor entryReturned eventIndex childVolume + childVolume := by
  rw [returned_cursor_eq, returned_cursor_eq,
    List.take_succ_eq_append_getElem eventBound, eventEquation,
    CompactComplexSourceReadyEventScheduleSemantics.childNames_append]
  simp only [childNames, List.length_append, List.length_cons, List.length_nil]
  ring

theorem last_position_bound (callCount existingOrdinal : ℕ) (ordinalFits : existingOrdinal<callCount) :
    callCount-1<callCount := by omega

theorem last_ordinal_succ (callCount lastOrdinal : ℕ) (callCountPositive : 0<callCount)
    (ordinalEquation : lastOrdinal=callCount-1) : lastOrdinal+1=callCount := by omega

/-- Last element of a nonempty symbolic list. This generic definition keeps
concrete compiler call enumeration outside kernel conversion. -/
def lastElement {Element : Type*} (items : List Element) (itemsPositive : 0 < items.length) : Element :=
  items[items.length-1]'(by omega)

/-- The last position's index follows solely from distinctness of an abstract
list, before any specialization to the actual compiler call list. -/
theorem last_element_ordinal {Element : Type*} [DecidableEq Element] (items : List Element)
    (itemsDistinct : items.Nodup) (itemsPositive : 0 < items.length) :
    items.idxOf (lastElement items itemsPositive)+1=items.length := by
  classical
  have lastBound : items.length - 1 < items.length := by omega
  have literalOrdinal := itemsDistinct.idxOf_getElem (items.length-1) lastBound
  have namedOrdinal : items.idxOf (lastElement items itemsPositive)=items.length-1 := by
    simpa only [lastElement] using literalOrdinal
  exact last_ordinal_succ items.length (items.idxOf (lastElement items itemsPositive)) itemsPositive namedOrdinal

attribute [local irreducible] lastElement

/-- A genuine call witnesses nonemptiness of the original call list, so its
last position is an actual literal call rather than an invented ordinal. -/
def finalCall (existingCall : Call) : Call :=
  lastElement calls (Nat.zero_lt_of_lt (CompactRecursiveDependencyBudget.precedingCalls_lt existingCall))

attribute [local irreducible] finalCall

theorem final_call_eq (existingCall : Call) :
    finalCall existingCall=lastElement calls
      (Nat.zero_lt_of_lt (CompactRecursiveDependencyBudget.precedingCalls_lt existingCall)) := by
  unfold finalCall
  rfl

/-- The last literal call's preceding-sibling ordinal specializes the abstract
list theorem and the already proved original-call ordinal correspondence. -/
theorem final_call_ordinal (existingCall : Call) :
    precedingCalls (finalCall existingCall)+1=calls.length := by
  classical
  have namedOrdinal := last_element_ordinal calls CompactComplexActualCallOrdinal.calls_nodup
    (Nat.zero_lt_of_lt (CompactRecursiveDependencyBudget.precedingCalls_lt existingCall))
  rw [←final_call_eq existingCall] at namedOrdinal
  rw [CompactComplexActualCallOrdinal.calls_idxOf] at namedOrdinal
  exact namedOrdinal

/-- The extra real scalar dependency level and enclosing parent frame pay the
current parent's used scalar prefix and one stopped child-volume advance. -/
theorem stopped_child_ledger (rowBound baselineLive dependencyLevels frameVolume entryReturned eventIndex
    usedRows parentLive childExponent : ℕ) (call : Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (rowsUsedBound : usedRows≤rowBound)
    (parentLedger : parentLive≤ledger rowBound baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) usedRows) :
    parentLive+arity^(childExponent+1)≤ledger rowBound baselineLive (dependencyLevels+1)
      (frameVolume+arity^(childExponent+2))
      (entryReturned+precedingCalls call*arity^(childExponent+1)) 0 := by
  have ordinal := CompactComplexActualCallOrdinal.schedule_prefix_ordinal eventIndex eventBound call eventEquation
  rw [returned_cursor_eq,ordinal] at parentLedger
  have childVolumeFits : arity^(childExponent+1)≤arity^(childExponent+2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact stopped_ledger_arithmetic rowBound baselineLive dependencyLevels frameVolume
    (entryReturned+precedingCalls call*arity^(childExponent+1)) usedRows parentLive
    (arity^(childExponent+1)) (arity^(childExponent+2)) rowsUsedBound childVolumeFits parentLedger

/-- Final child accounting uses its genuine last-call Path. One new scalar
level pays the used prefix, and the enclosing node frame pays the last missing
sibling's double return charge. -/
theorem completed_child_ledger (rowBound baselineLive dependencyLevels frameVolume entryReturned usedRows
    completedLive childExponent : ℕ) (existingCall : Call)
    (rowsUsedBound : usedRows≤rowBound)
    (completedLedger : completedLive≤ledger rowBound baselineLive dependencyLevels frameVolume
      (entryReturned+calls.length*arity^childExponent) usedRows) :
    completedLive≤ledger rowBound baselineLive (dependencyLevels+1)
      (frameVolume+arity^(childExponent+1))
      (entryReturned+precedingCalls (finalCall existingCall)*arity^childExponent) 0 := by
  have lastOrdinal := final_call_ordinal existingCall
  have framePaysReturn : 2*arity^childExponent≤arity^(childExponent+1) := by
    rw [pow_succ]
    have arityLarge : 2≤arity := by decide
    nlinarith only [Nat.mul_le_mul_right (arity^childExponent) arityLarge]
  exact completed_ledger_arithmetic rowBound baselineLive dependencyLevels frameVolume
    entryReturned usedRows completedLive (arity^childExponent) (arity^(childExponent+1))
    calls.length (precedingCalls (finalCall existingCall)) rowsUsedBound lastOrdinal framePaysReturn completedLedger

section Progress
variable {shape : CompactGadgetReservationShape.Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  (entryPath : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
  (call : Call) (eventIndex metadataPrecision rowBound baselineLive usedRows parentLive : ℕ)
  (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
  (metadataFits : 2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤metadataPrecision-2*shape.bits)
  (denominatorRoom : CompactComplexDenominatorCapacity.room rowBound≤shape.chunk)
  (rowsUsedBound : usedRows≤rowBound)
  (parentLedger : parentLive≤ledger rowBound baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) usedRows)

include eventIndex usedRows eventBound eventEquation rowsUsedBound parentLedger in
theorem entry_ledger :
    parentLive≤ledger rowBound baselineLive (dependencyLevels+1) (frameVolume+arity^(childExponent+2))
      (entryReturned+precedingCalls call*arity^(childExponent+1)) 0 := by
  have stoppedLedger := stopped_child_ledger rowBound baselineLive dependencyLevels frameVolume entryReturned eventIndex
    usedRows parentLive childExponent call eventBound eventEquation rowsUsedBound parentLedger
  omega

/-- Both ledgers are actual child-entry dependency Paths in the stopped
branch. Its one-volume advance fits the real enclosing node frame. -/
def stopped : Progress shape metadataPrecision parentLive
    (parentLive+arity^(childExponent+1)) (parentLive+arity^(childExponent+1)) where
  R := rowBound
  baseline := baselineLive
  parentLeft := nodeLeft+call.slot.val*arity^(childExponent+1)
  parentExponent := childExponent+1
  parentLevels := dependencyLevels+1
  parentFrames := frameVolume+arity^(childExponent+2)
  parentReturned := entryReturned+precedingCalls call*arity^(childExponent+1)
  parentUsed := 0
  childLeft := nodeLeft+call.slot.val*arity^(childExponent+1)
  childExponent := childExponent+1
  childLevels := dependencyLevels+1
  childFrames := frameVolume+arity^(childExponent+2)
  childReturned := entryReturned+precedingCalls call*arity^(childExponent+1)
  childUsed := 0
  parentPath := Path.child entryPath call
  childPath := Path.child entryPath call
  metadata := metadataFits
  base := baselineFits
  room := denominatorRoom
  parentUsed_le := Nat.zero_le _
  childUsed_le := Nat.zero_le _
  before_live := entry_ledger call eventIndex rowBound baselineLive usedRows parentLive eventBound eventEquation rowsUsedBound parentLedger
  completed_live := stopped_child_ledger rowBound baselineLive dependencyLevels frameVolume entryReturned eventIndex
    usedRows parentLive childExponent call eventBound eventEquation rowsUsedBound parentLedger
  target_growth := by omega
  promote := Nat.le_add_right _ _
  contract := le_rfl

/-- Before accounting uses this scheduled call's real entry Path; after
accounting uses its completed nonleaf node's actual final literal child Path. -/
def nonleaf (completedLive : ℕ)
    (completedUsedRows : ℕ) (completedRowsBound : completedUsedRows≤rowBound)
    (completedLedger : completedLive≤ledger rowBound baselineLive (dependencyLevels+1)
      (frameVolume+arity^(childExponent+2))
      (entryReturned+precedingCalls call*arity^(childExponent+1)+calls.length*arity^childExponent) completedUsedRows)
    (completedTarget : parentLive+2*arity^(childExponent+1)≤completedLive) :
    Progress shape metadataPrecision parentLive completedLive (parentLive+2*arity^(childExponent+1)) where
  R := rowBound
  baseline := baselineLive
  parentLeft := nodeLeft+call.slot.val*arity^(childExponent+1)
  parentExponent := childExponent+1
  parentLevels := dependencyLevels+1
  parentFrames := frameVolume+arity^(childExponent+2)
  parentReturned := entryReturned+precedingCalls call*arity^(childExponent+1)
  parentUsed := 0
  childLeft := (nodeLeft+call.slot.val*arity^(childExponent+1))+(finalCall call).slot.val*arity^childExponent
  childExponent := childExponent
  childLevels := (dependencyLevels+1)+1
  childFrames := (frameVolume+arity^(childExponent+2))+arity^(childExponent+1)
  childReturned := (entryReturned+precedingCalls call*arity^(childExponent+1))+precedingCalls (finalCall call)*arity^childExponent
  childUsed := 0
  parentPath := Path.child entryPath call
  childPath := Path.child (Path.child entryPath call) (finalCall call)
  metadata := metadataFits
  base := baselineFits
  room := denominatorRoom
  parentUsed_le := Nat.zero_le _
  childUsed_le := Nat.zero_le _
  before_live := entry_ledger call eventIndex rowBound baselineLive usedRows parentLive eventBound eventEquation rowsUsedBound parentLedger
  completed_live := completed_child_ledger rowBound baselineLive (dependencyLevels+1)
    (frameVolume+arity^(childExponent+2)) (entryReturned+precedingCalls call*arity^(childExponent+1))
    completedUsedRows completedLive childExponent call completedRowsBound completedLedger
  target_growth := le_rfl
  promote := Nat.le_add_right _ _
  contract := completedTarget

end Progress

section EntryTarget
open CompactGadgetReservationShape (Shape)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)

/-- The pending target's budget is captured at genuine node entry. Later
sibling cursors need not (and must not) alter the entry dependency Path when
the unchanged target is restored from its saved frame. -/
def entryTargetLedger
    {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {rows polynomialExponent metadataPrecision nodeLeft nodeExponent baselinePrecision
      growthConstant completedAxes baselineLive dependencyLevels frameVolume entryReturned
      scalarPrefix entryLive : ℕ}
    {pcStack : Fin extraTapes} {stackOrigin : ℤ} {savedCalls : List Call}
    {entryBank : Tapes (nodeTapes extraTapes roles) 2}
    (entryPath : Path shape.active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (entryReached : Reached stage rows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      entryReturned scalarPrefix entryLive pcStack stackOrigin savedCalls entryBank)
    (metadataFits : baselinePrecision + 2 * shape.bits ≤ metadataPrecision)
    (baselineFits : baselineLive ≤ baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room
      CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk) :
    CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision entryLive
      entryReached.targetValue nodeLeft nodeExponent where
  R := CompactComplexDenominatorCapacity.scalarRows
  baseline := baselineLive
  levels := dependencyLevels
  frames := frameVolume
  returned := entryReturned
  used := (CompactFramedScalarGrid.rows scalarPrefix).length
  path := entryPath
  metadata := by omega
  base := by omega
  room := denominatorRoom
  used_le := CompactComplexDenominatorCapacity.actual_prefix scalarPrefix
  live := entryReached.upper_ledger
  target_growth := entryReached.target_growth

/-- Restore the retained target using its entry certificate, even after
the live denominator and sibling counter have advanced. -/
def retainedTargetLedger
    {shape : Shape} {metadataPrecision entryLive entryTarget currentTarget nodeLeft nodeExponent : ℕ}
    (entryLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision
      entryLive entryTarget nodeLeft nodeExponent)
    (targetRetained : currentTarget = entryTarget) :
    CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision
      entryLive currentTarget nodeLeft nodeExponent :=
  targetRetained.symm ▸ entryLedger

end EntryTarget

end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildProgress
