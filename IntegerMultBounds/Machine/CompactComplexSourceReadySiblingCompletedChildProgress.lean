module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildProgress
public import IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal

/-! Nonleaf return accounting from an actual completed child reached bank.
The original parent entry Path and actual scheduled cursor determine child
entry; the terminal child witness supplies its complete dependency ledger.
The completed target inequality remains an explicit execution boundary. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingCompletedChildProgress
noncomputable section
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path precedingCalls)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexCompletedLiveLower (schedule childNames Event)
open Networks.ComplexRecursiveCallSchema (Call calls)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  schedule calls CompactComplexDenominatorCapacity.scalarRows Networks.ComplexFramedExecution.rows

/-- At genuine schedule end every original call is counted exactly once;
this specializes only list identities, without evaluating concrete calls. -/
theorem returned_cursor_end (entryReturned childVolume : ℕ) :
    returnedCursor entryReturned schedule.length childVolume=entryReturned+calls.length*childVolume := by
  unfold returnedCursor
  rw [List.take_length,CompactComplexCompletedLiveLower.schedule_calls]

/-- The actual full schedule ends at the original compiler's complete scalar
prefix, so a terminal trace has the scalar index used by completed Progress. -/
theorem scalar_cursor_end :
    (CompactComplexActualScalarOrdinal.scalarGroups schedule).length = Networks.ComplexRank25.program.length := by
  rw [CompactComplexActualScalarOrdinal.schedule_scalarGroups]
  exact List.length_ofFn

section Parent
variable {stackCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
  {parentStage childStage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex : ℕ}
  {parentRows childRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
    parentScalarPrefix parentLive completedAxes completedLive : ℕ}
  {pcStack : Fin stackCount} {parentOrigin childOrigin : ℤ}
  {parentCalls childCalls : List Call}
  {parentBank childBank : Tapes (nodeTapes stackCount roles) 2}
  (entryPath : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
  (call : Call)
  (parentReached : Reached parentStage parentRows polynomialExponent metadataPrecision (childExponent+2)
    baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) parentScalarPrefix parentLive
    pcStack parentOrigin parentCalls parentBank)
  (childReached : Reached childStage childRows polynomialExponent metadataPrecision (childExponent+1)
    baselinePrecision growthConstant completedAxes baselineLive (dependencyLevels+1) (frameVolume+arity^(childExponent+2))
    (returnedCursor (entryReturned+precedingCalls call*arity^(childExponent+1)) schedule.length (arity^childExponent))
    Networks.ComplexRank25.program.length completedLive pcStack childOrigin childCalls childBank)

include childReached in
/-- Actual terminal storage accounting replaces an assumed completed ledger.
Its scalar-row count comes from this child witness's real complete prefix,
and its returned counter comes from the actual end of the original schedule. -/
theorem completed_ledger :
    completedLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows baselineLive
      (dependencyLevels+1) (frameVolume+arity^(childExponent+2))
      (entryReturned+precedingCalls call*arity^(childExponent+1)+calls.length*arity^childExponent)
      (CompactFramedScalarGrid.rows Networks.ComplexRank25.program.length).length := by
  have actualLedger := childReached.upper_ledger
  rw [returned_cursor_end] at actualLedger
  exact actualLedger

/-- Both return ledgers derive from genuine child-entry Paths and actual
reached banks. The final literal child Path pays the nonleaf completion;
completion of the chosen two-volume target is still required explicitly. -/
def progress
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (completedTarget : parentLive+2*arity^(childExponent+1)≤completedLive) :
    CompactComplexChildAlignmentBudget.Progress shape metadataPrecision parentLive completedLive
      (parentLive+2*arity^(childExponent+1)) :=
  CompactComplexSourceReadySiblingChildProgress.nonleaf entryPath call eventIndex metadataPrecision
    CompactComplexDenominatorCapacity.scalarRows baselineLive (CompactFramedScalarGrid.rows parentScalarPrefix).length parentLive
    eventBound eventEquation (by omega) (by omega) denominatorRoom
    (CompactComplexDenominatorCapacity.actual_prefix parentScalarPrefix) parentReached.upper_ledger
    completedLive (CompactFramedScalarGrid.rows Networks.ComplexRank25.program.length).length
    (CompactComplexDenominatorCapacity.actual_prefix Networks.ComplexRank25.program.length)
    (completed_ledger call childReached) completedTarget

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingCompletedChildProgress
