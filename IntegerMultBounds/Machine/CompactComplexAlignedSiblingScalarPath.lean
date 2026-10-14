module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingScalarPath
public import IntegerMultBounds.Machine.CompactComplexAlignedScalarEventPath
public import IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal

/-! Actual scalar events after counted child returns execute in the unchanged
aligned prime-alphabet table. The original entry Path supplies all numerical
readiness; no dependency Path with an advanced sibling counter is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedSiblingScalarPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes output)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexSourceReadyReachedEventInvariant (Reached nextCaller)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexAlignedScalarEventPath (bank path)
open CompactComplexActualCallFullAlignment (localTapes)
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCompletedLiveLower.schedule
  CompactComplexRolePhaseSite.roleCount

variable {extraTapes basisStates : ℕ} {shape : Shape}
  {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned childVolume : ℕ}
  {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive parentLive : ℕ}
  {pcStack : Fin extraTapes} {origin : ℤ}
  {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes extraTapes roles) 2}

/-- The real event derives the scalar cursor expected by its reached bank. -/
theorem event_cursor
    (eventIndex : Fin CompactComplexCompletedLiveLower.schedule.length) (group : GroupIndex)
    (eventEquation : CompactComplexCompletedLiveLower.schedule.get eventIndex=
      CompactComplexCompletedLiveLower.Event.scalar group) :
    (CompactComplexActualScalarOrdinal.scalarGroups
      (CompactComplexCompletedLiveLower.schedule.take eventIndex.val)).length=group.val :=
  CompactComplexActualScalarOrdinal.schedule_prefix_ordinal eventIndex.val eventIndex.isLt group
    (by simpa only [List.get_eq_getElem] using eventEquation)

/-- The original scalar lifecycle and its real table edge are both paid,
retaining the actual emitted arrays and the blank basis workspace. -/
theorem scalar_successor
    (basisProgram : Program ActivePrefixStageNative.tapes basisStates prime)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent)
    (eventIndex : Fin CompactComplexCompletedLiveLower.schedule.length) (group : GroupIndex)
    (eventEquation : CompactComplexCompletedLiveLower.schedule.get eventIndex=
      CompactComplexCompletedLiveLower.Event.scalar group)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex.val childVolume) group.val parentLive
      pcStack origin savedCalls parentBank)
    (rowsPositive : 0<parentRows/roles) (guardPositive : 0<shape.guard)
    (chunkPositive : 0<shape.chunk) (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤shape.chunk)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room
      CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (headerStack liveStack : Fin extraTapes) :
    ∃ nextReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex.val childVolume) (group.val+1)
      (parentLive+(gates group).length) pcStack origin savedCalls
      (output parentBank (nextCaller parentReached group)),
      nextReached.data=execute (block group) parentReached.data ∧
      ∃ elapsedSteps≤CompactComplexScalarCountLifecycle.roleTimeConstant (block group)*
        (parentRows*2^shape.bits*2^polynomialExponent)*
        (ButterflyGuard.halfWidth metadataPrecision shape.bits+2)+1,
        path basisProgram headerStack pcStack liveStack
          (CompactComplexScheduledPCLayout.eventPC eventIndex) (bank parentBank) elapsedSteps
          (CompactComplexScheduledPCLayout.nextPC eventIndex)
          (bank (output parentBank (nextCaller parentReached group))) := by
  obtain ⟨scalarRuns,nextReached,nextDataEquation⟩ :=
    CompactComplexSourceReadySiblingScalarPath.scalar_successor entryPath childFitsNode group parentReached
      rowsPositive guardPositive chunkPositive activePositive precisionReserve axesFit chunkRoom
      growthReserve baselineFits denominatorRoom
  have alignedRuns := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _
    (SharedBank.empty (localTapes roles) prime) scalarRuns
  refine ⟨nextReached,nextDataEquation,?_⟩
  exact CompactComplexAlignedScalarEventPath.scalar_local basisProgram headerStack pcStack liveStack
    eventIndex group eventEquation (bank parentBank)
    (bank (output parentBank (nextCaller parentReached group))) _ alignedRuns

end
end IntegerMultBounds.Machine.CompactComplexAlignedSiblingScalarPath
