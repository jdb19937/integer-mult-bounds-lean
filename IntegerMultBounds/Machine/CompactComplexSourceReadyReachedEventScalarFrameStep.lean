module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingScalarPath
public import IntegerMultBounds.Machine.CompactComplexActualReturnedOrdinal
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant

/-! A genuine scalar event constructs a reached execution step after counted
siblings. Actual scalar/returned cursors are transported by symbolic ordinal
identities, and the existing lifecycle supplies both physical endpoints. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarFrameStep
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes output)
open CompactComplexSourceReadyReachedEventInvariant (Reached nextCaller)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexActualScalarOrdinal (scalarGroups)
open CompactComplexSourceReadyReachedEventTrace (State Step physicalBank cursorPC)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  Networks.ComplexRecursiveCallSchema.sites Networks.ComplexRecursiveCallSchema.calls schedule
  CompactComplexRolePhaseSite.roleCount

section Transport
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume returnedBefore returnedAfter prefixBefore prefixAfter liveBefore liveAfter : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {bank : Tapes (nodeTapes stackCount roles) 2}

/-- Equality transport changes only the numerical indices of a reached
witness, retaining its literal physical bank and every data component. -/
private def reindex_reached
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedAfter prefixAfter liveAfter pcStack origin savedCalls bank := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  exact reached

private theorem reindex_reached_data
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    (reindex_reached reached returnedEqual prefixEqual liveEqual).data=reached.data := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  rfl

private theorem reindex_reached_fields
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    (reindex_reached reached returnedEqual prefixEqual liveEqual).targetValue=reached.targetValue ∧
    (reindex_reached reached returnedEqual prefixEqual liveEqual).storage=reached.storage ∧
    (reindex_reached reached returnedEqual prefixEqual liveEqual).aux=reached.aux := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  exact ⟨rfl,rfl,rfl⟩

/-- The retained target is certified by the actual physical target port;
all other fields, the data and the underlying bank remain literal. -/
private def retarget_reached
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (retainedTarget : ℕ)
    (targetPort : reached.storage.head (⟨8,by omega⟩ : Fin (10+stackCount))=1 ∧
      reached.storage.tape (⟨8,by omega⟩ : Fin (10+stackCount))=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits retainedTarget))
    (targetGrowth : retainedTarget≤liveBefore+2*arity^nodeExponent) :
    Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank :=
  { reached with targetValue := retainedTarget, target := targetPort, target_growth := targetGrowth }

end Transport

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume entryReturned childExponent eventIndex sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}

/-- The actual scalar lifecycle retains the same target certificate and ancestor
frames on its selected successor witness, with every physical edge paid. -/
theorem scalar_step
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+1)
      dependencyLevels frameVolume entryReturned)
    (headerStack liveStack : Fin stackCount) (group : GroupIndex)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.scalar group)
    (before : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) eventIndex sourceLive)
    (snapshot : Snapshot stackCount) (beforeSettled : Settled snapshot before.reached.storage before.reached.aux)
    (rowsPositive : 0<rowCount/roles) (guardPositive : 0<shape.guard) (chunkPositive : 0<shape.chunk)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤shape.chunk)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk) :
    ∃ after : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1) (sourceLive+(block group).length),
      after.reached.data=execute (block group) before.reached.data ∧
      after.reached.targetValue=before.reached.targetValue ∧
      Settled snapshot after.reached.storage after.reached.aux ∧
      ∃ elapsedSteps≤CompactComplexScalarCountLifecycle.roleTimeConstant (block group)*
          (rowCount*2^shape.bits*2^polynomialExponent)*(ButterflyGuard.halfWidth metadataPrecision shape.bits+2)+1,
        Step basisProgram headerStack liveStack before after elapsedSteps := by
  have prefixOrdinal := CompactComplexActualScalarOrdinal.schedule_prefix_ordinal eventIndex eventBound group eventEquation
  let eventReached := reindex_reached before.reached rfl prefixOrdinal rfl
  have eventData := reindex_reached_data before.reached rfl prefixOrdinal rfl
  have eventFields := reindex_reached_fields before.reached rfl prefixOrdinal rfl
  have eventSettled : Settled snapshot eventReached.storage eventReached.aux := by
    rw [eventFields.2.1,eventFields.2.2]
    exact beforeSettled
  obtain ⟨nextReached,nextData,elapsedSteps,timeBound,scalarExecution⟩ :=
    CompactComplexAlignedSiblingScalarPath.scalar_successor basisProgram entryPath
      (Nat.pow_le_pow_right (by decide) (by omega)) ⟨eventIndex,eventBound⟩ group
      (by simpa only [List.get_eq_getElem] using eventEquation) eventReached
      rowsPositive guardPositive chunkPositive activePositive precisionReserve axesFit chunkRoom growthReserve
      baselineFits denominatorRoom headerStack liveStack
  have endpointCanonical : output before.bank (nextCaller eventReached group)=
      CompactComplexSourceReadyReachedEventInvariant.canonical (nextCaller eventReached group) eventReached.aux :=
    (congrArg (fun bank => output bank (nextCaller eventReached group)) eventReached.canonical_bank).trans
      (CompactComplexSourceReadyReachedEventInvariant.canonical_output _ _ _)
  have endpointFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields nextReached
    (nextCaller eventReached group) eventReached.aux endpointCanonical
  have storagePreserved : nextReached.storage=CompactComplexScalarCallerEndpoint.storageOutput (by omega)
      eventReached.storage (sourceLive+(gates group).length) := by
    simpa only [nextCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using endpointFields.1
  have targetFrame := CompactComplexScalarCallerEndpoint.storage_frame (by omega) eventReached.storage
    (sourceLive+(gates group).length) (⟨8,by omega⟩ : Fin (10+stackCount)) (by norm_num)
  have targetPort : nextReached.storage.head (⟨8,by omega⟩ : Fin (10+stackCount))=1 ∧
      nextReached.storage.tape (⟨8,by omega⟩ : Fin (10+stackCount))=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits eventReached.targetValue) := by
    rw [storagePreserved]
    exact ⟨targetFrame.1.trans eventReached.target.1,targetFrame.2.trans eventReached.target.2⟩
  let normalizedReached := retarget_reached nextReached eventReached.targetValue targetPort
    (by have incomingGrowth := eventReached.target_growth;omega)
  have endpointSettled : Settled snapshot normalizedReached.storage normalizedReached.aux := by
    change Settled snapshot nextReached.storage nextReached.aux
    rw [storagePreserved,endpointFields.2]
    exact CompactComplexSourceReadySettledFrames.scalar_storage_settled eventSettled _
  have returnedEqual : returnedCursor entryReturned eventIndex (arity^childExponent)=
      returnedCursor entryReturned (eventIndex+1) (arity^childExponent) :=
    (CompactComplexActualReturnedOrdinal.scalar_returned_cursor entryReturned eventIndex (arity^childExponent)
      eventBound group eventEquation).symm
  have prefixEqual : group.val+1=(scalarGroups (schedule.take (eventIndex+1))).length := by
    have successor := CompactComplexActualScalarOrdinal.scalar_count_successor schedule eventIndex eventBound group eventEquation
    rw [prefixOrdinal] at successor
    exact successor.symm
  have liveEqual : sourceLive+(gates group).length=sourceLive+(block group).length := by
    rw [CompactComplexScalarSegmentRows.block_length]
  let after : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1) (sourceLive+(block group).length) := {
    inRange := by omega
    bank := output before.bank (nextCaller eventReached group)
    reached := reindex_reached normalizedReached returnedEqual prefixEqual liveEqual }
  have afterFields := reindex_reached_fields normalizedReached returnedEqual prefixEqual liveEqual
  refine ⟨after,?_,?_,?_,elapsedSteps,timeBound,?_⟩
  · exact (reindex_reached_data normalizedReached returnedEqual prefixEqual liveEqual).trans
      (nextData.trans (congrArg (execute (block group)) eventData))
  · exact afterFields.1.trans eventFields.1
  · change Settled snapshot (reindex_reached normalizedReached returnedEqual prefixEqual liveEqual).storage
      (reindex_reached normalizedReached returnedEqual prefixEqual liveEqual).aux
    rw [afterFields.2.1,afterFields.2.2]
    exact endpointSettled
  · apply Step.scalar group eventBound eventEquation before after elapsedSteps
    rw [CompactComplexSourceReadyReachedEventTrace.cursorPC_event eventIndex eventBound,
      CompactComplexSourceReadyReachedEventTrace.cursorPC_next (⟨eventIndex,eventBound⟩ : Fin schedule.length)]
    exact scalarExecution

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarFrameStep
