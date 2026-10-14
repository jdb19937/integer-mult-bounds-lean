module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingScalarPath
public import IntegerMultBounds.Machine.CompactComplexActualReturnedOrdinal

/-! A genuine scalar event constructs a reached execution step after counted
siblings. Actual scalar/returned cursors are transported by symbolic ordinal
identities, and the existing lifecycle supplies both physical endpoints. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarStep
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

end Transport

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume entryReturned childExponent eventIndex sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}

/-- The actual scalar lifecycle constructs both the successor reached bank
and its paid fixed-table Step, with emitted arrays and both cursors derived. -/
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
      ∃ elapsedSteps≤CompactComplexScalarCountLifecycle.roleTimeConstant (block group)*
          (rowCount*2^shape.bits*2^polynomialExponent)*(ButterflyGuard.halfWidth metadataPrecision shape.bits+2)+1,
        Step basisProgram headerStack liveStack before after elapsedSteps := by
  have prefixOrdinal := CompactComplexActualScalarOrdinal.schedule_prefix_ordinal eventIndex eventBound group eventEquation
  let eventReached := reindex_reached before.reached rfl prefixOrdinal rfl
  have eventData := reindex_reached_data before.reached rfl prefixOrdinal rfl
  obtain ⟨nextReached,nextData,elapsedSteps,timeBound,scalarExecution⟩ :=
    CompactComplexAlignedSiblingScalarPath.scalar_successor basisProgram entryPath
      (Nat.pow_le_pow_right (by decide) (by omega)) ⟨eventIndex,eventBound⟩ group
      (by simpa only [List.get_eq_getElem] using eventEquation) eventReached
      rowsPositive guardPositive chunkPositive activePositive precisionReserve axesFit chunkRoom growthReserve
      baselineFits denominatorRoom headerStack liveStack
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
    reached := reindex_reached nextReached returnedEqual prefixEqual liveEqual }
  refine ⟨after,?_,elapsedSteps,timeBound,?_⟩
  · exact (reindex_reached_data nextReached returnedEqual prefixEqual liveEqual).trans
      (nextData.trans (congrArg (execute (block group)) eventData))
  · apply Step.scalar group eventBound eventEquation before after elapsedSteps
    rw [CompactComplexSourceReadyReachedEventTrace.cursorPC_event eventIndex eventBound,
      CompactComplexSourceReadyReachedEventTrace.cursorPC_next (⟨eventIndex,eventBound⟩ : Fin schedule.length)]
    exact scalarExecution

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarStep
