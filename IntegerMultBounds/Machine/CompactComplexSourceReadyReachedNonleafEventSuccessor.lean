module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant

/-! A paid nonstopped child event's literal final reached bank becomes the
next scheduled State. Numerical transport preserves that bank, its coefficient
array, retained target and settled ancestor frame; this adapter does not assert
existence of the child execution or parent restoration. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafEventSuccessor
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event childTarget)
open CompactComplexSourceReadyReachedEventTrace (State Step physicalBank)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Transport
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume returnedBefore returnedAfter prefixBefore prefixAfter liveBefore liveAfter : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {bank : Tapes (nodeTapes stackCount roles) 2}

/-- Equality transport changes only the numerical indices of a reached
witness, retaining its literal physical bank and every data component. -/
def reindex_reached
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedAfter prefixAfter liveAfter pcStack origin savedCalls bank := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  exact reached

theorem reindex_reached_data
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    (reindex_reached reached returnedEqual prefixEqual liveEqual).data=reached.data := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  rfl

theorem reindex_reached_fields
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

end Transport

section Event
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex rowCount polynomialExponent
    metadataPrecision baselinePrecision growthConstant baselineLive sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- Package an actual fully paid nonstopped child event, retaining the same
literal output bank and coefficient data. Execution is an explicit compositional
input, to be supplied by child execution joined with physical parent return. -/
theorem successor
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (childNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false)
    (before : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) eventIndex sourceLive)
    (finalBank : Tapes (nodeTapes stackCount roles) 2)
    (finalReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent
      metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1))
      (CompactComplexActualScalarOrdinal.scalarGroups (schedule.take eventIndex)).length
      (sourceLive+2*arity^(childExponent+1)) pcStack origin savedCalls finalBank)
    (snapshot : Snapshot stackCount)
    (targetRetained : finalReached.targetValue=before.reached.targetValue)
    (finalSettled : Settled snapshot finalReached.storage finalReached.aux)
    (elapsedSteps : ℕ)
    (execution : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (CompactComplexScheduledPCLayout.eventPC ⟨eventIndex,eventBound⟩) (physicalBank before) elapsedSteps
      (CompactComplexScheduledPCLayout.callNextPC call) (CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
        (CompactComplexSourceReadyScalarWorkspace.ready finalBank)))) :
    ∃ after : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)),
      after.bank=finalBank ∧ after.reached.data=finalReached.data ∧
      after.reached.targetValue=before.reached.targetValue ∧
      Settled snapshot after.reached.storage after.reached.aux ∧
      Step basisProgram headerStack liveStack before after elapsedSteps := by
  have returnedSuccessor := CompactComplexSourceReadySiblingChildProgress.returned_cursor_successor
    entryReturned eventIndex (arity^(childExponent+1)) call eventBound eventEquation
  have scalarPreserved := CompactComplexActualScalarOrdinal.child_count_successor schedule eventIndex eventBound call eventEquation
  have nonstoppedTarget : childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1))
      sourceLive (childExponent+1)=sourceLive+2*arity^(childExponent+1) := by
    rw [childNonstopped]
    rfl
  let after : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)) := {
    inRange := by omega
    bank := finalBank
    reached := reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm nonstoppedTarget.symm }
  have fieldsPreserved := reindex_reached_fields finalReached returnedSuccessor.symm scalarPreserved.symm nonstoppedTarget.symm
  refine ⟨after,rfl,reindex_reached_data _ _ _ _,fieldsPreserved.1.trans targetRetained,?_,?_⟩
  · change Settled snapshot (reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm nonstoppedTarget.symm).storage
      (reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm nonstoppedTarget.symm).aux
    rw [fieldsPreserved.2.1,fieldsPreserved.2.2]
    exact finalSettled
  · apply Step.child call eventBound eventEquation before after elapsedSteps
    rw [CompactComplexSourceReadyReachedEventTrace.cursorPC_event eventIndex eventBound,
      CompactComplexSourceReadyReachedEventTrace.cursorPC_next (⟨eventIndex,eventBound⟩ : Fin schedule.length)]
    rw [CompactComplexScheduledPCLayout.actual_return_successor call (⟨eventIndex,eventBound⟩ : Fin schedule.length)
      (by simpa only [List.get_eq_getElem] using eventEquation)] at execution
    exact execution

end Event
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafEventSuccessor
