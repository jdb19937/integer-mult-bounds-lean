module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafReturnFrame
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafEventSuccessor

/-! A paid nonleaf event outcome becomes an actual scheduled successor with
its original target and ancestor frames. The returned bank is extracted from
the computed physical restoration, rather than supplied as an endpoint oracle.
The outcome must include the actual entry, child run and parent-return paths. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafReturnStep
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
open CompactComplexSourceReadyNonleafReturnFrame (ReturnOutcome)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Event
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex rowCount polynomialExponent
    metadataPrecision baselinePrecision growthConstant baselineLive sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

local notation "ParentState" => State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
  (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
  (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
  (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
  (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
  (origin:=origin) (savedCalls:=savedCalls)

/-- Consume a composed physical outcome on the actual event PC, preserving
its paid runtime, the captured ancestor snapshot and the immutable node target. -/
theorem step_of_outcome
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (headerStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (childNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false)
    (before : ParentState eventIndex sourceLive)
    {forwardBank : Tapes (nodeTapes stackCount roles) 2}
    (forwardReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent
      metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
      (CompactComplexActualScalarOrdinal.scalarGroups (schedule.take eventIndex)).length sourceLive pcStack origin savedCalls forwardBank)
    (forwardTarget : forwardReached.targetValue=before.reached.targetValue)
    (snapshot : Snapshot stackCount) (forwardSettled : Settled snapshot forwardReached.storage forwardReached.aux)
    (snapshotHeaderStack : snapshot.headerStack=headerStack)
    (snapshotLiveStack : snapshot.liveStack=liveStack) (snapshotPcStack : snapshot.pcStack=pcStack)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) polynomialExponent)
    (childBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (returnScalar : ActiveRepairRankHeadersCommands.State)
    (olderWord : ℤ → Fin 6) (olderHead : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls olderWord olderHead)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (timeBudget : ℕ)
    (outcome : ReturnOutcome phaseCoordinate entryPath activeFits pair forwardReached call headerStack liveStack
      childResult (CompactComplexAlignedPoppedReturnReadiness.popped childBank pcStack olderWord olderHead) returnScalar
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
      (CompactComplexScheduledPCLayout.eventPC ⟨eventIndex,eventBound⟩) (physicalBank before) timeBudget) :
    ∃ after : ParentState (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)),
      after.reached.targetValue=before.reached.targetValue ∧
      Settled snapshot after.reached.storage after.reached.aux ∧
      ∃ elapsedSteps≤timeBudget,Step basisProgram headerStack liveStack before after elapsedSteps := by
  obtain ⟨controlBank,queueBank,scalarHeaders,tailBank,storageBank,auxiliaryBank,returnedReached,returnedData,
      finalReached,finalData,targetPreserved,finalSettled,elapsedSteps,timeBound,physical⟩ :=
    CompactComplexSourceReadyNonleafReturnFrame.extract_final_settled
      phaseCoordinate entryPath activeFits pair forwardReached call headerStack liveStack
      childResult childBank returnScalar olderWord olderHead olderAssociated snapshot forwardSettled
      snapshotHeaderStack snapshotLiveStack snapshotPcStack headerLiveDistinct pcHeaderDistinct pcLiveDistinct
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
      _ _ timeBudget outcome
  obtain ⟨after,_sameBank,_sameData,targetRetained,settled,actualStep⟩ :=
    CompactComplexSourceReadyReachedNonleafEventSuccessor.successor
      phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack call eventBound eventEquation
      childNonstopped before _ finalReached snapshot (targetPreserved.trans forwardTarget) finalSettled elapsedSteps physical
  exact ⟨after,targetRetained,settled,elapsedSteps,timeBound,actualStep⟩

end Event
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafReturnStep
