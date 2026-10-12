module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedEventPath
public import IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal

/-! A genuine stopped-child event constructs an actual reached execution step.
The forward/leaf/restoration/inverse run supplies its final physical bank;
actual cursor identities transport that endpoint into the next trace State.
Retained-target and frame-preservation invariants remain separate contracts. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedChildStep
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event childTarget)
open CompactComplexSourceReadyReachedEventTrace (State Step physicalBank)
open CompactComplexAlignedStoppedReturnPath (ReturnOutcome prefixCost returnCost stoppedResult stoppedBank)
open CompactNativeRoleConjugatedPorts (encoding)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Parent
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {leftBoundary childExponent rowCount logColumns precision basePrecision growthConstant baseline levels frames
    entryReturned eventIndex scalarPrefix parentLive : ℕ}
  (rowCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+2) levels frames entryReturned)
  (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair) rowCount logColumns precision
    (childExponent+2) basePrecision growthConstant 0 baseline levels frames
    (CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
    scalarPrefix parentLive pcStack stackOrigin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- Extract the actual final canonical bank while result and stopped-return
banks are abstract. No physical endpoint equality is an input. -/
private theorem extract_final
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2))
    (initialBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (timeBudget : ℕ)
    (outcome : ReturnOutcome rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
      childResult returnedBank packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive
      parentSlots parentPacked startPC initialBank timeBudget) :
    ∃ finalBank : Tapes (nodeTapes stackCount roles) 2,
      ∃ finalReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair) rowCount logColumns precision
        (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls finalBank,
      ∃ elapsedSteps≤timeBudget,
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack startPC initialBank elapsedSteps
          (CompactComplexScheduledPCLayout.callNextPC call)
          (CleanSubbank.bank (Alphabet.mapTapes encoding (ready finalBank))) := by
  unfold ReturnOutcome at outcome
  dsimp only at outcome
  obtain ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,elapsedSteps,timeBound,physical⟩ := outcome
  exact ⟨_,finalReached,elapsedSteps,timeBound,physical⟩

end Parent

attribute [local irreducible] ReturnOutcome stoppedResult stoppedBank CompactComplexAlignedPoppedReturnReadiness.popped

section Event
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex : ℕ}
  {rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- All literal programs, basis passes and table edges of one stopped event
are paid. Its next State is constructed from the actual returned witness. -/
theorem stopped_child_step
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (before : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) eventIndex sourceLive)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (parentTailsClean : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,before.reached.storage.head storagePort≤cell →
      before.reached.storage.tape storagePort cell=blank)
    (activePositive : 0<shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<rowCount) (childRowsPositive : 0<rowCount/roles) (rolesDivideRows : roles∣rowCount)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      before.reached.targetValue ledgerLeft ledgerExponent) :
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) polynomialExponent
      metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
      basisInput polynomialExponent (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
        basisPC false (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent)
          (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ after : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)),
      ∃ elapsedSteps≤(CompactComplexActualCallRoleAlignment.cost roles stage rowCount polynomialExponent metadataPrecision passTime+
        1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) rowCount polynomialExponent metadataPrecision+1)+
        (prefixCost (rowCount/roles) shape polynomialExponent metadataPrecision childExponent+
          returnCost phaseCoordinate entryPath.visit activeFits pair call packingLimit guardPositive guardFitsChunk
            childRowsPositive parentSlots parentPacked),
        Step basisProgram headerStack liveStack before after elapsedSteps := by
  dsimp only
  obtain ⟨forwardReached,forwardData,targetRetained,forwardBasisBound,olderWord,olderHead,olderAssociated,outcome⟩ :=
    CompactComplexAlignedSiblingStoppedEventPath.runs phaseCoordinate entryPath activeFits pair headerStack pcStack liveStack
      origin savedCalls before.bank ⟨eventIndex,eventBound⟩ before.reached call packingLimit basisProgram basisConstant basisRuns
      (by simpa only [List.get_eq_getElem] using eventEquation) pcHeaderDistinct pcLiveDistinct headerLiveDistinct
      parentTailsClean activePositive childStopped axesFit chunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive
      rolesDivideRows unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom
      axesPositive chunkPositive ledgerLive ledgerLeft ledgerExponent savedLedger
  obtain ⟨finalBank,finalReached,elapsedSteps,timeBound,physical⟩ :=
    extract_final (rowCoordinate:=phaseCoordinate) (entryPath:=entryPath) (activeFitsAxes:=activeFits) (pair:=pair)
      (parentReached:=forwardReached) (call:=call) (headerStack:=headerStack) (liveStack:=liveStack)
      (stoppedResult phaseCoordinate entryPath.visit activeFits pair forwardReached call)
      (CompactComplexAlignedPoppedReturnReadiness.popped
        (stoppedBank phaseCoordinate entryPath.visit activeFits pair forwardReached call headerStack liveStack)
        pcStack olderWord olderHead)
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked _ _ _ outcome
  have returnedSuccessor := CompactComplexSourceReadySiblingChildProgress.returned_cursor_successor
    entryReturned eventIndex (arity^(childExponent+1)) call eventBound eventEquation
  have scalarPreserved := CompactComplexActualScalarOrdinal.child_count_successor schedule eventIndex eventBound call eventEquation
  have stoppedTarget : childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1))
      sourceLive (childExponent+1)=sourceLive+arity^(childExponent+1) := by
    rw [childStopped]
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
    reached := by rw [returnedSuccessor,scalarPreserved,stoppedTarget];exact finalReached }
  refine ⟨after,elapsedSteps,timeBound,?_⟩
  apply Step.child call eventBound eventEquation before after elapsedSteps
  rw [CompactComplexSourceReadyReachedEventTrace.cursorPC_event eventIndex eventBound,
    CompactComplexSourceReadyReachedEventTrace.cursorPC_next (⟨eventIndex,eventBound⟩ : Fin schedule.length)]
  rw [CompactComplexScheduledPCLayout.actual_return_successor call (⟨eventIndex,eventBound⟩ : Fin schedule.length)
    (by simpa only [List.get_eq_getElem] using eventEquation)] at physical
  exact physical

end Event
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedChildStep
