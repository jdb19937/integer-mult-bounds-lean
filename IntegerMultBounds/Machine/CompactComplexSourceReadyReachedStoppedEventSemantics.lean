module

public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedEventPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedChildSemantics

/-! The actual stopped event on the aligned table has the original decoded
child-instruction action. Forward, returned and inverse witnesses and their
individual data equations are extracted from the executed branch. This is a
local base semantic adapter, not full recursive schedule execution. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedEventSemantics
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller returnedData)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event childTarget)
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
private theorem extract_return_witnesses
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
    ∃ (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
      (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (aux : Tapes 2 2),
      ∃ returnedReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls
        (canonical (returnedCaller parentReached (CompactComplexRolePhaseSite.role call.site)
          (arity^(childExponent+1)) childResult control queue scalar tail storage) aux),
      returnedReached.data=returnedData parentReached (CompactComplexRolePhaseSite.role call.site)
        (arity^(childExponent+1)) childResult ∧
      let inverseArray := basisArray (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive parentSlots
        (CompactComplexRolePhaseSite.pc call.site) true
        (returnedReached.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)))
      ∃ finalReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls
        (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
          returnedReached.aux),
      finalReached.data=replacementData returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray ∧
      ∃ elapsedSteps≤timeBudget,
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack startPC initialBank elapsedSteps
          (CompactComplexScheduledPCLayout.callNextPC call)
          (CleanSubbank.bank (Alphabet.mapTapes encoding
            (ready (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
              returnedReached.aux)))) := by
  unfold ReturnOutcome at outcome
  dsimp only at outcome
  obtain ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,elapsedSteps,timeBound,physical⟩ := outcome
  exact ⟨_,_,_,_,_,_,returnedReached,returnedData,finalReached,finalData,elapsedSteps,timeBound,physical⟩


attribute [local irreducible] ReturnOutcome stoppedBank CompactComplexAlignedPoppedReturnReadiness.popped

/-- A complete executed stopped event returns one actual reached bank with
both its paid fixed-table path and its original child-instruction semantics.
Its Reached fields certify grid, literal live descriptor and upper ledger. -/
theorem stopped_event_values
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (parentTailsClean : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,parentReached.storage.head storagePort≤cell →
      parentReached.storage.tape storagePort cell=blank)
    (activePositive : 0<shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<rowCount) (childRowsPositive : 0<rowCount/roles) (rolesDivideRows : roles∣rowCount)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : basePrecision+2*shape.bits≤precision) (baselineFits : baseline≤basePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape precision ledgerLive
      parentReached.targetValue ledgerLeft ledgerExponent) :
    let stage := parent rowCoordinate entryPath.visit activeFitsAxes pair
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) logColumns
      precision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
      basisInput logColumns (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
        basisPC false (ActivePrefixStageNativePolynomial.symbols (2^logColumns)
          (NativePolynomialStageShape.width shape precision)) parentPacked)
    ∃ finalBank : Tapes (nodeTapes stackCount roles) 2,
      ∃ finalReached : Reached stage rowCount logColumns precision (childExponent+2)
        basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls finalBank,
      (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^logColumns))
        (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
        stored rowCoordinate entryPath.visit (rowCount/roles) logColumns (precision-2*shape.bits)
          (parentLive+arity^(childExponent+1)) finalReached.data row polynomialIndex globalAnchor=
        Networks.FramedFactorExecution.run
          [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
          (stored rowCoordinate entryPath.visit (rowCount/roles) logColumns (precision-2*shape.bits)
            parentLive parentReached.data row polynomialIndex globalAnchor)) ∧
      ∃ elapsedSteps≤(CompactComplexActualCallRoleAlignment.cost roles stage rowCount logColumns precision passTime+
        1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) rowCount logColumns precision+1)+
        (prefixCost (rowCount/roles) shape logColumns precision childExponent+
          returnCost rowCoordinate entryPath.visit activeFitsAxes pair call packingLimit guardPositive guardFitsChunk
            childRowsPositive parentSlots parentPacked),
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (CompactComplexScheduledPCLayout.eventPC ⟨eventIndex,eventBound⟩)
          (CleanSubbank.bank (Alphabet.mapTapes encoding (ready parentBank))) elapsedSteps
          (CompactComplexScheduledPCLayout.callNextPC call)
          (CleanSubbank.bank (Alphabet.mapTapes encoding (ready finalBank))) := by
  dsimp only
  obtain ⟨forwardReached,forwardData,targetRetained,forwardBasisBound,olderWord,olderHead,olderAssociated,outcome⟩ :=
    CompactComplexAlignedSiblingStoppedEventPath.runs rowCoordinate entryPath activeFitsAxes pair headerStack pcStack liveStack
      stackOrigin savedCalls parentBank ⟨eventIndex,eventBound⟩ parentReached call packingLimit basisProgram basisConstant basisRuns
      (by simpa only [List.get_eq_getElem] using eventEquation) pcHeaderDistinct pcLiveDistinct headerLiveDistinct
      parentTailsClean activePositive childStopped axesFit chunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive
      rolesDivideRows unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom
      axesPositive chunkPositive ledgerLive ledgerLeft ledgerExponent savedLedger
  obtain ⟨control,queue,scalar,tail,storage,aux,returnedReached,returnedDataEquation,
      finalReached,finalDataEquation,elapsedSteps,timeBound,physical⟩ :=
    extract_return_witnesses (rowCoordinate:=rowCoordinate) (entryPath:=entryPath) (activeFitsAxes:=activeFitsAxes) (pair:=pair)
      (parentReached:=forwardReached) (call:=call) (headerStack:=headerStack) (liveStack:=liveStack)
      (stoppedResult rowCoordinate entryPath.visit activeFitsAxes pair forwardReached call)
      (CompactComplexAlignedPoppedReturnReadiness.popped
        (stoppedBank rowCoordinate entryPath.visit activeFitsAxes pair forwardReached call headerStack liveStack)
        pcStack olderWord olderHead)
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked _ _ _ outcome
  refine ⟨_,finalReached,?_,elapsedSteps,timeBound,physical⟩
  intro row polynomialIndex globalAnchor
  exact CompactComplexSourceReadySiblingStoppedChildSemantics.reached_event_semantics
    rowCoordinate entryPath activeFitsAxes pair parentReached call
    guardPositive guardFitsChunk childRowsPositive parentSlots activePositive precisionReserve
    (by simpa only [Nat.zero_add] using axesFit) growthReserve chunkRoom control queue scalar tail storage aux
    forwardReached forwardData returnedReached returnedDataEquation finalReached finalDataEquation
    row polynomialIndex globalAnchor

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedEventSemantics
