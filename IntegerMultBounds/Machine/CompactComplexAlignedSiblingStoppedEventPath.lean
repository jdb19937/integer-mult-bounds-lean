module

public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingChildEntryPath
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedReturnPath

/-! One complete scheduled stopped-child event on the unchanged aligned table.
Forward basis, child entry, classifier, leaf, saved-PC pop, parent restoration
and inverse basis are joined from actual event PC to original next-call PC. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedEventPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexAlignedChildEntryPath (BasisRuns path)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexAlignedStoppedReturnPath (ReturnOutcome stoppedResult stoppedBank prefixCost returnCost)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  schedule CompactComplexRolePhaseSite.roleCount

private theorem child_midpoint {stackCount : ℕ}
    (childBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2) :
    CleanSubbank.bank (s:=CompactComplexActualCallFullAlignment.localTapes roles)
      (Alphabet.mapTapes encoding (ready (CompactComplexSourceReadyWorkspace.ready childBank)))=
      CompactComplexAlignedChildReturnPath.liftedBank (CompactComplexSourceReadyWorkspace.bank childBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)) := rfl

section Parent
variable {stackCount basisStateCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  (headerStack pcStack liveStack : Fin stackCount) (origin : ℤ)
  (savedCalls : List Networks.ComplexRecursiveCallSchema.Call)
  (parentBank : Tapes (nodeTapes stackCount roles) 2)
  (eventPosition : Fin schedule.length)
  (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
    parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
    baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventPosition.val (arity^(childExponent+1))) scalarPrefix parentLive
    pcStack origin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call)

/-- Compose before actual banks specialize the dependent returned/final
witness types. Both path segments retain the same basis program and table. -/
private theorem append_return_outcome
    (childResult : CompactSpectatorVisitGeometry.Array shape (parentRows/roles) polynomialExponent)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<parentRows/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (startPC middlePC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2))
    (initialBank middleBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (prefixSteps prefixBudget suffixBudget : ℕ) (prefixBound : prefixSteps≤prefixBudget)
    (prefixExecution : path basisProgram headerStack pcStack liveStack startPC initialBank prefixSteps middlePC middleBank)
    (suffixOutcome : ReturnOutcome phaseCoordinate entryPath.visit activeFits pair parentReached call headerStack liveStack childResult returnedBank
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
      middlePC middleBank suffixBudget) :
    ReturnOutcome phaseCoordinate entryPath.visit activeFits pair parentReached call headerStack liveStack childResult returnedBank
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
      startPC initialBank (prefixBudget+suffixBudget) := by
  unfold ReturnOutcome at suffixOutcome ⊢
  dsimp only at suffixOutcome ⊢
  obtain ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,suffixSteps,suffixBound,suffixExecution⟩ := suffixOutcome
  refine ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,
    prefixSteps+suffixSteps,Nat.add_le_add prefixBound suffixBound,?_⟩
  exact FiniteFlowPath.append prefixExecution suffixExecution

attribute [local irreducible] ReturnOutcome stoppedResult stoppedBank CompactComplexAlignedPoppedReturnReadiness.popped

/-- Complete stopped event: genuine forward and stopped-result data, older
saved history, restored/inverse reached witnesses and their fully paid path. -/
theorem runs (packingLimit : ℕ)
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (eventEquation : schedule.get eventPosition=Event.child call)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (headerLiveDistinct : headerStack≠liveStack)
    (parentTailsClean : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,parentReached.storage.head storagePort≤cell →
      parentReached.storage.tape storagePort cell=blank)
    (activePositive : 0<shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<parentRows) (childRowsPositive : 0<parentRows/roles) (rolesDivideRows : roles∣parentRows)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f →
      ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input
          (parent phaseCoordinate entryPath.visit activeFits pair) (parentRows/roles) polynomialExponent
          metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      parentReached.targetValue ledgerLeft ledgerExponent) :
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (parentRows/roles) polynomialExponent
      metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let afterBasis := basisArray stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive
      guardFitsChunk childRowsPositive parentSlots basisPC false
      (parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
      basisInput polynomialExponent (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
        basisPC false (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent)
          (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ forwardReached : Reached stage parentRows polynomialExponent metadataPrecision (childExponent+2)
      baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventPosition.val (arity^(childExponent+1))) scalarPrefix parentLive
      pcStack origin savedCalls (canonical (replacementCaller parentReached selectedRole afterBasis) parentReached.aux),
      forwardReached.data=replacementData parentReached selectedRole afterBasis ∧
      forwardReached.targetValue=parentReached.targetValue ∧
      (CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent metadataPrecision passTime : ℝ)≤
        basisConstant*ActivePrefixStageInverseBudget.scale basisInput ∧
      ∃ olderWord olderHead,
        CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls olderWord olderHead ∧
        ReturnOutcome phaseCoordinate entryPath.visit activeFits pair forwardReached call headerStack liveStack
          (stoppedResult phaseCoordinate entryPath.visit activeFits pair forwardReached call)
          (CompactComplexAlignedPoppedReturnReadiness.popped
            (stoppedBank phaseCoordinate entryPath.visit activeFits pair forwardReached call headerStack liveStack)
            pcStack olderWord olderHead)
          packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
          (CompactComplexScheduledPCLayout.eventPC eventPosition)
          (CleanSubbank.bank (Alphabet.mapTapes encoding (ready parentBank)))
          ((CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent metadataPrecision passTime+
            1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) parentRows polynomialExponent metadataPrecision+1)+
            (prefixCost (parentRows/roles) shape polynomialExponent metadataPrecision childExponent+
              returnCost phaseCoordinate entryPath.visit activeFits pair call packingLimit guardPositive guardFitsChunk
                childRowsPositive parentSlots parentPacked)) := by
  dsimp only
  obtain ⟨forwardReached,forwardData,targetRetained,forwardBasisBound,entrySteps,entryBound,entryExecution⟩ :=
    CompactComplexAlignedSiblingChildEntryPath.child_paths phaseCoordinate entryPath activeFits pair headerStack pcStack liveStack
      origin savedCalls parentBank eventPosition parentReached call packingLimit basisProgram basisConstant basisRuns
      eventEquation pcHeaderDistinct pcLiveDistinct guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows
      unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
      ledgerLive ledgerLeft ledgerExponent savedLedger
  have forwardStorageFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields forwardReached _ parentReached.aux rfl
  have storagePreserved : forwardReached.storage=parentReached.storage := by
    simpa only [replacementCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank]
      using forwardStorageFields.1
  have forwardTailsClean : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,forwardReached.storage.head storagePort≤cell →
      forwardReached.storage.tape storagePort cell=blank := by
    rw [storagePreserved]
    exact parentTailsClean
  have forwardLedger := CompactComplexSourceReadySiblingChildProgress.retainedTargetLedger savedLedger targetRetained
  obtain ⟨olderWord,olderHead,olderAssociated,returnOutcome⟩ :=
    CompactComplexAlignedSiblingStoppedReturnPath.runs phaseCoordinate entryPath activeFits pair forwardReached call headerStack liveStack
      packingLimit basisProgram basisConstant basisRuns eventPosition.isLt
      (by simpa only [List.get_eq_getElem] using eventEquation) headerLiveDistinct pcHeaderDistinct pcLiveDistinct
      forwardTailsClean precisionReserve baselineFits denominatorRoom activePositive axesPositive guardPositive guardFitsChunk
      childRowsPositive rolesDivideRows unitPayload childStopped axesFit growthReserve chunkRoom
      ledgerLive ledgerLeft ledgerExponent forwardLedger parentSlots parentPacked
  have childBankEquality : CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate entryPath activeFits pair
      forwardReached call headerStack liveStack=
      CompactComplexSourceReadyCapturedChildFrames.childOutput phaseCoordinate entryPath.visit activeFits pair
        forwardReached call headerStack liveStack := rfl
  rw [child_midpoint,childBankEquality] at entryExecution
  refine ⟨forwardReached,forwardData,targetRetained,forwardBasisBound,olderWord,olderHead,olderAssociated,?_⟩
  exact append_return_outcome (phaseCoordinate:=phaseCoordinate) (entryPath:=entryPath)
    (activeFits:=activeFits) (pair:=pair) (headerStack:=headerStack) (pcStack:=pcStack) (liveStack:=liveStack)
    (origin:=origin) (savedCalls:=savedCalls) (parentBank:=_) (eventPosition:=eventPosition)
    (parentReached:=forwardReached) (call:=call)
    (stoppedResult phaseCoordinate entryPath.visit activeFits pair forwardReached call)
    (CompactComplexAlignedPoppedReturnReadiness.popped
      (stoppedBank phaseCoordinate entryPath.visit activeFits pair forwardReached call headerStack liveStack)
      pcStack olderWord olderHead)
    packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
    _ _ _ _ entrySteps _ _ entryBound entryExecution returnOutcome

end Parent
end
end IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedEventPath
