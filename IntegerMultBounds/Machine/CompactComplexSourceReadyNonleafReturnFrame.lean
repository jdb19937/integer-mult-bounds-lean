module

public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingJoinedPhysicalReturn
public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames

/-! Exact nonleaf physical-return outcomes use the captured original parent
header, live and target frames and the genuinely popped child PC stack.
Restoration advances the denominator by twice the child volume and the
returned-volume cursor by once its volume. The computed endpoint retains
ancestor frames and the original parent target without a storage oracle. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafReturnFrame
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical caller)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller returnedData)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexAlignedReachedChildReturnPath (mid)
open CompactComplexSourceReadyChildReturnPath (storagePart controlPart queuePart tailPart)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
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

/-- Exact result type of captured sibling restoration and inverse basis. -/
def ReturnOutcome
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (returnScalar : ActiveRepairRankHeadersCommands.State)
    (basisWidth : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardSufficient : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (slotsCorrect : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth)
    (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+CompactComplexCompletedLiveLower.schedule.length)+2))
    (initialBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (totalBudget : ℕ) : Prop :=
    let stage := parent rowCoordinate entryPath.visit activeFitsAxes pair
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let basisOccurrence := CompactComplexRolePhaseSite.pc call.site
    let restoredMidpoint := mid selectedRole (caller parentReached) returnedBank headerStack liveStack (parentReached.storage.tape (Fin.natAdd 10 headerStack)) (parentReached.storage.head (Fin.natAdd 10 headerStack)) (parentReached.storage.tape (Fin.natAdd 10 liveStack)) (parentReached.storage.head (Fin.natAdd 10 liveStack)) (childExponent+2) parentLive (parentLive+2*arity^(childExponent+1))
      rowCoordinate entryPath.visit activeFitsAxes pair rowCount logColumns precision (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult))
    let restoredStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart restoredMidpoint)
      (parentLive+2*arity^(childExponent+1)) (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) (parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount))) parentReached.targetValue
    let restoredParentBank := canonical (returnedCaller parentReached selectedRole (2*arity^(childExponent+1)) childResult (controlPart restoredMidpoint) (queuePart restoredMidpoint)
      returnScalar (tailPart restoredMidpoint) restoredStorage) parentReached.aux
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput logColumns
      (CompactComplexActualCallAlignment.nativeCost basisWidth basisInput slotsCorrect basisOccurrence true
        (ActivePrefixStageNativePolynomial.symbols (2^logColumns) (NativePolynomialStageShape.width shape precision)) basisPacked)
    ∃ returnedReached : Reached stage rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames ((returnedCursor entryReturned eventIndex (arity^(childExponent+1)))+(arity^(childExponent+1))) scalarPrefix
      (parentLive+2*arity^(childExponent+1)) pcStack stackOrigin savedCalls restoredParentBank,
      returnedReached.data=returnedData parentReached selectedRole (2*arity^(childExponent+1)) childResult ∧
      let afterBasisArray := basisArray stage (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisOccurrence true
        (returnedReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
      ∃ finalReached : Reached stage rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames ((returnedCursor entryReturned eventIndex (arity^(childExponent+1)))+(arity^(childExponent+1))) scalarPrefix
        (parentLive+2*arity^(childExponent+1)) pcStack stackOrigin savedCalls (canonical (replacementCaller returnedReached selectedRole afterBasisArray) returnedReached.aux),
        finalReached.data=replacementData returnedReached selectedRole afterBasisArray ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage rowCount logColumns precision passTime : ℝ)≤
          basisConstant*ActivePrefixStageInverseBudget.scale basisInput ∧
        ∃ elapsedSteps≤totalBudget,
          CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
            startPC initialBank elapsedSteps
            (CompactComplexScheduledPCLayout.callNextPC call)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready
              (canonical (replacementCaller returnedReached selectedRole afterBasisArray) returnedReached.aux))))

/-- Prepend an actual paid child-entry and execution path to the same
restored parent outcome, without changing any reached endpoint or data. -/
theorem append_outcome
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (returnScalar : ActiveRepairRankHeadersCommands.State)
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (startPC middlePC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2))
    (initialBank middleBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (prefixSteps prefixBudget suffixBudget : ℕ) (prefixBound : prefixSteps≤prefixBudget)
    (prefixExecution : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      startPC initialBank prefixSteps middlePC middleBank)
    (suffixOutcome : ReturnOutcome rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack
      childResult returnedBank returnScalar packingLimit basisProgram basisConstant guardPositive guardFitsChunk
      childRowsPositive parentSlots parentPacked middlePC middleBank suffixBudget) :
    ReturnOutcome rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack
      childResult returnedBank returnScalar packingLimit basisProgram basisConstant guardPositive guardFitsChunk
      childRowsPositive parentSlots parentPacked startPC initialBank (prefixBudget+suffixBudget) := by
  unfold ReturnOutcome at suffixOutcome ⊢
  dsimp only at suffixOutcome ⊢
  obtain ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,suffixSteps,suffixBound,suffixExecution⟩ := suffixOutcome
  refine ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,
    prefixSteps+suffixSteps,Nat.add_le_add prefixBound suffixBound,?_⟩
  exact FiniteFlowPath.append prefixExecution suffixExecution

/-- Extract the actual final canonical bank while result and nonleaf-return
banks are abstract. No physical endpoint equality is an input. -/
theorem extract_final_settled
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (childBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (returnScalar : ActiveRepairRankHeadersCommands.State)
    (olderWord : ℤ → Fin 6) (olderHead : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead)
    (snapshot : Snapshot stackCount) (parentSettled : Settled snapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : snapshot.headerStack=headerStack)
    (snapshotLiveStack : snapshot.liveStack=liveStack) (snapshotPcStack : snapshot.pcStack=pcStack)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
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
    (outcome : ReturnOutcome rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack
      childResult (CompactComplexAlignedPoppedReturnReadiness.popped childBank pcStack olderWord olderHead) returnScalar packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive
      parentSlots parentPacked startPC initialBank timeBudget) :
    ∃ (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
      (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (aux : Tapes 2 2),
      ∃ returnedReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+2*arity^(childExponent+1)) pcStack stackOrigin savedCalls
        (canonical (returnedCaller parentReached (CompactComplexRolePhaseSite.role call.site)
          (2*arity^(childExponent+1)) childResult control queue scalar tail storage) aux),
      returnedReached.data=returnedData parentReached (CompactComplexRolePhaseSite.role call.site)
        (2*arity^(childExponent+1)) childResult ∧
      let inverseArray := basisArray (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive parentSlots
        (CompactComplexRolePhaseSite.pc call.site) true
        (returnedReached.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)))
      ∃ finalReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+2*arity^(childExponent+1)) pcStack stackOrigin savedCalls
        (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
          returnedReached.aux),
      finalReached.data=replacementData returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray ∧
      finalReached.targetValue=parentReached.targetValue ∧
      Settled snapshot finalReached.storage finalReached.aux ∧
      ∃ elapsedSteps≤timeBudget,
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack startPC initialBank elapsedSteps
          (CompactComplexScheduledPCLayout.callNextPC call)
          (CleanSubbank.bank (Alphabet.mapTapes encoding
            (ready (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
              returnedReached.aux)))) := by
  unfold ReturnOutcome at outcome
  dsimp only at outcome
  obtain ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,elapsedSteps,timeBound,physical⟩ := outcome
  have framePreserved := CompactComplexAlignedReturnedDormantFrames.captured_final_settled parentReached
    (CompactComplexRolePhaseSite.role call.site) childBank olderWord olderHead olderAssociated
    headerStack liveStack snapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
    headerLiveDistinct pcHeaderDistinct pcLiveDistinct (2*arity^(childExponent+1)) (arity^(childExponent+1))
    rowCoordinate entryPath.visit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult)) childResult
    _ _ returnScalar _ returnedReached _ finalReached
  let restoredStorage := CompactComplexAlignedReturnedDormantFrames.capturedStorage parentReached
    (CompactComplexRolePhaseSite.role call.site) childBank olderWord olderHead headerStack liveStack
    (2*arity^(childExponent+1)) rowCoordinate entryPath.visit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult))
  have returnedFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields
    returnedReached _ parentReached.aux rfl
  have returnedStorage : returnedReached.storage=restoredStorage := by
    simpa only [restoredStorage,CompactComplexAlignedReturnedDormantFrames.capturedStorage,
      CompactComplexSourceReadyReachedReturnInvariant.returnedCaller,
      CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using returnedFields.1
  have finalFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields
    finalReached _ returnedReached.aux rfl
  have finalStorage : finalReached.storage=returnedReached.storage := by
    simpa only [CompactComplexSourceReadyReachedBasisInvariant.replacementCaller,
      CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using finalFields.1
  have targetPorts : restoredStorage.head ⟨8,by omega⟩=1 ∧
      restoredStorage.tape ⟨8,by omega⟩=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits parentReached.targetValue) := by
    unfold restoredStorage CompactComplexAlignedReturnedDormantFrames.capturedStorage
    constructor
    · exact (CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports _ _ _ _ _).2.2.1
    · exact (CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports _ _ _ _ _).2.2.2.1.trans
        (BinaryDescriptorStackRoundtrip.descriptor_encoded _)
  let retainedReached := { finalReached with
    targetValue := parentReached.targetValue
    target := by rw [finalStorage,returnedStorage]; exact targetPorts
    target_growth := parentReached.target_growth.trans
      (Nat.add_le_add_right (Nat.le_add_right parentLive (2*arity^(childExponent+1)))
        (2*arity^(childExponent+2))) }
  exact ⟨_,_,_,_,_,_,returnedReached,returnedData,retainedReached,finalData,rfl,
    framePreserved.2,elapsedSteps,timeBound,physical⟩

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafReturnFrame
