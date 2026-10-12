module

public import IntegerMultBounds.Machine.CompactComplexAlignedJoinedPhysicalReturn
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingReturnInvariant

/-! Original physical child return and inverse basis execute on the unchanged
aligned table after counted siblings. Promotion guard and capacity derive
from the real entry Path and actual schedule prefix, without an advanced Path. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedSiblingJoinedPhysicalReturn
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller canonical)
open CompactComplexSourceReadyReachedReturnInvariant (roleData returnedCaller returnedData returned_reached_from_path)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData basis_reached)
open CompactComplexAlignedChildReturnPath (liftedReturn liftedBank)
open CompactComplexAlignedReachedChildReturnPath (mid)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexNonleafRoleChildBank (storage current target control)
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexSourceReadyChildReturnPath
open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexNativeCodec (raw)
open CompactNativeRoleConjugatedPorts (encoding)
variable {extraTapes basisStates : ℕ} {shape : Shape} {nodeLeft childExponent : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

open CompactComplexSourceReadySiblingGuards (returnedCursor)

/-- Actual decoded return restores the parent then runs its original inverse
basis word with one fixed program witness; every join/table transition is paid. -/
theorem runs (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2))
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) (parentRows polynomialExponent metadataPrecision : ℕ) (childResult : CompactSpectatorVisitGeometry.Array shape (parentRows/roles) polynomialExponent)
    (returnedChildBank : Tapes (CompactComplexNonleafRoleChildBank.tapes extraTapes roles) 2)
    (headerStack pcStack liveStack : Fin extraTapes) (headerLiveDistinct : headerStack≠liveStack)
    (headerFrame : ℤ → Fin 6) (headerHead : ℤ) (nodeExponent : ℕ) (nodeExponentPositive : 0<nodeExponent) (childRowsPositive : 0<parentRows/roles) (rolesDivideRows : roles ∣ parentRows) (nodeExponentEquation : nodeExponent=childExponent+2) (guardPositive : 1≤shape.guard)
    (childSourceBank : Placement.active placement returnedChildBank=
      CompactNativeRoleOriginal.bank (raw (child phaseCoordinate visit activeFits pair call.slot) (parentRows/roles) polynomialExponent metadataPrecision) (CompactNativeRoleReservedBridge.sourcePayload shape (parentRows/roles) polynomialExponent childResult roles))
    (headerStackWord : returnedChildBank.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames headerFrame headerHead
      (CompactComplexControllerChildPrefix.data (parent phaseCoordinate visit activeFits pair)))
    (headerStackHead : returnedChildBank.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top headerHead
      (CompactComplexControllerChildPrefix.data (parent phaseCoordinate visit activeFits pair)))
    (headerTailClean : ∀ z,headerHead≤z → headerFrame z=blank)
    (childExponentWord : returnedChildBank.tape (control 1)=BinaryDescriptorStack.descriptor (bits (nodeExponent-1))) (childExponentHead : returnedChildBank.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive childCurrent childVolume denominatorAdvance : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress shape metadataPrecision parentLive childCurrent (parentLive+denominatorAdvance))
    (savedLiveWord : returnedChildBank.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (savedLiveHead : returnedChildBank.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (returnedLiveWord : returnedChildBank.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+denominatorAdvance))) (returnedLiveHead : returnedChildBank.head current=1)
    (childTargetBlank : returnedChildBank.tape target=(fun _ => blank)) (childTargetHead : returnedChildBank.head target=0)
    (liveFrameClean : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume entryReturned eventIndex scalarPrefix : ℕ) (origin : ℤ)
    (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (parentBank : Tapes (nodeTapes extraTapes roles) 2)
    (parentReached : Reached (parent phaseCoordinate visit activeFits pair) parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes
      baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex childVolume) scalarPrefix parentLive pcStack origin calls parentBank)
    (childWidth : ∀ selectedRole,(childResult selectedRole).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
      (childResult selectedRole).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision)
    (rolesPositive : 0<roles) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (payloadStackPort : returnedChildBank.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape parentRows polynomialExponent metadataPrecision
          (parent phaseCoordinate visit activeFits pair).rho (parent phaseCoordinate visit activeFits pair).left
          (parent phaseCoordinate visit activeFits pair).f (parent phaseCoordinate visit activeFits pair).slots
          (parent phaseCoordinate visit activeFits pair).right (parent phaseCoordinate visit activeFits pair).source.val
          (parent phaseCoordinate visit activeFits pair).target.val (caller parentReached)).head CompactComplexNonleafRoleEntry.stack ∧
      returnedChildBank.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape parentRows polynomialExponent metadataPrecision
          (parent phaseCoordinate visit activeFits pair).rho (parent phaseCoordinate visit activeFits pair).left
          (parent phaseCoordinate visit activeFits pair).f (parent phaseCoordinate visit activeFits pair).slots
          (parent phaseCoordinate visit activeFits pair).right (parent phaseCoordinate visit activeFits pair).source.val
          (parent phaseCoordinate visit activeFits pair).target.val (caller parentReached)).tape CompactComplexNonleafRoleEntry.stack)
    (clockBlank : returnedChildBank.head (extra 1)=0 ∧ returnedChildBank.tape (extra 1)=fun _ => blank)
    (scalar : State) (scalarBankPort : scalarPart returnedChildBank=ActiveRepairRankHeadersCommands.bank scalar)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive parentReached.targetValue ledgerLeft ledgerExponent)
    (targetStackWord : (storagePart returnedChildBank).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits parentReached.targetValue))
    (targetStackHead : (storagePart returnedChildBank).head ⟨9,by omega⟩=targetHead+1+(bits parentReached.targetValue).length)
    (targetFrameClean : ∀ z,targetHead≤z → z<targetHead+1+(bits parentReached.targetValue).length → targetFrame z=blank)
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStates prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStates basisProgram basisConstant)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes+denominatorAdvance≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (advanceFits : denominatorAdvance≤2*childVolume)
    (childGrid : CompactSpectatorInheritedGrid.Grid shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentLive+denominatorAdvance)
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*((returnedCursor entryReturned eventIndex childVolume)+childVolume)+completedAxes))) childResult)
    (guardFitsChunk : shape.guard+1≤shape.chunk) (rowsPositive : 0<parentRows) (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate visit activeFits pair).slots=25^3)
    (parentPacked : ∀ op,1<(parent phaseCoordinate visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate visit activeFits pair)
          (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) op) packingLimit)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (countBlank : (storagePart returnedChildBank).head 0=0 ∧ (storagePart returnedChildBank).tape 0=(fun _ => blank))
    (control28Blank : (controlPart returnedChildBank).head 28=0 ∧ (controlPart returnedChildBank).tape 28=(fun _ => blank))
    (control29Blank : (controlPart returnedChildBank).head 29=0 ∧ (controlPart returnedChildBank).tape 29=(fun _ => blank))
    (savedHistory : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart returnedChildBank).tape (Fin.natAdd 10 pcStack)) ((storagePart returnedChildBank).head (Fin.natAdd 10 pcStack))) :

    let stage := parent phaseCoordinate visit activeFits pair
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let middle := mid selectedRole (caller parentReached) returnedChildBank headerStack liveStack headerFrame headerHead liveFrame liveHead nodeExponent parentLive (parentLive+denominatorAdvance)
      phaseCoordinate visit activeFits pair parentRows polynomialExponent metadataPrecision (CompactNativeRoleReservedBridge.sourcePayload shape (parentRows/roles) polynomialExponent childResult roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult))
    let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
      (parentLive+denominatorAdvance) targetFrame targetHead parentReached.targetValue
    let start := canonical (returnedCaller parentReached selectedRole denominatorAdvance childResult (controlPart middle) (queuePart middle)
      scalar (tailPart middle) nextStorage) parentReached.aux
    let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d polynomialExponent
      (CompactComplexActualCallAlignment.nativeCost packingLimit d parentSlots basisPC true
        (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent) (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ restoredParent : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume ((returnedCursor entryReturned eventIndex childVolume)+childVolume) scalarPrefix
      (parentLive+denominatorAdvance) pcStack origin calls start,
      restoredParent.data=returnedData parentReached selectedRole denominatorAdvance childResult ∧
      let after := basisArray stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive parentSlots basisPC true
        (restoredParent.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
      ∃ final : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume ((returnedCursor entryReturned eventIndex childVolume)+childVolume) scalarPrefix
        (parentLive+denominatorAdvance) pcStack origin calls (canonical (replacementCaller restoredParent selectedRole after) restoredParent.aux),
        final.data=replacementData restoredParent selectedRole after ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent metadataPrecision passTime : ℝ)≤
          basisConstant*ActivePrefixStageInverseBudget.scale d ∧
        ∃ time≤timeConstant roles*CompactNativeRoleTransferBudget.volume parentRows shape polynomialExponent metadataPrecision+1+
          CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent metadataPrecision passTime+1,
          CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
            (CompactComplexScheduledPCDecode.savedPC call)
            (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedChildBank
              (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2))) time
            (CompactComplexScheduledPCLayout.callNextPC call)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready
              (canonical (replacementCaller restoredParent selectedRole after) restoredParent.aux)))) := by
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have promotion := CompactComplexSourceReadySiblingReturnInvariant.promotion_guard entryPath eventIndex childVolume scalarPrefix
    baselinePrecision growthConstant completedAxes denominatorAdvance metadataPrecision childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom
  exact CompactComplexAlignedJoinedPhysicalReturn.runs_with_guard phaseCoordinate visit activeFits pair call parentRows polynomialExponent metadataPrecision childResult returnedChildBank
    headerStack pcStack liveStack headerLiveDistinct headerFrame headerHead nodeExponent nodeExponentPositive childRowsPositive rolesDivideRows nodeExponentEquation guardPositive childSourceBank headerStackWord headerStackHead headerTailClean childExponentWord childExponentHead
    liveFrame liveHead parentLive childCurrent childVolume denominatorAdvance progress savedLiveWord savedLiveHead returnedLiveWord returnedLiveHead
    childTargetBlank childTargetHead liveFrameClean baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex childVolume) scalarPrefix origin calls parentBank parentReached childWidth rolesPositive axesPositive chunkPositive
    payloadStackPort clockBlank scalar scalarBankPort targetFrame targetHead ledgerLive ledgerLeft ledgerExponent ledger
    targetStackWord targetStackHead targetFrameClean packingLimit basisProgram basisConstant basisRuns metadataFits promotion.1 promotion.2 advanceFits childGrid
    guardFitsChunk rowsPositive unitPayload parentSlots parentPacked pcHeaderDistinct pcLiveDistinct countBlank control28Blank control29Blank savedHistory

end
end IntegerMultBounds.Machine.CompactComplexAlignedSiblingJoinedPhysicalReturn
