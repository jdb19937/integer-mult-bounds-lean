module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnPorts
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnGrid
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafReturnFrame
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafProgress
public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildReadiness
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget

/-! Actual nonleaf parent restoration and inverse basis from the same popped
completed child bank. Literal return ports, true-live Progress, and the tight
parent return grid are derived from actual frames, the real child trace, and
its exact tensor identity. No independent return-grid or physical-port oracle
is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadyCompletedChildBoundary (completed result)
open CompactComplexAlignedPoppedReturnReadiness (popped)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexCompletedLiveLower (schedule Event)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexSourceReadyNonleafReturnFrame (ReturnOutcome)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (address)
open Networks
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexRolePhaseSite.roleEncoding
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

section Parent
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
    parentLevels parentFrames parentReturned eventIndex parentPrefix parentLive finalLive eventElapsed : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    parentLevels parentFrames parentReturned)
  (activeFits : shape.active≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  {pcStack headerStack liveStack : Fin stackCount} {origin : ℤ} {savedCalls : List ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
    metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive parentLevels parentFrames
    (returnedCursor parentReturned eventIndex (arity^(childExponent+1))) parentPrefix parentLive pcStack origin savedCalls parentBank)
  (call : ComplexRecursiveCallSchema.Call)
  (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
  (initialChild : State (stage:=child phaseCoordinate parentPath.visit activeFits pair call.slot)
    (rowCount:=parentRows/roles) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=parentLevels+1) (frameVolume:=parentFrames+arity^(childExponent+2))
    (entryReturned:=parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1))
    (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls) 0 parentLive)
  (finalBoundary : FrameState (stage:=child phaseCoordinate parentPath.visit activeFits pair call.slot)
    (rowCount:=parentRows/roles) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=parentLevels+1) (frameVolume:=parentFrames+arity^(childExponent+2))
    (entryReturned:=parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1))
    (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls)
    (capture initialChild headerStack liveStack) initialChild.reached.targetValue schedule.length finalLive)
  (childTrace : Execution basisProgram headerStack liveStack parentLive initialChild finalBoundary.state eventElapsed)
  (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
  (childRowsDivisible : roles∣parentRows/roles)

include childTrace

/-- Every returned-child machine premise is derived on the actual completed
bank. The original basis witness and saved target Ledger remain genuine static
subroutine and numerical contracts. -/
theorem runs
    (initialEntryBank : initialChild.bank=canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent
        (child phaseCoordinate parentPath.visit activeFits pair call.slot) childSlots (parentRows/roles)
        polynomialExponent metadataPrecision parentLive childExponent childRowsDivisible
        (CompactComplexSourceReadyOrientationInvariants.oriented call (selectedArray parentReached call))
        (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        parentReached.scalar
        (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
      (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
    (actualChildTensor : ∀ (rawRow : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      nativeField (metadataPrecision-2*shape.bits) (parentLive+2*arity^(childExponent+1))
        (result finalBoundary.state.reached childSlots childRowsDivisible call) rawRow polynomialIndex globalAnchor=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^childExponent)).symm
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor
          (nativeField (metadataPrecision-2*shape.bits) parentLive (selectedArray parentReached call) rawRow polynomialIndex))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor)
      else ComplexEndpoints.fullFrame (arity^childExponent)
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor
          (nativeField (metadataPrecision-2*shape.bits) parentLive (selectedArray parentReached call) rawRow polynomialIndex))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor))
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (completedSettled : Settled
      (CompactComplexSourceReadyCapturedChildFrames.snapshot phaseCoordinate parentPath.visit activeFits pair parentReached call headerStack liveStack)
      finalBoundary.state.reached.storage finalBoundary.state.reached.aux)
    (older : ℤ → Fin 6) (top : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls older top)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (packingLimit : ℕ) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (rowsPositive : 0<parentRows) (childRowsPositive : 0<parentRows/roles) (rolesDivideRows : roles∣parentRows)
    (guardPositive : 1≤ shape.guard) (guardFitsChunk : shape.guard+1≤ shape.chunk) (axesPositive : 0<shape.axes)
    (chunkPositive : 0<shape.chunk) (activePositive : 0<shape.active) (unitPayload : shape.payload=1)
    (precisionReserve : baselinePrecision+2*shape.bits≤ metadataPrecision) (baselineFits : baselineLive≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤ shape.chunk)
    (axesFit : 0+2*arity^(childExponent+1)≤ shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤ shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedTargetLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      parentReached.targetValue ledgerLeft ledgerExponent)
    (parentSlots : (parent phaseCoordinate parentPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate parentPath.visit activeFits pair).slots),
      1<(parent phaseCoordinate parentPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
          (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) :
    let returnedBank := popped (completed finalBoundary.state.reached childSlots childRowsDivisible call) pcStack older top
    let resultArray := result finalBoundary.state.reached childSlots childRowsDivisible call
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
      (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput polynomialExponent
      (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots (CompactComplexRolePhaseSite.pc call.site) true
        (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent) (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ReturnOutcome phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack resultArray returnedBank
      finalBoundary.state.reached.scalar packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive
      parentSlots parentPacked (CompactComplexScheduledPCDecode.savedPC call)
      (CompactComplexAlignedBoundaryPaths.alignedBank
        ((CompactComplexSourceReadyWorkspace.ready returnedBank).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))
      (CompactComplexSourceReadyChildReturnPath.timeConstant roles*CompactNativeRoleTransferBudget.volume parentRows shape polynomialExponent metadataPrecision+1+
        CompactComplexActualCallRoleAlignment.cost roles (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision passTime+1) := by
  dsimp only
  let terminalReached := finalBoundary.state.reached
  let returnedBank := popped (completed terminalReached childSlots childRowsDivisible call) pcStack older top
  let resultArray := result terminalReached childSlots childRowsDivisible call
  have metadataFits : 2*shape.bits≤ metadataPrecision := by omega
  have initialTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    initialChild.reached childSlots parentLive childExponent childRowsDivisible
    (CompactComplexSourceReadyOrientationInvariants.oriented call (selectedArray parentReached call))
    (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    parentReached.scalar
    (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    initialEntryBank
  have terminalTarget : terminalReached.targetValue=parentLive+2*arity^(childExponent+1) :=
    finalBoundary.targetRetained.trans initialTarget
  have actualProgress := CompactComplexSourceReadyReachedNonleafProgress.progress
    parentPath call parentReached childTrace eventBound eventEquation precisionReserve baselineFits denominatorRoom
  have physicalPorts := CompactComplexSourceReadyNonleafChildReturnPorts.ready_ports
    phaseCoordinate parentPath.visit activeFits pair parentReached call headerStack liveStack terminalReached childSlots childRowsDivisible older top
    ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack completedSettled
    pcHeaderDistinct pcLiveDistinct headerLiveDistinct olderAssociated
  have resultWidth := CompactComplexAlignedCompletedReturnReadiness.completed_record_width
    terminalReached childSlots childRowsDivisible call metadataFits
  have resultGrid := CompactComplexSourceReadyNonleafChildReturnGrid.selected_return_grid parentReached call
    phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) metadataFits resultArray actualChildTensor
  have actualCurrent := physicalPorts.live
  rw [terminalTarget] at actualCurrent
  have childFitsNode : arity^(childExponent+1)≤ arity^(childExponent+2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have exponentRemaining : childExponent+2-1=childExponent+1 := by omega
  have actualReturn := CompactComplexAlignedSiblingJoinedPhysicalReturn.runs
    phaseCoordinate parentPath.visit activeFits pair call parentRows polynomialExponent metadataPrecision resultArray returnedBank
    headerStack pcStack liveStack headerLiveDistinct
    (parentReached.storage.tape (Fin.natAdd 10 headerStack)) (parentReached.storage.head (Fin.natAdd 10 headerStack))
    (childExponent+2) (by omega) childRowsPositive rolesDivideRows rfl guardPositive physicalPorts.rawSource
    physicalPorts.savedHeaders.2 physicalPorts.savedHeaders.1 physicalPorts.headerTailClean
    (by simpa only [exponentRemaining] using physicalPorts.exponent.2) physicalPorts.exponent.1
    (parentReached.storage.tape (Fin.natAdd 10 liveStack)) (parentReached.storage.head (Fin.natAdd 10 liveStack))
    parentLive finalLive (arity^(childExponent+1)) (2*arity^(childExponent+1)) actualProgress
    physicalPorts.savedLive.2 physicalPorts.savedLive.1 actualCurrent.2 actualCurrent.1 physicalPorts.targetBlank.2 physicalPorts.targetBlank.1
    physicalPorts.liveFrameClean baselinePrecision growthConstant 0 baselineLive parentLevels parentFrames parentReturned eventIndex parentPrefix origin
    savedCalls parentBank parentReached resultWidth (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) axesPositive chunkPositive
    physicalPorts.payloadStack physicalPorts.clock terminalReached.scalar physicalPorts.scalar
    (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) (parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount)))
    ledgerLive ledgerLeft ledgerExponent savedTargetLedger physicalPorts.savedTarget.2 physicalPorts.savedTarget.1 physicalPorts.targetFrameClean
    packingLimit basisProgram basisConstant basisRuns parentPath childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom
    le_rfl resultGrid guardFitsChunk rowsPositive unitPayload parentSlots parentPacked pcHeaderDistinct pcLiveDistinct
    physicalPorts.countBlank physicalPorts.control28Blank physicalPorts.control29Blank physicalPorts.olderHistory
  exact actualReturn

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnRun
