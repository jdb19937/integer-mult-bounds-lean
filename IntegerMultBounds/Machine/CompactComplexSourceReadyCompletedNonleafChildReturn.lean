module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChild
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnRun
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnGrid
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafReturnFrame
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafProgress
public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildReadiness
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget

/-! Consume an actual completed-child certificate and execute physical parent
restoration and inverse basis on the same aligned table. The child classifier,
full node execution, saved-PC pop and parent continuation form one paid path;
no separately supplied execution or tensor callback is needed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildReturn
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
open CompactComplexSourceReadyCompletedNonleafChild (resultArray returnedBank completed_settled)
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
    parentLevels parentFrames parentReturned eventIndex parentPrefix parentLive eventBudget pathBudget : ℕ}
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
  (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
  (childRowsDivisible : roles∣parentRows/roles)
  (certificate : CompactComplexSourceReadyCompletedNonleafChild.CompletedChild (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair
    parentReached call basisProgram childSlots childRowsDivisible eventBudget pathBudget)

/-- An actual completed child returns to its parent continuation with the
literal result, the real terminal scalar state, and both paid path budgets. -/
theorem runs
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
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
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
      (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput polynomialExponent
      (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots (CompactComplexRolePhaseSite.pc call.site) true
        (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent) (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ReturnOutcome phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack
      certificate.resultArray certificate.returnedBank certificate.finalBoundary.state.reached.scalar
      packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
      (CompactComplexAlignedBoundaryPaths.alignedBank
        ((CompactComplexSourceReadyWorkspace.ready
          (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
            parentReached call headerStack liveStack)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))
      (pathBudget+(CompactComplexSourceReadyChildReturnPath.timeConstant roles*
        CompactNativeRoleTransferBudget.volume parentRows shape polynomialExponent metadataPrecision+1+
        CompactComplexActualCallRoleAlignment.cost roles (parent phaseCoordinate parentPath.visit activeFits pair)
          parentRows polynomialExponent metadataPrecision passTime+1)) := by
  dsimp only
  have completedSettled := CompactComplexSourceReadyCompletedNonleafChild.completed_settled
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram certificate ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerLiveDistinct pcHeaderDistinct pcLiveDistinct
  have returnOutcome := CompactComplexSourceReadyNonleafChildReturnRun.runs phaseCoordinate parentPath activeFits pair
    parentReached call basisProgram certificate.initialChild certificate.finalBoundary certificate.childTrace
    childSlots childRowsDivisible certificate.initialEntryBank certificate.actualChildTensor
    ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack completedSettled
    certificate.older certificate.top certificate.olderAssociated eventBound eventEquation headerLiveDistinct pcHeaderDistinct pcLiveDistinct
    packingLimit basisConstant basisRuns rowsPositive childRowsPositive rolesDivideRows guardPositive guardFitsChunk axesPositive
    chunkPositive activePositive unitPayload precisionReserve baselineFits growthReserve denominatorRoom axesFit chunkRoom
    ledgerLive ledgerLeft ledgerExponent savedTargetLedger parentSlots parentPacked
  exact CompactComplexSourceReadyNonleafReturnFrame.append_outcome phaseCoordinate parentPath activeFits pair
    parentReached call headerStack liveStack certificate.resultArray certificate.returnedBank certificate.finalBoundary.state.reached.scalar
    packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
    _ _ _ _ certificate.elapsedSteps pathBudget _ certificate.pathTimeBound certificate.physical returnOutcome

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildReturn
