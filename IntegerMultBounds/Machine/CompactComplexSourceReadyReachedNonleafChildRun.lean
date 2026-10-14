module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyClassifiedStoppedNode
public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildReadiness
public import IntegerMultBounds.Machine.CompactComplexRecursivePathRows

/-! A genuine scheduled nonleaf child whose own children stop executes from
its actual entered bank through the full corrected node and saved-PC return.
Original child input readiness is extracted from the real parent bank and its
Settled frame; no child execution or semantic callback is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafChildRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexSourceReadyReachedStoppedSchedule (totalBudget)
open CompactComplexSourceReadyReachedStoppedNodeNormalizedValues (normalized)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactSpectatorInheritedGrid (Width Grid)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (address)
open Networks
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexRolePhaseSite.roleEncoding totalBudget

section Child
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft grandchildExponent parentLevels parentFrames parentReturned eventIndex parentRows polynomialExponent
    inputPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (grandchildExponent+3)
    parentLevels parentFrames parentReturned)
  (activeFits : shape.active≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
    (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) (grandchildExponent+3)
    baselinePrecision growthConstant 0 baselineLive parentLevels parentFrames
    (returnedCursor parentReturned eventIndex (arity^(grandchildExponent+2))) scalarPrefix parentLive
    pcStack origin savedCalls parentBank)
  (call : ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- All child input descriptors, widths, grid and tails follow from the actual
scheduled entry and the genuine parent frame; the returned bank is shared by
physical execution and its exact directional tensor semantics. -/
theorem exists_child_run
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=CompactComplexCompletedLiveLower.Event.child call)
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (parentRowsPadded : parentRows=CompactGlobalRowPadding.rowsAt roles arity shape.axes shape.chunk parentLevels)
    (activePositive : 0<shape.active)
    (nodeNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (grandchildExponent+2)=false)
    (grandchildrenStopped : ComplexRecursiveCallSchema.stopped shape.axes (grandchildExponent+1)=true)
    (axesFit : 0+arity^(grandchildExponent+1)≤ shape.bits)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+guardBits≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤ shape.chunk)
    (guardPositive : 1≤ shape.guard) (guardFitsChunk : shape.guard+1≤ shape.chunk) (unitPayload : shape.payload=1)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (childSlots : (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair).slots=25^3)
    (childPacked : ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair).slots),1 < (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair).f →
      ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (CompactComplexSourceReadyReachedBasisInvariant.input
            (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
            ((parentRows/roles)/roles) polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) guardPositive guardFitsChunk
            (by
              have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
                (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) (by omega) (by omega)
              rw [←parentRowsPadded] at rowGuards
              exact rowGuards.2.2.2.2.1)) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive≤ baselinePrecision) (growthReserve : CompactFramedScalarGrid.growthConstant≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤ shape.chunk)
    :
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsDivisible : roles∣parentRows/roles := by simpa only [←parentRowsPadded] using rowGuards.2.2.1
    let grandchildRowsPositive : 0<(parentRows/roles)/roles := by simpa only [←parentRowsPadded] using rowGuards.2.2.2.2.1
    ∃ initialState : State (stage:=parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair) (rowCount:=(parentRows/roles))
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=(parentLevels+1)) (frameVolume:=(parentFrames+arity^(grandchildExponent+3)))
      (entryReturned:=(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))) (childExponent:=grandchildExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::savedCalls)) 0 parentLive,
      initialState.bank=CompactComplexSourceReadyReachedEventInvariant.canonical
        (CompactComplexCorrectedEntryGeometryReadiness.permanent (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
          childSlots (parentRows/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          parentLive (grandchildExponent+1) childRowsDivisible (oriented call (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)) (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) parentReached.scalar (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
        (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
        (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair) childSlots (parentRows/roles) polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) childRowsDivisible (oriented call (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call))
        (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair) (rowCount:=(parentRows/roles))
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=(parentLevels+1)) (frameVolume:=(parentFrames+arity^(grandchildExponent+3)))
      (entryReturned:=(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))) (childExponent:=grandchildExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::savedCalls)) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ eventElapsed,
        Execution basisProgram headerStack liveStack parentLive initialState finalBoundary.state eventElapsed ∧
        eventElapsed ≤ totalBudget phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair packingLimit guardPositive guardFitsChunk
          grandchildRowsPositive childSlots childPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent parentLive (grandchildExponent+1) ≤ finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1) ≤ finalLive ∧
      ∃ older top elapsed,
        CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls older top ∧
        elapsed ≤ ((CompactComplexSourceReadyOrientationInvariants.constant+
          4*CompactComplexSourceReadyGuard.guardConstant+1)*
          CompactNativeRoleTransferBudget.volume (parentRows/roles) shape polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+1)+
          CompactComplexAlignedReachedNodeEntryPath.entryCost shape (parentRows/roles) polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
          totalBudget phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair packingLimit guardPositive guardFitsChunk
            grandchildRowsPositive childSlots childPacked+
          CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape) (parentRows/roles) polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
          (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5) ∧
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
          (CompactComplexAlignedBoundaryPaths.alignedBank
            ((CompactComplexSourceReadyWorkspace.ready
              (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
                parentReached call headerStack liveStack)).append
              (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) elapsed
          (CompactComplexScheduledPCDecode.savedPC call)
          (CompactComplexAlignedBoundaryPaths.alignedBank
            ((CompactComplexSourceReadyWorkspace.ready
              (CompactComplexAlignedPoppedReturnReadiness.popped
                (CompactComplexSourceReadyCompletedChildBoundary.completed finalBoundary.state.reached childSlots childRowsDivisible call)
                pcStack older top)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) ∧
        let resultBank := CompactComplexAlignedPoppedReturnReadiness.popped
          (CompactComplexSourceReadyCompletedChildBoundary.completed finalBoundary.state.reached childSlots childRowsDivisible call)
          pcStack older top
        let sourcePort := Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles))
        let resultArray := oriented call
          (normalized (parentRows/roles) polynomialExponent finalLive
            (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1)) childRowsDivisible
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
              childSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data))
        resultBank.head sourcePort=0 ∧
        resultBank.tape sourcePort=CompactSpectatorLeafAxis.word resultArray ∧
        Width shape (parentRows/roles) polynomialExponent inputPrecision resultArray ∧
        Grid shape (parentRows/roles) polynomialExponent inputPrecision
          (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1))
          (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (parentLevels+1)
            ((parentFrames+arity^(grandchildExponent+3))+2*(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2)))*4^(2*arity^(grandchildExponent+2))) resultArray ∧
        (∀ (rawRow : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          nativeField inputPrecision (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1))
            resultArray rawRow polynomialIndex globalAnchor =
          if call.inverse then (ComplexEndpoints.fullFrame (arity^(grandchildExponent+1))).symm
            (slice phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor
              (nativeField inputPrecision parentLive (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call) rawRow polynomialIndex))
            (address phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor)
          else ComplexEndpoints.fullFrame (arity^(grandchildExponent+1))
            (slice phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor
              (nativeField inputPrecision parentLive (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call) rawRow polynomialIndex))
            (address phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor)) := by
  dsimp only
  have metadataFits : 2*shape.bits≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  have baselineFitsPrecision : baselinePrecision≤ inputPrecision := by
    unfold ButterflyIndependentGuardHeaders.reservation at precisionReserve
    omega
  have actualEntry := CompactComplexSourceReadySiblingChildInvariant.scheduled_child_entered
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack
    pcHeaderDistinct pcLiveDistinct metadataFits growthReserve eventBound eventEquation
  have selectedWidth : Width shape (parentRows/roles) polynomialExponent inputPrecision (selectedArray parentReached call) := by
    simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using actualEntry.width
  have selectedGrid : Grid shape (parentRows/roles) polynomialExponent inputPrecision parentLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (parentLevels+1)
        (parentFrames+arity^(grandchildExponent+3)+2*(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))))
      (selectedArray parentReached call) := by
    simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using actualEntry.grid
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
    (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
  rw [←parentRowsPadded] at rowGuards
  have childRowsDivisible : roles∣parentRows/roles := rowGuards.2.2.1
  have childRowsPositive : 0<parentRows/roles := rowGuards.2.2.2.1
  have grandchildRowsPositive : 0<(parentRows/roles)/roles := rowGuards.2.2.2.2.1
  have initialLedger : parentLive≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive (parentLevels+1) (parentFrames+arity^(grandchildExponent+3))
      (parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))
      (CompactFramedScalarGrid.rows 0).length := by
    have enteredLedger : parentLive≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
        baselineLive (parentLevels+1) (parentFrames+arity^(grandchildExponent+3))
        (parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2)) 0 := by
      simpa only [Nat.add_assoc] using actualEntry.upper_ledger
    unfold CompactComplexDenominatorCapacity.ledger at enteredLedger ⊢
    omega
  have protectedTails := CompactComplexSourceReadyRecursiveChildCleanTails.original_protected_tails
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerLiveDistinct pcHeaderDistinct pcLiveDistinct
  have savedAssociation := actualEntry.saved_calls
  unfold CompactComplexSourceReadySavedCallHistory.Reached at savedAssociation
  have savedPorts := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack
    (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  dsimp only [CompactComplexSourceReadyScalarWorkspace.ready] at savedAssociation
  rw [CompactComplexSourceReadyWorkspace.ready_leaf] at savedAssociation
  rw [savedPorts.1,savedPorts.2] at savedAssociation
  have childResult := CompactComplexSourceReadyClassifiedStoppedNode.exists_classified_node_return
    call phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair
    packingLimit basisProgram basisConstant basisRuns headerStack liveStack (selectedArray parentReached call)
    selectedWidth selectedGrid baselineFitsPrecision
    (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    parentReached.scalar
    (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.count_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.current_ready phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.target_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.clock_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.auxiliary_free phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.exponent_ready phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.control28_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.control29_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    initialLedger savedAssociation pcHeaderDistinct pcLiveDistinct headerLiveDistinct protectedTails activePositive nodeNonstopped
    grandchildrenStopped axesFit childChunkRoom scalarChunkRoom guardPositive guardFitsChunk childRowsPositive grandchildRowsPositive
    childRowsDivisible unitPayload childSlots childPacked precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  have originalBankEquation := CompactComplexSourceReadyRecursiveChildReadiness.bank_eq_originalBank
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack
  change CompactComplexAlignedBoundaryPaths.alignedBank
      ((CompactComplexSourceReadyWorkspace.ready
        (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
          parentReached call headerStack liveStack)).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))=
      CompactComplexAlignedReachedNodeEntryPath.originalBank
        (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
        (parentRows/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
        (selectedArray parentReached call)
        (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        parentReached.scalar
        (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
      at originalBankEquation
  rw [←originalBankEquation] at childResult
  exact childResult

/-- Execute the actual entered nonleaf child using its own smaller-child
provider; input readiness and output semantics use the same physical banks. -/
theorem exists_child_run_of_provider
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=CompactComplexCompletedLiveLower.Event.child call)
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (parentRowsPadded : parentRows=CompactGlobalRowPadding.rowsAt roles arity shape.axes shape.chunk parentLevels)
    (activePositive : 0<shape.active)
    (nodeNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (grandchildExponent+2)=false)
    (axesFit : 0+arity^(grandchildExponent+1)≤ shape.bits)
    (nonstoppedAxesFit : ComplexRecursiveCallSchema.stopped shape.axes (grandchildExponent+1)=false →
      0+2*arity^(grandchildExponent+1) ≤ shape.bits)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+guardBits≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤ shape.chunk)
    (guardPositive : 1≤ shape.guard) (guardFitsChunk : shape.guard+1≤ shape.chunk) (unitPayload : shape.payload=1)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (childSlots : (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair).slots=25^3)
    (childPacked : ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair).slots),1 < (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair).f →
      ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (CompactComplexSourceReadyReachedBasisInvariant.input
            (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
            ((parentRows/roles)/roles) polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) guardPositive guardFitsChunk
            (by
              have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
                (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) (by omega) (by omega)
              rw [←parentRowsPadded] at rowGuards
              exact rowGuards.2.2.2.2.1)) operation) packingLimit)
    (grandchildSlots : ∀ grandchildCall : ComplexRecursiveCallSchema.Call,
      (CompactComplexChildHeadersData.child phaseCoordinate
        (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair grandchildCall.slot).slots=arity)
    (grandchildRowsDivisible : ComplexRecursiveCallSchema.stopped shape.axes (grandchildExponent+1)=false →
      roles∣(parentRows/roles)/roles)
    (grandchildEventBudget grandchildPathBudget : ComplexRecursiveCallSchema.Call → ℕ)
    (grandchildProvider : ∀ grandchildrenNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (grandchildExponent+1)=false,
      CompactComplexSourceReadyRecursiveChildProvider.Provider
      (parentRows:=parentRows/roles) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=(call::savedCalls))
      (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair basisProgram
      grandchildSlots (grandchildRowsDivisible grandchildrenNonstopped) grandchildEventBudget grandchildPathBudget)
    (precisionReserve : baselinePrecision+2*shape.bits≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive≤ baselinePrecision) (growthReserve : CompactFramedScalarGrid.growthConstant≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤ shape.chunk)
    :
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsDivisible : roles∣parentRows/roles := by simpa only [←parentRowsPadded] using rowGuards.2.2.1
    let grandchildRowsPositive : 0<(parentRows/roles)/roles := by simpa only [←parentRowsPadded] using rowGuards.2.2.2.2.1
    ∃ initialState : State (stage:=parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair) (rowCount:=(parentRows/roles))
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=(parentLevels+1)) (frameVolume:=(parentFrames+arity^(grandchildExponent+3)))
      (entryReturned:=(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))) (childExponent:=grandchildExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::savedCalls)) 0 parentLive,
      initialState.bank=CompactComplexSourceReadyReachedEventInvariant.canonical
        (CompactComplexCorrectedEntryGeometryReadiness.permanent (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
          childSlots (parentRows/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          parentLive (grandchildExponent+1) childRowsDivisible (oriented call (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)) (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) parentReached.scalar (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
        (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
        (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair) childSlots (parentRows/roles) polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) childRowsDivisible (oriented call (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call))
        (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair) (rowCount:=(parentRows/roles))
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=(parentLevels+1)) (frameVolume:=(parentFrames+arity^(grandchildExponent+3)))
      (entryReturned:=(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))) (childExponent:=grandchildExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::savedCalls)) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ eventElapsed,
        Execution basisProgram headerStack liveStack parentLive initialState finalBoundary.state eventElapsed ∧
        eventElapsed ≤ CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair packingLimit grandchildPathBudget guardPositive guardFitsChunk
          grandchildRowsPositive childSlots childPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent parentLive (grandchildExponent+1) ≤ finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1) ≤ finalLive ∧
      ∃ older top elapsed,
        CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls older top ∧
        elapsed ≤ ((CompactComplexSourceReadyOrientationInvariants.constant+
          4*CompactComplexSourceReadyGuard.guardConstant+1)*
          CompactNativeRoleTransferBudget.volume (parentRows/roles) shape polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+1)+
          CompactComplexAlignedReachedNodeEntryPath.entryCost shape (parentRows/roles) polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
          CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair packingLimit grandchildPathBudget guardPositive guardFitsChunk
            grandchildRowsPositive childSlots childPacked+
          CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape) (parentRows/roles) polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
          (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5) ∧
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
          (CompactComplexAlignedBoundaryPaths.alignedBank
            ((CompactComplexSourceReadyWorkspace.ready
              (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
                parentReached call headerStack liveStack)).append
              (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) elapsed
          (CompactComplexScheduledPCDecode.savedPC call)
          (CompactComplexAlignedBoundaryPaths.alignedBank
            ((CompactComplexSourceReadyWorkspace.ready
              (CompactComplexAlignedPoppedReturnReadiness.popped
                (CompactComplexSourceReadyCompletedChildBoundary.completed finalBoundary.state.reached childSlots childRowsDivisible call)
                pcStack older top)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) ∧
        let resultBank := CompactComplexAlignedPoppedReturnReadiness.popped
          (CompactComplexSourceReadyCompletedChildBoundary.completed finalBoundary.state.reached childSlots childRowsDivisible call)
          pcStack older top
        let sourcePort := Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles))
        let resultArray := oriented call
          (normalized (parentRows/roles) polynomialExponent finalLive
            (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1)) childRowsDivisible
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
              childSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data))
        resultBank.head sourcePort=0 ∧
        resultBank.tape sourcePort=CompactSpectatorLeafAxis.word resultArray ∧
        Width shape (parentRows/roles) polynomialExponent inputPrecision resultArray ∧
        Grid shape (parentRows/roles) polynomialExponent inputPrecision
          (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1))
          (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (parentLevels+1)
            ((parentFrames+arity^(grandchildExponent+3))+2*(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2)))*4^(2*arity^(grandchildExponent+2))) resultArray ∧
        (∀ (rawRow : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          nativeField inputPrecision (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1))
            resultArray rawRow polynomialIndex globalAnchor =
          if call.inverse then (ComplexEndpoints.fullFrame (arity^(grandchildExponent+1))).symm
            (slice phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor
              (nativeField inputPrecision parentLive (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call) rawRow polynomialIndex))
            (address phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor)
          else ComplexEndpoints.fullFrame (arity^(grandchildExponent+1))
            (slice phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor
              (nativeField inputPrecision parentLive (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call) rawRow polynomialIndex))
            (address phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit globalAnchor)) := by
  dsimp only
  have metadataFits : 2*shape.bits≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  have baselineFitsPrecision : baselinePrecision≤ inputPrecision := by
    unfold ButterflyIndependentGuardHeaders.reservation at precisionReserve
    omega
  have actualEntry := CompactComplexSourceReadySiblingChildInvariant.scheduled_child_entered
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack
    pcHeaderDistinct pcLiveDistinct metadataFits growthReserve eventBound eventEquation
  have selectedWidth : Width shape (parentRows/roles) polynomialExponent inputPrecision (selectedArray parentReached call) := by
    simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using actualEntry.width
  have selectedGrid : Grid shape (parentRows/roles) polynomialExponent inputPrecision parentLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (parentLevels+1)
        (parentFrames+arity^(grandchildExponent+3)+2*(parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))))
      (selectedArray parentReached call) := by
    simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using actualEntry.grid
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
    (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
  rw [←parentRowsPadded] at rowGuards
  have childRowsDivisible : roles∣parentRows/roles := rowGuards.2.2.1
  have childRowsPositive : 0<parentRows/roles := rowGuards.2.2.2.1
  have grandchildRowsPositive : 0<(parentRows/roles)/roles := rowGuards.2.2.2.2.1
  have initialLedger : parentLive≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive (parentLevels+1) (parentFrames+arity^(grandchildExponent+3))
      (parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2))
      (CompactFramedScalarGrid.rows 0).length := by
    have enteredLedger : parentLive≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
        baselineLive (parentLevels+1) (parentFrames+arity^(grandchildExponent+3))
        (parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(grandchildExponent+2)) 0 := by
      simpa only [Nat.add_assoc] using actualEntry.upper_ledger
    unfold CompactComplexDenominatorCapacity.ledger at enteredLedger ⊢
    omega
  have protectedTails := CompactComplexSourceReadyRecursiveChildCleanTails.original_protected_tails
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerLiveDistinct pcHeaderDistinct pcLiveDistinct
  have savedAssociation := actualEntry.saved_calls
  unfold CompactComplexSourceReadySavedCallHistory.Reached at savedAssociation
  have savedPorts := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack
    (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  dsimp only [CompactComplexSourceReadyScalarWorkspace.ready] at savedAssociation
  rw [CompactComplexSourceReadyWorkspace.ready_leaf] at savedAssociation
  rw [savedPorts.1,savedPorts.2] at savedAssociation
  have childResult := CompactComplexSourceReadyClassifiedStoppedNode.exists_classified_node_return_of_provider
    call phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call) activeFits pair
    packingLimit basisProgram basisConstant basisRuns headerStack liveStack (selectedArray parentReached call)
    selectedWidth selectedGrid baselineFitsPrecision
    (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    parentReached.scalar
    (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.count_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.current_ready phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.target_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.clock_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.auxiliary_free phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.exponent_ready phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.control28_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.control29_blank phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    initialLedger savedAssociation pcHeaderDistinct pcLiveDistinct headerLiveDistinct protectedTails activePositive nodeNonstopped
    axesFit nonstoppedAxesFit childChunkRoom scalarChunkRoom guardPositive guardFitsChunk childRowsPositive grandchildRowsPositive
    childRowsDivisible unitPayload childSlots childPacked grandchildSlots grandchildRowsDivisible grandchildEventBudget
    grandchildPathBudget grandchildProvider precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  have originalBankEquation := CompactComplexSourceReadyRecursiveChildReadiness.bank_eq_originalBank
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack
  change CompactComplexAlignedBoundaryPaths.alignedBank
      ((CompactComplexSourceReadyWorkspace.ready
        (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
          parentReached call headerStack liveStack)).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))=
      CompactComplexAlignedReachedNodeEntryPath.originalBank
        (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
        (parentRows/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
        (selectedArray parentReached call)
        (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        parentReached.scalar
        (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
      at originalBankEquation
  rw [←originalBankEquation] at childResult
  exact childResult

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafChildRun
