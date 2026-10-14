module

public import IntegerMultBounds.Machine.CompactNativePolynomialStagePacked
public import IntegerMultBounds.Machine.CompactComplexLargeAxesStop
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChild
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafChildRun
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget

/-! Construct a completed nonleaf child certificate from the actual stopped-
grandchild execution theorem. The result array, saved-PC endpoint and tensor
identity all come from the same reached terminal bank. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren
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

open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
/-- The already paid classifier, corrected entry, actual event schedule,
finalization and saved-PC pop bound, with the schedule charge abstracted. -/
def pathBudget (shape : Shape) (rows ell metadataPrecision eventBudget : ℕ) :=
  ((CompactComplexSourceReadyOrientationInvariants.constant+4*CompactComplexSourceReadyGuard.guardConstant+1)*
    CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+1)+
  CompactComplexAlignedReachedNodeEntryPath.entryCost shape rows ell metadataPrecision+eventBudget+
  CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape) rows ell metadataPrecision+
  (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)

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

theorem exists_completed_child
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
    let eventBudget := totalBudget phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call)
      activeFits pair packingLimit guardPositive guardFitsChunk grandchildRowsPositive childSlots childPacked
    Nonempty (CompactComplexSourceReadyCompletedNonleafChild.CompletedChild
      (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget
      (pathBudget shape (parentRows/roles) polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) eventBudget)) := by
  dsimp only
  obtain ⟨initialState,entryBank,entryData,finalLive,finalBoundary,eventElapsed,childTrace,eventTimeBound,
      minimumCoverage,targetCoverage,older,top,childElapsed,olderAssociated,childTimeBound,childPath,
      sourceHead,sourceWord,childWidth,childGrid,childTensor⟩ :=
    CompactComplexSourceReadyReachedNonleafChildRun.exists_child_run phaseCoordinate parentPath activeFits pair
      parentReached call headerStack liveStack packingLimit basisProgram basisConstant basisRuns eventBound eventEquation
      ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack pcHeaderDistinct pcLiveDistinct
      headerLiveDistinct parentRowsPadded activePositive nodeNonstopped grandchildrenStopped axesFit childChunkRoom
      scalarChunkRoom guardPositive guardFitsChunk unitPayload axesPositive chunkPositive childSlots childPacked precisionReserve
      baselineFits growthReserve denominatorRoom
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
    (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
  rw [←parentRowsPadded] at rowGuards
  have childRowsDivisible : roles∣parentRows/roles := rowGuards.2.2.1
  have initialTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    initialState.reached childSlots parentLive (grandchildExponent+1) childRowsDivisible
    (oriented call (selectedArray parentReached call))
    (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    parentReached.scalar
    (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    entryBank
  have terminalTarget : finalBoundary.state.reached.targetValue=parentLive+2*arity^(grandchildExponent+2) :=
    finalBoundary.targetRetained.trans initialTarget
  have resultEquation : CompactComplexSourceReadyCompletedChildBoundary.result
      finalBoundary.state.reached childSlots childRowsDivisible call=
    oriented call (normalized (parentRows/roles) polynomialExponent finalLive
      (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1)) childRowsDivisible
      (CompactComplexSinkSliceValues.scalarOutputRoles
        (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
        childSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) := by
    unfold CompactComplexSourceReadyCompletedChildBoundary.result
    rw [CompactComplexSourceReadyNormalizedBoundary.joined_eq_normalized,terminalTarget]
    rfl
  let traceWitness := CompactComplexSourceReadyCompletedNonleafChild.TraceWitness.make
    (childSlots:=childSlots) (childRowsDivisible:=childRowsDivisible)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram
    initialState finalLive finalBoundary eventElapsed childTrace eventTimeBound entryBank
  refine ⟨CompactComplexSourceReadyCompletedNonleafChild.CompletedChild.make
    (childSlots:=childSlots) (childRowsDivisible:=childRowsDivisible)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram
    traceWitness older top olderAssociated childElapsed childTimeBound childPath ?_⟩
  intro rawRow polynomialIndex globalAnchor
  dsimp only [traceWitness, CompactComplexSourceReadyCompletedNonleafChild.TraceWitness.make,
    CompactComplexSourceReadyCompletedNonleafChild.TraceWitness.finalBoundary]
  have outputConversion := congrArg
    (fun coefficients : CompactSpectatorVisitGeometry.Array shape (parentRows/roles) polynomialExponent =>
      nativeField inputPrecision (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1))
        coefficients rawRow polynomialIndex globalAnchor) resultEquation
  have computedTensor := outputConversion.trans (childTensor rawRow polynomialIndex globalAnchor)
  simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel,
    CompactComplexDenominatorPolicy.networkTarget,CompactComplexChildHeadersData.parent,
    CompactComplexChildHeadersData.child] using computedTensor

/-- Build the same computed completed-child certificate from an actual
provider-driven recursive execution and its literal physical return. -/
theorem exists_completed_child_of_provider
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
    let eventBudget := CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call)
      activeFits pair packingLimit grandchildPathBudget guardPositive guardFitsChunk grandchildRowsPositive childSlots childPacked
    Nonempty (CompactComplexSourceReadyCompletedNonleafChild.CompletedChild
      (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget
      (pathBudget shape (parentRows/roles) polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) eventBudget)) := by
  dsimp only
  obtain ⟨initialState,entryBank,entryData,finalLive,finalBoundary,eventElapsed,childTrace,eventTimeBound,
      minimumCoverage,targetCoverage,older,top,childElapsed,olderAssociated,childTimeBound,childPath,
      sourceHead,sourceWord,childWidth,childGrid,childTensor⟩ :=
    CompactComplexSourceReadyReachedNonleafChildRun.exists_child_run_of_provider phaseCoordinate parentPath activeFits pair
      parentReached call headerStack liveStack packingLimit basisProgram basisConstant basisRuns eventBound eventEquation
      ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack pcHeaderDistinct pcLiveDistinct
      headerLiveDistinct parentRowsPadded activePositive nodeNonstopped axesFit nonstoppedAxesFit childChunkRoom
      scalarChunkRoom guardPositive guardFitsChunk unitPayload axesPositive chunkPositive childSlots childPacked
      grandchildSlots grandchildRowsDivisible grandchildEventBudget grandchildPathBudget grandchildProvider precisionReserve
      baselineFits growthReserve denominatorRoom
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards parentPath activeFits roles shape.chunk
    (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
  rw [←parentRowsPadded] at rowGuards
  have childRowsDivisible : roles∣parentRows/roles := rowGuards.2.2.1
  have initialTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    initialState.reached childSlots parentLive (grandchildExponent+1) childRowsDivisible
    (oriented call (selectedArray parentReached call))
    (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    parentReached.scalar
    (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    entryBank
  have terminalTarget : finalBoundary.state.reached.targetValue=parentLive+2*arity^(grandchildExponent+2) :=
    finalBoundary.targetRetained.trans initialTarget
  have resultEquation : CompactComplexSourceReadyCompletedChildBoundary.result
      finalBoundary.state.reached childSlots childRowsDivisible call=
    oriented call (normalized (parentRows/roles) polynomialExponent finalLive
      (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1)) childRowsDivisible
      (CompactComplexSinkSliceValues.scalarOutputRoles
        (parent phaseCoordinate (CompactRecursiveDependencyBudget.Path.child parentPath call).visit activeFits pair)
        childSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) := by
    unfold CompactComplexSourceReadyCompletedChildBoundary.result
    rw [CompactComplexSourceReadyNormalizedBoundary.joined_eq_normalized,terminalTarget]
    rfl
  let traceWitness := CompactComplexSourceReadyCompletedNonleafChild.TraceWitness.make
    (childSlots:=childSlots) (childRowsDivisible:=childRowsDivisible)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram
    initialState finalLive finalBoundary eventElapsed childTrace eventTimeBound entryBank
  refine ⟨CompactComplexSourceReadyCompletedNonleafChild.CompletedChild.make
    (childSlots:=childSlots) (childRowsDivisible:=childRowsDivisible)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram
    traceWitness older top olderAssociated childElapsed childTimeBound childPath ?_⟩
  intro rawRow polynomialIndex globalAnchor
  dsimp only [traceWitness, CompactComplexSourceReadyCompletedNonleafChild.TraceWitness.make,
    CompactComplexSourceReadyCompletedNonleafChild.TraceWitness.finalBoundary]
  have outputConversion := congrArg
    (fun coefficients : CompactSpectatorVisitGeometry.Array shape (parentRows/roles) polynomialExponent =>
      nativeField inputPrecision (CompactComplexDenominatorPolicy.networkTarget parentLive (grandchildExponent+1))
        coefficients rawRow polynomialIndex globalAnchor) resultEquation
  have computedTensor := outputConversion.trans (childTensor rawRow polynomialIndex globalAnchor)
  simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel,
    CompactComplexDenominatorPolicy.networkTarget,CompactComplexChildHeadersData.parent,
    CompactComplexChildHeadersData.child] using computedTensor

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactGlobalRowPadding (rowsAt)
open CompactRecursiveDependencyBudget (Path)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget
  CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget

section Static
variable {stackCount basisStateCount : ℕ} {shape : Shape}
    (phaseCoordinate : Fin shape.chunk) (activeFits : shape.active ≤ shape.axes)
    (pair : BinaryRowProgram.Op (Fin arity))
    (polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit : ℕ)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard+1 ≤ shape.chunk)

/-- All descendant packing follows the original genuine dependency geometry.
No packing contract can depend on a live counter, bank or coefficient array. -/
def PackingFamily : Prop :=
  ∀ {nodeLeft childExponent dependencyLevels frameVolume returnedVolume : ℕ}
    (path : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume returnedVolume)
    (rowCount : ℕ)
    (_rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels)
    (roleRowsPositive : 0 < rowCount/roles),
    ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate path.visit activeFits pair).slots),
      1 < (parent phaseCoordinate path.visit activeFits pair).f →
      ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate path.visit activeFits pair)
            (rowCount/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
            guardPositive guardFitsChunk roleRowsPositive) operation) packingLimit

variable (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount)

/-- The budget functions precede every actual stack history and every dynamic
forward bank quantified by Provider. Static geometry alone indexes the costs. -/
def UniformProvider {nodeLeft childExponent dependencyLevels frameVolume returnedVolume rowCount : ℕ}
    (path : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume returnedVolume)
    (childRowsDivisible : roles ∣ rowCount/roles)
    (eventBudget pathBudget : ComplexRecursiveCallSchema.Call → ℕ) : Prop :=
  ∀ (origin : ℤ) (savedCalls : List ComplexRecursiveCallSchema.Call),
    CompactComplexSourceReadyRecursiveChildProvider.Provider
      (parentRows:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate path activeFits pair basisProgram (fun _ => rfl) childRowsDivisible eventBudget pathBudget

/-- A runtime-free predicate on the static genuine node context and the
chosen event/path budgets. It cannot inspect a bank, live value or stack history. -/
abbrev BudgetInvariant (shape : Shape) :=
  ∀ {nodeLeft childExponent dependencyLevels frameVolume returnedVolume rowCount : ℕ},
    (path : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume returnedVolume) →
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels) →
    (ComplexRecursiveCallSchema.Call → ℕ) → (ComplexRecursiveCallSchema.Call → ℕ) → Prop

/-- Pure closure of a static budget invariant under the exact recurrence used
by the completed-child producer. All choices remain outside runtime contexts. -/
def SuccessorBudgetInvariant
    (chunkPositive : 0 < shape.chunk)
    (packingFamily : PackingFamily phaseCoordinate activeFits pair polynomialExponent inputPrecision packingLimit
      guardPositive guardFitsChunk)
    (invariant : BudgetInvariant shape) : Prop :=
  ∀ {nodeLeft smallerExponent dependencyLevels frameVolume returnedVolume rowCount : ℕ}
    (path : Path shape.active nodeLeft (smallerExponent+3) dependencyLevels frameVolume returnedVolume)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels)
    (smallerEventBudget smallerPathBudget : ComplexRecursiveCallSchema.Call → ComplexRecursiveCallSchema.Call → ℕ),
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards path activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsPadded : rowCount/roles=rowsAt roles arity shape.axes shape.chunk (dependencyLevels+1) := by
      rw [rowsPadded]
      exact rowGuards.2.2.2.2.2.1
    let childRoleRowsPositive : 0 < (rowCount/roles)/roles := by
      rw [rowsPadded]
      exact rowGuards.2.2.2.2.1
    let childSlots : ∀ call : ComplexRecursiveCallSchema.Call,
        (parent phaseCoordinate (Path.child path call).visit activeFits pair).slots=25^3 := fun _ => rfl
    let childPacked := fun call : ComplexRecursiveCallSchema.Call =>
      packingFamily (Path.child path call) (rowCount/roles) childRowsPadded childRoleRowsPositive
    let eventBudget : ComplexRecursiveCallSchema.Call → ℕ := fun call =>
      CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate (Path.child path call) activeFits pair
        packingLimit (smallerPathBudget call) guardPositive guardFitsChunk childRoleRowsPositive (childSlots call) (childPacked call)
    let returnPathBudget : ComplexRecursiveCallSchema.Call → ℕ := fun call =>
      CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget shape (rowCount/roles)
        polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) (eventBudget call)
    (∀ call : ComplexRecursiveCallSchema.Call,
      invariant (Path.child path call) childRowsPadded (smallerEventBudget call) (smallerPathBudget call)) →
    invariant path rowsPadded eventBudget returnPathBudget

/-- Fixed budgets and a real recursive Provider exist by ordinary exponent
induction. Exponent-one nodes stop under the original strict large-axis test;
every successor certificate is built from the smaller genuine child Path. -/
theorem exists_fixed_provider_with_budget_invariant
    (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (largeAxes : arity^1000 < shape.axes) (activePositive : 0 < shape.active)
    (axesPositive : 0 < shape.axes) (chunkPositive : 0 < shape.chunk) (unitPayload : shape.payload=1)
    (packingFamily : PackingFamily phaseCoordinate activeFits pair polynomialExponent inputPrecision packingLimit
      guardPositive guardFitsChunk)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+guardBits ≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits ≤ shape.chunk)
    (precisionReserve : baselinePrecision+2*shape.bits ≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive ≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk)
    (invariant : BudgetInvariant shape)
    (baseInvariant : ∀ {nodeLeft dependencyLevels frameVolume returnedVolume rowCount : ℕ}
      (path : Path shape.active nodeLeft (0+2) dependencyLevels frameVolume returnedVolume)
      (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels),
      invariant path rowsPadded (fun _ => 0) (fun _ => 0))
    (successorInvariant : SuccessorBudgetInvariant phaseCoordinate activeFits pair polynomialExponent inputPrecision
      packingLimit guardPositive guardFitsChunk chunkPositive packingFamily invariant)
    (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume returnedVolume rowCount : ℕ}
    (path : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume returnedVolume)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels) :
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards path activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsDivisible : roles ∣ rowCount/roles := by
      rw [rowsPadded]
      exact rowGuards.2.2.1
    ∃ eventBudget pathBudget : ComplexRecursiveCallSchema.Call → ℕ,
      UniformProvider phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision growthConstant
        baselineLive basisProgram headerStack pcStack liveStack path childRowsDivisible eventBudget pathBudget ∧
      invariant path rowsPadded eventBudget pathBudget := by
  induction childExponent generalizing nodeLeft dependencyLevels frameVolume returnedVolume rowCount with
  | zero =>
    dsimp only
    refine ⟨fun _ => 0,fun _ => 0,?_,baseInvariant path rowsPadded⟩
    intro origin savedCalls eventIndex parentLive forwardBank forwardReached call eventBound eventEquation childNonstopped
    have stoppedOne := CompactComplexLargeAxesStop.one_stopped shape.axes largeAxes
    have classifierConflict : true=false := stoppedOne.symm.trans childNonstopped
    cases classifierConflict
  | succ smallerExponent inductionHypothesis =>
    dsimp only
    have rolesPositive : 0 < roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
    have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards path activeFits roles shape.chunk
      rolesPositive chunkPositive (by omega)
    have childRowsPadded : rowCount/roles=rowsAt roles arity shape.axes shape.chunk (dependencyLevels+1) := by
      rw [rowsPadded]
      exact rowGuards.2.2.2.2.2.1
    have childRoleRowsPositive : 0 < (rowCount/roles)/roles := by
      rw [rowsPadded]
      exact rowGuards.2.2.2.2.1
    let childSlots : ∀ call : ComplexRecursiveCallSchema.Call,
        (parent phaseCoordinate (Path.child path call).visit activeFits pair).slots=25^3 := fun _ => rfl
    let childPacked (call : ComplexRecursiveCallSchema.Call) :=
      packingFamily (Path.child path call) (rowCount/roles) childRowsPadded childRoleRowsPositive
    have smallerProviders (call : ComplexRecursiveCallSchema.Call) :=
      inductionHypothesis (Path.child path call) childRowsPadded
    let smallerEventBudget (call : ComplexRecursiveCallSchema.Call) := Classical.choose (smallerProviders call)
    let smallerPathBudget (call : ComplexRecursiveCallSchema.Call) :=
      Classical.choose (Classical.choose_spec (smallerProviders call))
    let eventBudget : ComplexRecursiveCallSchema.Call → ℕ := fun call =>
      CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate (Path.child path call) activeFits pair
        packingLimit (smallerPathBudget call) guardPositive guardFitsChunk childRoleRowsPositive (childSlots call) (childPacked call)
    let returnPathBudget : ComplexRecursiveCallSchema.Call → ℕ := fun call =>
      CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget shape (rowCount/roles)
        polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) (eventBudget call)
    refine ⟨eventBudget,returnPathBudget,?_,?_⟩
    · intro origin savedCalls eventIndex parentLive forwardBank forwardReached call eventBound eventEquation childNonstopped
        ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
        headerLiveDistinct pcHeaderDistinct pcLiveDistinct
      have grandchildGuards := CompactComplexRecursivePathRows.grandchild_row_guards path activeFits roles shape.chunk
        rolesPositive chunkPositive rowsPadded call
      let grandchildSlots : ∀ grandchildCall : ComplexRecursiveCallSchema.Call,
          (child phaseCoordinate (Path.child path call).visit activeFits pair grandchildCall.slot).slots=arity := fun _ => rfl
      let grandchildRowsDivisible : ComplexRecursiveCallSchema.stopped shape.axes (smallerExponent+1)=false →
          roles ∣ (rowCount/roles)/roles := fun _ => grandchildGuards.1
      have grandchildProvider : ∀ grandchildrenNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (smallerExponent+1)=false,
          CompactComplexSourceReadyRecursiveChildProvider.Provider
            (parentRows:=rowCount/roles) (polynomialExponent:=polynomialExponent)
            (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
            (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
            (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls) (headerStack:=headerStack) (liveStack:=liveStack)
            phaseCoordinate (Path.child path call) activeFits pair basisProgram grandchildSlots
            (grandchildRowsDivisible grandchildrenNonstopped) (smallerEventBudget call) (smallerPathBudget call) := by
        intro grandchildrenNonstopped
        exact (Classical.choose_spec (Classical.choose_spec (smallerProviders call))).1 origin (call::savedCalls)
      have doubleChildFit := CompactComplexRecursivePathRows.two_child_volumes_fit (Path.child path call) chunkPositive
      have singleChildFit : 0+arity^(smallerExponent+1) ≤ shape.bits := by omega
      have completed := CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.exists_completed_child_of_provider
        phaseCoordinate path activeFits pair forwardReached call headerStack liveStack packingLimit basisProgram basisConstant basisRuns
        eventBound eventEquation ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
        pcHeaderDistinct pcLiveDistinct headerLiveDistinct rowsPadded activePositive childNonstopped singleChildFit
        (fun _ => doubleChildFit) childChunkRoom scalarChunkRoom guardPositive guardFitsChunk unitPayload axesPositive chunkPositive
        (childSlots call) (childPacked call) grandchildSlots grandchildRowsDivisible
        (smallerEventBudget call) (smallerPathBudget call) grandchildProvider precisionReserve baselineFits growthReserve denominatorRoom
      exact completed
    · apply successorInvariant path rowsPadded smallerEventBudget smallerPathBudget
      intro call
      exact (Classical.choose_spec (Classical.choose_spec (smallerProviders call))).2

/-- Compatibility projection of budget-certified exponent induction. -/
theorem exists_fixed_provider
    (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (largeAxes : arity^1000 < shape.axes) (activePositive : 0 < shape.active)
    (axesPositive : 0 < shape.axes) (chunkPositive : 0 < shape.chunk) (unitPayload : shape.payload=1)
    (packingFamily : PackingFamily phaseCoordinate activeFits pair polynomialExponent inputPrecision packingLimit
      guardPositive guardFitsChunk)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+guardBits ≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits ≤ shape.chunk)
    (precisionReserve : baselinePrecision+2*shape.bits ≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive ≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk)
    (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume returnedVolume rowCount : ℕ}
    (path : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume returnedVolume)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels) :
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards path activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsDivisible : roles ∣ rowCount/roles := by
      rw [rowsPadded]
      exact rowGuards.2.2.1
    ∃ eventBudget pathBudget : ComplexRecursiveCallSchema.Call → ℕ,
      UniformProvider phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision growthConstant
        baselineLive basisProgram headerStack pcStack liveStack path childRowsDivisible eventBudget pathBudget := by
  let invariant : BudgetInvariant shape :=
    fun {nodeLeft childExponent dependencyLevels frameVolume returnedVolume rowCount} _ _ _ _ => True
  have baseInvariant : ∀ {nodeLeft dependencyLevels frameVolume returnedVolume rowCount : ℕ}
      (path : Path shape.active nodeLeft (0+2) dependencyLevels frameVolume returnedVolume)
      (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels),
      invariant path rowsPadded (fun _ => 0) (fun _ => 0) := by
    intros
    exact True.intro
  have successorInvariant : SuccessorBudgetInvariant phaseCoordinate activeFits pair polynomialExponent inputPrecision
      packingLimit guardPositive guardFitsChunk chunkPositive packingFamily invariant := by
    unfold SuccessorBudgetInvariant
    intro nodeLeft smallerExponent dependencyLevels frameVolume returnedVolume rowCount
      path rowsPadded smallerEventBudget smallerPathBudget
    dsimp only
    intro _
    exact True.intro
  obtain ⟨eventBudget,pathBudget,provider,_budgetCertificate⟩ := exists_fixed_provider_with_budget_invariant
    phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit
    guardPositive guardFitsChunk basisProgram headerStack pcStack liveStack basisConstant basisRuns
    largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom
    precisionReserve baselineFits growthReserve denominatorRoom invariant baseInvariant successorInvariant childExponent path rowsPadded
  exact ⟨eventBudget,pathBudget,provider⟩

end Static
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction
noncomputable section
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactActualStageAllowance (actualShape)
open CompactGlobalRowPadding (rowsAt)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls CompactComplexRolePhaseSite.roleCount

/-- Transport the positive-row input through a literal row-count identity. -/
private theorem packed_row_count_transport
    {shape : CompactGadgetReservationShape.Shape} (stage : ActivePrefixStageParameters.Stage shape)
    (polynomialExponent metadataPrecision packingLimit : ℕ)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard+1 ≤ shape.chunk)
    {sourceRows targetRows : ℕ} (rowsEqual : sourceRows=targetRows)
    (sourcePositive : 0 < sourceRows) (targetPositive : 0 < targetRows)
    (operation : Networks.BinaryRowProgram.Op (Fin stage.slots))
    (targetPacked : ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (NativePolynomialStageShape.inputs stage targetRows polynomialExponent metadataPrecision
          guardPositive guardFitsChunk targetPositive) operation) packingLimit) :
    ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (NativePolynomialStageShape.inputs stage sourceRows polynomialExponent metadataPrecision
          guardPositive guardFitsChunk sourcePositive) operation) packingLimit := by
  cases rowsEqual
  exact targetPacked

/-- Actual polynomial serialization supplies the inherited packing contract
at every genuine descendant, from one stored signed-width allowance. -/
theorem eventually_actual_packing_family :
    ∀ᶠ inputSize : ℕ in Filter.atTop,
    ∀ (reservationAxes inputPrecision : ℕ)
      (cutoffFits : CompactReservationCutoff.cutoff roles arity inputSize ≤ reservationAxes)
      (reservationFits : reservationAxes ≤ Sizes.d inputSize)
      (phaseCoordinate : Fin (actualShape inputSize roles arity reservationAxes 1).chunk)
      (activeFits : (actualShape inputSize roles arity reservationAxes 1).active ≤
        (actualShape inputSize roles arity reservationAxes 1).axes)
      (pair : Networks.BinaryRowProgram.Op (Fin arity))
      (guardPositive : 1 ≤ (actualShape inputSize roles arity reservationAxes 1).guard)
      (guardFitsChunk : (actualShape inputSize roles arity reservationAxes 1).guard+1 ≤
        (actualShape inputSize roles arity reservationAxes 1).chunk)
      (_storedWidth : Sizes.b inputSize ≤ NativePolynomialStageShape.width
        (actualShape inputSize roles arity reservationAxes 1)
        (ButterflyIndependentGuardHeaders.reservation
          (actualShape inputSize roles arity reservationAxes 1).bits inputPrecision)),
      PackingFamily phaseCoordinate activeFits pair (Sizes.ℓ inputSize) inputPrecision 1 guardPositive guardFitsChunk := by
  have rolesAtLeastTwo : 2 ≤ roles := by
    norm_num [roles,CompactComplexRolePhaseSite.roleCount]
  have arityAtLeastTwo : 2 ≤ arity := by norm_num [arity]
  filter_upwards [CompactNativePolynomialStagePacked.eventually_packed roles arity rolesAtLeastTwo arityAtLeastTwo]
    with inputSize actualPacked
  intro reservationAxes inputPrecision cutoffFits reservationFits phaseCoordinate activeFits pair
    guardPositive guardFitsChunk storedWidth
  intro nodeLeft childExponent dependencyLevels frameVolume returnedVolume path rowCount rowsPadded roleRowsPositive
    operation _nontrivialStage
  have chunkPositive : 0 < (actualShape inputSize roles arity reservationAxes 1).chunk := by omega
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards path activeFits roles
    (actualShape inputSize roles arity reservationAxes 1).chunk (by omega) chunkPositive (by omega)
  have childRowsPadded : rowCount/roles=rowsAt roles arity (Sizes.d inputSize) (Sizes.K inputSize) (dependencyLevels+1) := by
    rw [rowsPadded]
    exact rowGuards.2.2.2.2.2.1
  have descendantDepth := CompactComplexRecursivePathRows.exponent_levels_le_depth path activeFits
  change (childExponent+2)+dependencyLevels ≤ CompactGlobalRowPadding.depth arity (Sizes.d inputSize) at descendantDepth
  have descendantPacked := actualPacked reservationAxes (dependencyLevels+1)
    (ButterflyIndependentGuardHeaders.reservation (actualShape inputSize roles arity reservationAxes 1).bits inputPrecision)
    cutoffFits reservationFits (by omega)
    (CompactComplexChildHeadersData.parent phaseCoordinate path.visit activeFits pair) storedWidth
    guardPositive guardFitsChunk (by rw [←childRowsPadded]; exact roleRowsPositive) operation
  exact packed_row_count_transport (CompactComplexChildHeadersData.parent phaseCoordinate path.visit activeFits pair)
    (Sizes.ℓ inputSize)
    (ButterflyIndependentGuardHeaders.reservation (actualShape inputSize roles arity reservationAxes 1).bits inputPrecision)
    1 guardPositive guardFitsChunk childRowsPadded roleRowsPositive
    (by rw [←childRowsPadded]; exact roleRowsPositive) operation descendantPacked

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction
