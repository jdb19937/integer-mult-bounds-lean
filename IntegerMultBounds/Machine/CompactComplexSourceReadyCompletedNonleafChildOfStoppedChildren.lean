module

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

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren
