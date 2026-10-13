module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafChildRun
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafProgress
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget

/-! The actual completed child trace and terminal frame supply physical
nonstopped return Progress. Both denominator ledgers and target coverage are
obtained from the real execution, rather than supplied as numerical oracles. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnProgress
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactRecursiveDependencyBudget (precedingCalls)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount schedule

section Child
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft grandchildExponent dependencyLevels frameVolume entryReturned eventIndex parentRows polynomialExponent
    metadataPrecision baselinePrecision growthConstant baselineLive parentScalarPrefix parentLive finalLive elapsedSteps : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (grandchildExponent+3)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack headerStack liveStack : Fin stackCount} {origin : ℤ}
  {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
    metadataPrecision (grandchildExponent+3) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^(grandchildExponent+2))) parentScalarPrefix parentLive
    pcStack origin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call)
  (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
  (initialChild : State (stage:=child phaseCoordinate parentPath.visit activeFits pair call.slot)
    (rowCount:=parentRows/roles) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=dependencyLevels+1) (frameVolume:=frameVolume+arity^(grandchildExponent+3))
    (entryReturned:=entryReturned+precedingCalls call*arity^(grandchildExponent+2))
    (childExponent:=grandchildExponent+1) (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls) 0 parentLive)
  (finalBoundary : FrameState (stage:=child phaseCoordinate parentPath.visit activeFits pair call.slot)
    (rowCount:=parentRows/roles) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=dependencyLevels+1) (frameVolume:=frameVolume+arity^(grandchildExponent+3))
    (entryReturned:=entryReturned+precedingCalls call*arity^(grandchildExponent+2))
    (childExponent:=grandchildExponent+1) (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls)
    (capture initialChild headerStack liveStack) initialChild.reached.targetValue schedule.length finalLive)
  (childTrace : Execution basisProgram headerStack liveStack parentLive initialChild finalBoundary.state elapsedSteps)

include childTrace in
/-- The actual raw terminal denominator covers the two-volume returned target. -/
theorem target_coverage : parentLive+2*arity^(grandchildExponent+2)≤finalLive := by
  have actualCoverage := CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage childTrace
  simpa only [CompactComplexDenominatorPolicy.networkTarget,Nat.add_assoc] using actualCoverage.2

/-- The actual entry target descriptor and the retained terminal frame
identify the literal completed target; no numeric target assertion is supplied. -/
theorem terminal_target_of_entry
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (original : CompactSpectatorVisitGeometry.Array shape (parentRows/roles) polynomialExponent)
    (controlBank : Tapes 43 2) (queueBank : Tapes 1 2) (scalarHeaders : ActiveRepairRankHeadersCommands.State)
    (tailBank : Tapes 22 2) (originalStorage : Tapes (10+stackCount) 2) (auxiliaryBank : Tapes 2 2)
    (entryBank : initialChild.bank=CompactComplexSourceReadyReachedEventInvariant.canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent
        (child phaseCoordinate parentPath.visit activeFits pair call.slot) childSlots (parentRows/roles)
        polynomialExponent metadataPrecision parentLive (grandchildExponent+1) childRowsDivisible original
        controlBank queueBank scalarHeaders tailBank originalStorage) auxiliaryBank) :
    finalBoundary.state.reached.targetValue=parentLive+2*arity^(grandchildExponent+2) := by
  have actualEntryTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    initialChild.reached childSlots parentLive (grandchildExponent+1) childRowsDivisible original
    controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank entryBank
  exact finalBoundary.targetRetained.trans (by simpa only [Nat.add_assoc] using actualEntryTarget)

/-- The unchanged parent's genuine entry Path and scheduled cursor combine
with the actual child terminal Reached ledger. The current is exactly finalLive;
the returned target is exactly parentLive plus twice the child volume. -/
def of_child_run
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk) :
    CompactComplexChildAlignmentBudget.Progress shape metadataPrecision parentLive finalLive
      (parentLive+2*arity^(grandchildExponent+2)) :=
  CompactComplexSourceReadyReachedNonleafProgress.progress (childExponent:=grandchildExponent+1)
    parentPath call parentReached childTrace eventBound eventEquation precisionReserve baselineFits denominatorRoom

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnProgress
