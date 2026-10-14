module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace

/-! A witnessed full child schedule supplies the nonleaf target coverage used
by physical parent return. The terminal reached bank supplies the upper ledger,
so neither completed-target nor completed-ledger inequalities are callbacks.
Existence of recursive child executions remains a separate obligation. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafProgress
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path precedingCalls)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event)
open Networks.ComplexRecursiveCallSchema (Call)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  schedule CompactComplexRolePhaseSite.roleCount CompactComplexDenominatorCapacity.scalarRows

variable {stackCount basisStateCount : ℕ} {shape : Shape}
    {parentStage childStage : ActivePrefixStageParameters.Stage shape}
    {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex : ℕ}
    {parentRows childRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
      parentScalarPrefix parentLive completedAxes completedLive elapsedSteps : ℕ}
    {pcStack headerStack liveStack : Fin stackCount} {parentOrigin childOrigin : ℤ}
    {parentCalls childCalls : List Call} {parentBank : Tapes (nodeTapes stackCount roles) 2}
    (entryPath : Path shape.active nodeLeft (childExponent + 2) dependencyLevels frameVolume entryReturned)
    (call : Call)
    (parentReached : Reached parentStage parentRows polynomialExponent metadataPrecision (childExponent + 2)
      baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity ^ (childExponent + 1))) parentScalarPrefix parentLive
      pcStack parentOrigin parentCalls parentBank)

local notation "ChildState" => CompactComplexSourceReadyReachedEventTrace.State
  (stage:=childStage) (rowCount:=childRows) (polynomialExponent:=polynomialExponent)
  (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
  (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
  (dependencyLevels:=dependencyLevels+1) (frameVolume:=frameVolume+arity^(childExponent+2))
  (entryReturned:=entryReturned+precedingCalls call*arity^(childExponent+1))
  (childExponent:=childExponent) (pcStack:=pcStack) (origin:=childOrigin) (savedCalls:=childCalls)

/-- The actual full child trace derives both ledgers and its required target
coverage. Its initial live is the parent's true incoming child live, and its
terminal live is the actual raw completed denominator before contraction. -/
def progress
    {basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime}
    {initialChild : ChildState 0 parentLive}
    {completedChild : ChildState schedule.length completedLive}
    (childTrace : CompactComplexSourceReadyReachedEventTrace.Execution
      (basisProgram:=basisProgram) (headerStack:=headerStack) (liveStack:=liveStack)
      parentLive initialChild completedChild elapsedSteps)
    (eventBound : eventIndex < schedule.length)
    (eventEquation : schedule[eventIndex] = Event.child call)
    (precisionReserve : baselinePrecision + 2 * shape.bits ≤ metadataPrecision)
    (baselineFits : baselineLive ≤ baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room
      CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk) :
    CompactComplexChildAlignmentBudget.Progress shape metadataPrecision parentLive completedLive
      (parentLive + 2 * arity ^ (childExponent + 1)) :=
  CompactComplexSourceReadySiblingCompletedChildProgress.progress entryPath call parentReached
    completedChild.terminal_reached eventBound eventEquation precisionReserve baselineFits denominatorRoom
    (by simpa only [CompactComplexDenominatorPolicy.networkTarget] using (CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage childTrace).2)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafProgress
