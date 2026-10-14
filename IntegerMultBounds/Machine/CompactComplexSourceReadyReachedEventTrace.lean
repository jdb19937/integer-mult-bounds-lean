module

public import IntegerMultBounds.Machine.CompactComplexFixedNodePathAlgebra
public import IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingCompletedChildProgress

/-! Witnessed actual schedule execution on the unchanged aligned finite table.
The event constructors require physical paths and genuine reached endpoints.
Execution induction derives the completed denominator and its terminal coverage;
this does not assert existence of recursive executions. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexScalarIntegerRows (GroupIndex RowIndex)
open CompactComplexScalarSegmentRows (block)
open CompactComplexCompletedLiveLower (Event schedule completedWith completed childTarget)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexActualScalarOrdinal (scalarGroups)
open Networks.Shared50ModularControl (prime)
open Networks.ComplexRecursiveCallSchema (Call)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  Networks.ComplexRecursiveCallSchema.sites Networks.ComplexRecursiveCallSchema.calls
  CompactComplexRolePhaseSite.roleCount schedule CompactComplexDenominatorCapacity.scalarRows
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- Abstract fold composition is proved before specializing the large schedule. -/
theorem completedWith_append (rows : GroupIndex → List RowIndex) (target : ℕ → ℕ)
    (firstEvents lastEvents : List Event) (initialLive : ℕ) :
    completedWith rows target (firstEvents++lastEvents) initialLive=
      completedWith rows target lastEvents (completedWith rows target firstEvents initialLive) := by
  induction firstEvents generalizing initialLive with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
    cases event <;> simp only [List.cons_append,completedWith,inductionHypothesis]

/-- A genuine next event advances precisely the completed prefix fold. -/
theorem completed_prefix_successor (rows : GroupIndex → List RowIndex) (target : ℕ → ℕ)
    (events : List Event) (eventIndex initialLive : ℕ) (eventBound : eventIndex<events.length) :
    completedWith rows target (events.take (eventIndex+1)) initialLive=
      match events[eventIndex] with
      | .scalar group => completedWith rows target (events.take eventIndex) initialLive+(rows group).length
      | .child _ => target (completedWith rows target (events.take eventIndex) initialLive) := by
  rw [List.take_succ_eq_append_getElem eventBound,completedWith_append]
  cases events[eventIndex] <;> rfl

/-- Scalar denominator accounting is proved over a symbolic event list. -/
theorem scalar_completed_step (stopped : Bool) (childExponent : ℕ) (events : List Event)
    (eventIndex initialLive sourceLive : ℕ) (group : GroupIndex)
    (eventBound : eventIndex<events.length) (eventEquation : events[eventIndex]=Event.scalar group)
    (priorLive : sourceLive=completed stopped childExponent (events.take eventIndex) initialLive) :
    sourceLive+(block group).length=completed stopped childExponent (events.take (eventIndex+1)) initialLive := by
  have successor := completed_prefix_successor block (fun live => childTarget stopped live childExponent)
    events eventIndex initialLive eventBound
  rw [eventEquation] at successor
  exact (congrArg (fun live => live+(block group).length) priorLive).trans successor.symm

/-- Child denominator accounting also uses only symbolic event data. -/
theorem child_completed_step (stopped : Bool) (childExponent : ℕ) (events : List Event)
    (eventIndex initialLive sourceLive : ℕ) (call : Call)
    (eventBound : eventIndex<events.length) (eventEquation : events[eventIndex]=Event.child call)
    (priorLive : sourceLive=completed stopped childExponent (events.take eventIndex) initialLive) :
    childTarget stopped sourceLive childExponent=
      completed stopped childExponent (events.take (eventIndex+1)) initialLive := by
  have successor := completed_prefix_successor block (fun live => childTarget stopped live childExponent)
    events eventIndex initialLive eventBound
  rw [eventEquation] at successor
  exact (congrArg (fun live => childTarget stopped live childExponent) priorLive).trans successor.symm

attribute [local irreducible] completed completedWith

/-- Symbolic cursor layout avoids evaluating the enormous closed schedule. -/
def cursorPCFor (originalCount eventCount eventIndex : ℕ) : Fin (originalCount+(4+eventCount)+2) :=
  if eventBound : eventIndex<eventCount then
    GuardedFiniteReturnExtraFlow.extraPC (N:=originalCount) (Fin.natAdd 4 ⟨eventIndex,eventBound⟩)
  else CompactComplexScheduledPCLayout.finalPCFor originalCount eventCount

theorem cursorPCFor_event (originalCount eventCount eventIndex : ℕ)
    (eventBound : eventIndex<eventCount) :
    cursorPCFor originalCount eventCount eventIndex=
      GuardedFiniteReturnExtraFlow.extraPC (N:=originalCount)
        (Fin.natAdd 4 (⟨eventIndex,eventBound⟩ : Fin eventCount)) := by
  rw [cursorPCFor,dite_eq_left eventBound]

theorem cursorPCFor_final (originalCount eventCount : ℕ) :
    cursorPCFor originalCount eventCount eventCount=
      CompactComplexScheduledPCLayout.finalPCFor originalCount eventCount := by
  rw [cursorPCFor,dite_eq_right (Nat.lt_irrefl _)]

theorem cursorPCFor_next (originalCount eventCount : ℕ) (eventIndex : Fin eventCount) :
    cursorPCFor originalCount eventCount (eventIndex.val+1)=
      CompactComplexScheduledPCLayout.nextPCFor originalCount eventCount eventIndex := rfl

attribute [local irreducible] cursorPCFor CompactComplexScheduledPCLayout.nextPCFor
  CompactComplexScheduledPCLayout.finalPCFor

/-- Cursor positions include the unique schedule-end continuation. Inferring
the result type avoids expanding the concrete PCs abbreviation. -/
def cursorPC (eventIndex : ℕ) :=
  cursorPCFor CompactComplexScheduledPCLayout.originalCount schedule.length eventIndex

theorem cursorPC_event (eventIndex : ℕ) (eventBound : eventIndex<schedule.length) :
    cursorPC eventIndex=CompactComplexScheduledPCLayout.eventPC ⟨eventIndex,eventBound⟩ :=
  cursorPCFor_event CompactComplexScheduledPCLayout.originalCount schedule.length eventIndex eventBound

theorem cursorPC_final : cursorPC schedule.length=CompactComplexScheduledPCLayout.finalPC :=
  cursorPCFor_final CompactComplexScheduledPCLayout.originalCount schedule.length

theorem cursorPC_next (eventIndex : Fin schedule.length) :
    cursorPC (eventIndex.val+1)=CompactComplexScheduledPCLayout.nextPC eventIndex :=
  cursorPCFor_next CompactComplexScheduledPCLayout.originalCount schedule.length eventIndex

attribute [local irreducible] CompactComplexFixedNodePaths.nodePath

/-- Prove fixed-table path algebra before specializing reached-bank types. -/
theorem fixed_path_nil {stackCount basisStateCount : ℕ}
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2))
    (bank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime) :
    CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      startPC bank 0 startPC bank := by
  unfold CompactComplexAlignedChildEntryPath.path
  exact CompactComplexFixedNodePathAlgebra.node_nil _ _ _ _ _ _ startPC bank

theorem fixed_path_append {stackCount basisStateCount : ℕ}
    {basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime}
    {headerStack pcStack liveStack : Fin stackCount}
    {startPC middlePC finalPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2)}
    {initialBank middleBank finalBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime}
    {priorSteps eventSteps : ℕ}
    (priorPath : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      startPC initialBank priorSteps middlePC middleBank)
    (eventPath : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      middlePC middleBank eventSteps finalPC finalBank) :
    CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      startPC initialBank (priorSteps+eventSteps) finalPC finalBank :=
  by
    unfold CompactComplexAlignedChildEntryPath.path at priorPath eventPath ⊢
    exact CompactComplexFixedNodePathAlgebra.node_append _ _ _ _ _ _ priorPath eventPath

attribute [local irreducible] CompactComplexAlignedChildEntryPath.path

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume entryReturned childExponent : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Call}

/-- Both prefix cursors are obtained from the actual event position. Metadata
exponent is fixed throughout the node, even when its child exponent is zero. -/
structure State (eventIndex live : ℕ) where
  inRange : eventIndex≤schedule.length
  bank : Tapes (nodeTapes stackCount roles) 2
  reached : Reached stage rowCount polynomialExponent metadataPrecision (childExponent+1)
    baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^childExponent))
    (scalarGroups (schedule.take eventIndex)).length live pcStack origin savedCalls bank

local notation "NodeState" => State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)

def physicalBank {eventIndex live : ℕ}
    (state : NodeState
      eventIndex live) : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime :=
  CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready state.bank))

variable (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
  (headerStack liveStack : Fin stackCount)

/-- Every constructor carries an actual event equation and a path on the same
fixed table. Denominator endpoints are indexed, rather than numeric callbacks. -/
inductive Step : {eventIndex sourceLive targetLive : ℕ} →
    NodeState
      eventIndex sourceLive → NodeState (eventIndex+1) targetLive → ℕ → Prop where
  | scalar {eventIndex sourceLive : ℕ} (group : GroupIndex)
      (eventBound : eventIndex<schedule.length)
      (eventEquation : schedule[eventIndex]=Event.scalar group)
      (before : NodeState eventIndex sourceLive)
      (after : NodeState (eventIndex+1) (sourceLive+(block group).length)) (elapsedSteps : ℕ)
      (physical : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
        (cursorPC eventIndex) (physicalBank before) elapsedSteps
        (cursorPC (eventIndex+1)) (physicalBank after)) : Step before after elapsedSteps
  | child {eventIndex sourceLive : ℕ} (call : Call)
      (eventBound : eventIndex<schedule.length)
      (eventEquation : schedule[eventIndex]=Event.child call)
      (before : NodeState eventIndex sourceLive)
      (after : NodeState (eventIndex+1)
        (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
          sourceLive childExponent)) (elapsedSteps : ℕ)
      (physical : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
        (cursorPC eventIndex) (physicalBank before) elapsedSteps
        (cursorPC (eventIndex+1)) (physicalBank after)) : Step before after elapsedSteps

variable {basisProgram headerStack liveStack}

theorem Step.physical {eventIndex sourceLive targetLive elapsedSteps : ℕ}
    {before : NodeState
      eventIndex sourceLive} {after : NodeState (eventIndex+1) targetLive}
    (step : Step basisProgram headerStack liveStack before after elapsedSteps) :
    CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (cursorPC eventIndex) (physicalBank before) elapsedSteps
      (cursorPC (eventIndex+1)) (physicalBank after) := by
  cases step with
  | scalar _ _ _ _ _ _ physical => exact physical
  | child _ _ _ _ _ _ physical => exact physical

/-- Actual snoc execution starts at the supplied initial physical reached bank. -/
inductive Execution (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount) (initialLive : ℕ) (initialState : NodeState 0 initialLive) :
    {eventIndex live : ℕ} → NodeState eventIndex live → ℕ → Prop where
  | nil : Execution basisProgram headerStack liveStack initialLive initialState initialState 0
  | snoc {eventIndex sourceLive targetLive priorSteps eventSteps : ℕ}
      {before : NodeState eventIndex sourceLive} {after : NodeState (eventIndex+1) targetLive}
      (priorExecution : Execution basisProgram headerStack liveStack initialLive initialState before priorSteps)
      (step : Step basisProgram headerStack liveStack before after eventSteps) :
      Execution basisProgram headerStack liveStack initialLive initialState after (priorSteps+eventSteps)

/-- Each actual typed event advances the symbolic completed denominator fold. -/
theorem Step.completed_prefix {eventIndex sourceLive targetLive elapsedSteps : ℕ}
    {before : NodeState eventIndex sourceLive} {after : NodeState (eventIndex+1) targetLive}
    (step : Step basisProgram headerStack liveStack before after elapsedSteps) (initialLive : ℕ)
    (priorLive : sourceLive=completed (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
      childExponent (schedule.take eventIndex) initialLive) :
    targetLive=completed (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
      childExponent (schedule.take (eventIndex+1)) initialLive :=
  Step.rec
    (motive := fun {targetLive} _ _ _ _ =>
      sourceLive=completed (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
        childExponent (schedule.take eventIndex) initialLive →
      targetLive=completed (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
        childExponent (schedule.take (eventIndex+1)) initialLive)
    (fun group eventBound eventEquation _ _ _ _ priorLive =>
      scalar_completed_step (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
        childExponent schedule eventIndex initialLive sourceLive group eventBound eventEquation priorLive)
    (fun call eventBound eventEquation _ _ _ _ priorLive =>
      child_completed_step (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
        childExponent schedule eventIndex initialLive sourceLive call eventBound eventEquation priorLive) step priorLive

-- Saved variable types are replayed before notation-captured section names.
-- Spell out State here to prevent silent recovery placeholders during replay.
variable {initialLive : ℕ} {initialState : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) 0 initialLive}

/-- All physical joins are already charged by the local fixed-table paths.
A direct recursor avoids costly dependent-induction preprocessing. -/
theorem execution_physical {eventIndex live elapsedSteps : ℕ} {finalState : NodeState eventIndex live}
    (trace : Execution (basisProgram:=basisProgram) (headerStack:=headerStack) (liveStack:=liveStack)
      initialLive initialState finalState elapsedSteps) :
    CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (cursorPC 0) (physicalBank initialState) elapsedSteps (cursorPC eventIndex) (physicalBank finalState) :=
  Execution.rec
    (motive := fun {eventIndex _live} finalState elapsedSteps _ =>
      CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
        (cursorPC 0) (physicalBank initialState) elapsedSteps
        (cursorPC eventIndex) (physicalBank finalState))
    (fixed_path_nil basisProgram headerStack pcStack liveStack (cursorPC 0) (physicalBank initialState))
    (fun {_ _ _ _ _ _ _} _ step inductionHypothesis =>
      fixed_path_append inductionHypothesis step.physical) trace


/-- Exact denominator accounting is derived from the actual scalar/child
constructors; no endpoint equation is assumed by the trace. -/
theorem execution_completed_exact {eventIndex live elapsedSteps : ℕ} {finalState : NodeState eventIndex live}
    (trace : Execution (basisProgram:=basisProgram) (headerStack:=headerStack) (liveStack:=liveStack)
      initialLive initialState finalState elapsedSteps) :
    live=completed (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
      childExponent (schedule.take eventIndex) initialLive :=
  Execution.rec
    (motive := fun {eventIndex live} _ _ _ =>
      live=completed (Networks.ComplexRecursiveCallSchema.stopped shape.axes childExponent)
        childExponent (schedule.take eventIndex) initialLive)
    (by simp only [List.take_zero,completed,completedWith])
    (fun {_ _ _ _ _ _ _} _ step inductionHypothesis =>
      step.completed_prefix initialLive inductionHypothesis) trace

/-- A terminal actual execution covers both published denominator-policy bounds. -/
theorem execution_terminal_coverage {live elapsedSteps : ℕ} {finalState : NodeState schedule.length live}
    (trace : Execution (basisProgram:=basisProgram) (headerStack:=headerStack) (liveStack:=liveStack)
      initialLive initialState finalState elapsedSteps) :
    CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive childExponent≤live ∧
    CompactComplexDenominatorPolicy.networkTarget initialLive childExponent≤live := by
  have exactLive := execution_completed_exact trace
  rw [List.take_length] at exactLive
  rw [exactLive]
  exact ⟨CompactComplexCompletedLiveLower.actual_completed_lower shape.axes childExponent initialLive,
    CompactComplexCompletedLiveLower.actual_network_target shape.axes childExponent initialLive⟩

/-- The denominator is the literal storage-seven descriptor of the reached
endpoint, including its physical head position. -/
theorem State.storage_live {eventIndex live : ℕ} (state : NodeState eventIndex live) :
    CompactComplexRecursiveLiveProgress.Live state.reached.storage ⟨7,by omega⟩ live :=
  state.reached.live

/-- The genuine terminal witness has precisely the complete compiler prefix,
as expected by the nonleaf child-progress adapter. -/
def State.terminal_reached {live : ℕ} (state : NodeState schedule.length live) :
    Reached stage rowCount polynomialExponent metadataPrecision (childExponent+1)
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned schedule.length (arity^childExponent))
      Networks.ComplexRank25.program.length live pcStack origin savedCalls state.bank := by
  have reached := state.reached
  rw [List.take_length,
    CompactComplexSourceReadySiblingCompletedChildProgress.scalar_cursor_end] at reached
  exact reached

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
