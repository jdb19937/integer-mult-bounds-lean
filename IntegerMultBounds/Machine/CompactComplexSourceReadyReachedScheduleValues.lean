module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexEventInstructionPrefix
public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics

/-! Original compiler-prefix values on any actual reached schedule, independent
of the child stopping branch. Local checked event values extend the same prefix;
the terminal prefix is the original full compiler network. Physical execution
is carried separately by the actual trace and is not asserted by these lemmas. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedScheduleValues
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyReachedEventTrace (State)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexActualInterleavedNetwork (expand instructions)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Node
variable {stackCount : ℕ} {shape : Shape}
  {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft childExponent rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
    dependencyLevels frameVolume entryReturned initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2))

local notation "NodeState" => State (stage:=stage) (rowCount:=rowCount)
  (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
  (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
  (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
  (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
  (origin:=origin) (savedCalls:=savedCalls)

/-- Prefix semantics uses the literal stored arrays of the original and
current reached states, preserving every row and spectator coordinate. -/
def PrefixValues (initialState : NodeState 0 initialLive)
    {eventIndex live : ℕ} (currentState : NodeState eventIndex live) : Prop :=
  ∀ (row : Fin (rowCount/CompactComplexSourceReadyScalarWorkspace.roles))
    (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
    stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
      (metadataPrecision-2*shape.bits) live currentState.reached.data row polynomialIndex globalAnchor=
    FramedFactorExecution.run (expand (arity^(childExponent+1)) (schedule.take eventIndex))
      (stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
        (metadataPrecision-2*shape.bits) initialLive initialState.reached.data row polynomialIndex globalAnchor)

/-- The actual initial stored data is the empty compiler prefix. -/
theorem initial (initialState : NodeState 0 initialLive) :
    PrefixValues phaseCoordinate visit initialState initialState := by
  intro row polynomialIndex globalAnchor
  exact (CompactComplexEventInstructionPrefix.prefix_run_zero (arity^(childExponent+1)) schedule _).symm

/-- The original chronological prefix advances using the exact local event
identity, for scalar, stopped child and nonstopped child events alike. -/
theorem successor (initialState : NodeState 0 initialLive)
    {eventIndex sourceLive targetLive : ℕ}
    (before : NodeState eventIndex sourceLive) (after : NodeState (eventIndex+1) targetLive)
    (eventBound : eventIndex<schedule.length)
    (priorValues : PrefixValues phaseCoordinate visit initialState before)
    (eventValues : ∀ (row : Fin (rowCount/CompactComplexSourceReadyScalarWorkspace.roles))
      (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
      stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
        (metadataPrecision-2*shape.bits) targetLive after.reached.data row polynomialIndex globalAnchor=
      FramedFactorExecution.run (instructions (arity^(childExponent+1)) schedule[eventIndex])
        (stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
          (metadataPrecision-2*shape.bits) sourceLive before.reached.data row polynomialIndex globalAnchor)) :
    PrefixValues phaseCoordinate visit initialState after := by
  intro row polynomialIndex globalAnchor
  have prefixStep := CompactComplexEventInstructionPrefix.schedule_prefix_run_step
    (arity^(childExponent+1)) eventIndex eventBound
    (stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
      (metadataPrecision-2*shape.bits) initialLive initialState.reached.data row polynomialIndex globalAnchor)
  exact (eventValues row polynomialIndex globalAnchor).trans
    ((congrArg (FramedFactorExecution.run (instructions (arity^(childExponent+1)) schedule[eventIndex]))
      (priorValues row polynomialIndex globalAnchor)).trans prefixStep.symm)

/-- A complete prefix on the actual terminal state is the original full
network action, without any stopping or child-execution premise. -/
theorem terminal (initialState : NodeState 0 initialLive) {finalLive : ℕ}
    (finalState : NodeState schedule.length finalLive)
    (values : PrefixValues phaseCoordinate visit initialState finalState) :
    ∀ (row : Fin (rowCount/CompactComplexSourceReadyScalarWorkspace.roles))
      (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
      stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
        (metadataPrecision-2*shape.bits) finalLive finalState.reached.data row polynomialIndex globalAnchor=
      FramedCircuit.run (ComplexFramedExecution.network (arity^(childExponent+1)))
        (stored phaseCoordinate visit (rowCount/CompactComplexSourceReadyScalarWorkspace.roles) polynomialExponent
          (metadataPrecision-2*shape.bits) initialLive initialState.reached.data row polynomialIndex globalAnchor) := by
  intro row polynomialIndex globalAnchor
  exact (values row polynomialIndex globalAnchor).trans
    (CompactComplexEventInstructionPrefix.schedule_prefix_terminal (arity^(childExponent+1)) _)

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedScheduleValues
