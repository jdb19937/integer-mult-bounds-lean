module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards
public import IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal

/-! Original instruction semantics of an actual scalar emitter between trace
States. Its group ordinal comes from the actual schedule prefix, and signed
reserves come from the original entry Path after counted sibling returns. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarValues
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyReachedEventTrace (State)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  Networks.ComplexRecursiveCallSchema.sites Networks.ComplexRecursiveCallSchema.calls schedule
  CompactComplexRolePhaseSite.roleCount

section Transport
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume returnedVolume sourcePrefix targetPrefix live : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {bank : Tapes (nodeTapes stackCount roles) 2}

private def prefix_reached
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume sourcePrefix live pcStack origin savedCalls bank)
    (prefixEqual : sourcePrefix=targetPrefix) :
    Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume targetPrefix live pcStack origin savedCalls bank := by
  cases prefixEqual
  exact reached

private theorem prefix_reached_data
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume sourcePrefix live pcStack origin savedCalls bank)
    (prefixEqual : sourcePrefix=targetPrefix) : (prefix_reached reached prefixEqual).data=reached.data := by
  cases prefixEqual
  rfl

end Transport

section Node
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume entryReturned childExponent eventIndex sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}

/-- The genuine emitted data equality supplies the scalar event's original
instruction action on every serialized row, polynomial and anchored slice.
No original-network prefix equality or advanced dependency Path is assumed. -/
theorem scalar_state_values
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
      dependencyLevels frameVolume entryReturned)
    (phaseCoordinate : Fin shape.chunk) (group : GroupIndex)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.scalar group)
    (before : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent+1) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) eventIndex sourceLive)
    (after : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent+1) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1) (sourceLive+(block group).length))
    (afterData : after.reached.data=execute (block group) before.reached.data)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*guardBits≤shape.chunk) :
    ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : Networks.BinaryWalsh.Address shape.bits),
      stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
        (sourceLive+(block group).length) after.reached.data row polynomialIndex anchor=
      Networks.FramedFactorExecution.run
        (CompactComplexActualInterleavedNetwork.instructions (arity^(childExponent+1)) (Event.scalar group))
        (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
          sourceLive before.reached.data row polynomialIndex anchor) := by
  have prefixOrdinal := CompactComplexActualScalarOrdinal.schedule_prefix_ordinal eventIndex eventBound group eventEquation
  let eventReached := prefix_reached before.reached prefixOrdinal
  have eventData := prefix_reached_data before.reached prefixOrdinal
  intro row polynomialIndex anchor
  rw [afterData,CompactComplexScalarSegmentRows.block_length,←eventData]
  exact CompactComplexSourceReadySiblingGuards.computed_scalar_semantics entryPath
    (Nat.pow_le_pow_right (by decide) (by omega)) phaseCoordinate entryPath.visit group eventReached
    activePositive precisionReserve axesFit growthReserve chunkRoom row polynomialIndex anchor

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarValues
