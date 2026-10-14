module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant

/-! Actual sibling cursors derive the numerical readiness of physical parent
return from the original node-entry Path. The explicit-guard return API then
retains every physical Restored port without inventing an advanced Path. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingReturnInvariant
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (half Grid)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedReturnInvariant (Restored returnedCaller returnedData)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule childNames)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  CompactComplexRolePhaseSite.roleCount schedule CompactComplexDenominatorCapacity.scalarRows

private theorem returned_cursor_eq (entryReturned eventIndex childVolume : ℕ) :
    returnedCursor entryReturned eventIndex childVolume=
      entryReturned+(childNames (schedule.take eventIndex)).length*childVolume := rfl

/-- Counted siblings retain the original parent promotion guard and capacity,
including the pending real denominator advance. -/
theorem promotion_guard {shape : Shape}
    {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (eventIndex childVolume scalarPrefix baselinePrecision growthConstant completedAxes denominatorAdvance metadataPrecision : ℕ)
    (childFitsNode : childVolume≤arity^nodeExponent) (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes+denominatorAdvance≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    denominatorAdvance≤half shape (metadataPrecision-2*shape.bits)+1 ∧
    CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume+2*returnedCursor entryReturned eventIndex childVolume+completedAxes))*2^denominatorAdvance<
      2^(half shape (metadataPrecision-2*shape.bits)) := by
  let numeratorBound := CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
    (frameVolume+2*returnedCursor entryReturned eventIndex childVolume+completedAxes)
  have prefixBound := CompactFramedScalarGrid.bound_le scalarPrefix numeratorBound growthConstant growthReserve
  have budgetEquation : numeratorBound*growthConstant*4^denominatorAdvance=
      CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume
        (returnedCursor entryReturned eventIndex childVolume) (completedAxes+denominatorAdvance) := by
    unfold numeratorBound CompactComplexScalarPathGuard.budget CompactRecursiveGridBudget.bound
    rw [pow_succ,pow_add,pow_add]
    ring
  have growthPower := CompactComplexSourceReadyEventScheduleSemantics.sibling_growth_power entryPath
    (childNames (schedule.take eventIndex)).length childVolume baselinePrecision growthConstant
    (completedAxes+denominatorAdvance)
    (CompactComplexSourceReadyEventScheduleSemantics.processed_calls_le_capacity eventIndex) childFitsNode
  rw [←returned_cursor_eq entryReturned eventIndex childVolume] at growthPower
  have storedReserve := CompactComplexScalarPathGuard.stored_guard shape baselinePrecision growthConstant
    (completedAxes+denominatorAdvance) metadataPrecision activePositive precisionReserve axesFit chunkRoom
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have halfEquation := CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits
  have powerFits : CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant
      (completedAxes+denominatorAdvance)≤half shape (metadataPrecision-2*shape.bits) := by
    rw [halfEquation]
    omega
  constructor
  · unfold half ButterflyGuard.halfWidth
    omega
  · have shiftBound : 2^denominatorAdvance≤4^denominatorAdvance :=
      Nat.pow_le_pow_left (by decide) denominatorAdvance
    calc
      _ ≤ CompactFramedScalarGrid.bound scalarPrefix numeratorBound*4^denominatorAdvance :=
        Nat.mul_le_mul_left _ shiftBound
      _ ≤ numeratorBound*growthConstant*4^denominatorAdvance := Nat.mul_le_mul_right _ prefixBound
      _ = _ := budgetEquation
      _ < 2^(CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant
          (completedAxes+denominatorAdvance)) := growthPower
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<2) powerFits

section Parent
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned eventIndex childVolume : ℕ}
    {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) scalarPrefix parentLive pcStack origin calls parentBank)

/-- The actual computed return array and physical restored fragments produce
the next genuine parent readiness at its advanced sibling counter. -/
theorem returned_reached
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent)
    (selected : Fin roles) (denominatorAdvance returnedChildVolume : ℕ)
    (childResult : Array shape (parentRows/roles) polynomialExponent)
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes+denominatorAdvance≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (advanceFits : denominatorAdvance≤2*returnedChildVolume)
    (childWidth : ∀ coefficient,(childResult coefficient).1.length=ButterflyGuard.halfWidth metadataPrecision shape.bits+1 ∧
      (childResult coefficient).2.length=ButterflyGuard.halfWidth metadataPrecision shape.bits+1)
    (childGrid : Grid shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      (parentLive+denominatorAdvance)
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
          (frameVolume+2*(returnedCursor entryReturned eventIndex childVolume+returnedChildVolume)+completedAxes))) childResult)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+extraTapes) 2) (aux : Tapes 2 2)
    (physical : Restored nodeExponent (parentLive+denominatorAdvance) parentReached.targetValue
      pcStack origin calls control storage aux) :
    ∃ nextReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume+returnedChildVolume) scalarPrefix
      (parentLive+denominatorAdvance) pcStack origin calls
      (canonical (returnedCaller parentReached selected denominatorAdvance childResult control queue scalar tail storage) aux),
      nextReached.data=returnedData parentReached selected denominatorAdvance childResult := by
  have numerical := promotion_guard entryPath eventIndex childVolume scalarPrefix baselinePrecision growthConstant
    completedAxes denominatorAdvance metadataPrecision childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom
  exact CompactComplexSourceReadyReachedReturnInvariant.returned_reached parentReached selected denominatorAdvance
    returnedChildVolume childResult (by omega) advanceFits childWidth childGrid numerical.1 numerical.2
    control queue scalar tail storage aux physical

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingReturnInvariant
