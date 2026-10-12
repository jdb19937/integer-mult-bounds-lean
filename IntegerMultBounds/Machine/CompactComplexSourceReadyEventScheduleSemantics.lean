module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarEventSemantics

/-! Actual schedule-prefix sibling accounting retains the original signed
width reservation. The entry dependency Path remains anchored at node entry;
processed sibling volumes are counted separately rather than constructing a
fictional Path with an advanced returned counter or counting siblings twice. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyEventScheduleSemantics
noncomputable section
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path callCapacity volumeCoefficient)
open CompactComplexCompletedLiveLower (Event schedule childNames)
open Networks
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.calls schedule

theorem childNames_append (eventPrefix eventSuffix : List Event) :
    childNames (eventPrefix++eventSuffix)=childNames eventPrefix++childNames eventSuffix := by
  induction eventPrefix with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
    cases event <;> simp only [List.cons_append,childNames,List.cons_append,inductionHypothesis]

/-- The actual processed child count is bounded by the original finite call
family, including prefixes between scalar groups and terminal sink calls. -/
theorem processed_calls_le_capacity (eventIndex : ℕ) :
    (childNames (schedule.take eventIndex)).length≤callCapacity := by
  have split := congrArg childNames (List.take_append_drop eventIndex schedule)
  rw [childNames_append,CompactComplexCompletedLiveLower.schedule_calls] at split
  have lengths := congrArg List.length split
  simp only [List.length_append] at lengths
  have prefixBound : (childNames (schedule.take eventIndex)).length≤ComplexRecursiveCallSchema.calls.length := by
    omega
  exact prefixBound.trans CompactRecursiveDependencyBudget.calls_le_capacity

/-- Ancestor frames and the current node's own volume share the original
shrinking-width potential; charging them independently would lose this fact. -/
theorem frames_and_node_le {active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned : ℕ}
    (entryPath : Path active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned) :
    frameVolume+arity^nodeExponent≤2*active := by
  have potential := entryPath.potential
  have arityPositive : 0<arity := by decide
  have arityTwice : arity≤2*(arity-1) := by decide
  have frameCharge := Nat.mul_le_mul_right frameVolume arityTwice
  have combined : arity*(frameVolume+arity^nodeExponent)≤arity*(2*active) := by
    calc
      _ = arity*frameVolume+arity*arity^nodeExponent := by ring
      _ ≤ (2*(arity-1))*frameVolume+2*(arity*arity^nodeExponent) :=
        Nat.add_le_add frameCharge (Nat.le_mul_of_pos_left _ (by decide : 0<2))
      _ = 2*(frameVolume*(arity-1)+arity*arity^nodeExponent) := by ring
      _ ≤ 2*(arity*active) := Nat.mul_le_mul_left 2 potential
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left combined arityPositive

/-- A genuine entry Path and counted original sibling calls fit exactly the
existing volume coefficient, with no increased precision or proof limits. -/
theorem sibling_volume_bound {active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned : ℕ}
    (entryPath : Path active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (processedCalls childVolume : ℕ) (callsFit : processedCalls≤callCapacity)
    (childFitsNode : childVolume≤arity^nodeExponent) :
    frameVolume+2*(entryReturned+processedCalls*childVolume)≤volumeCoefficient*active := by
  have ancestorReturned := entryPath.returned_le
  have nodeAndFrames := frames_and_node_le entryPath
  have framesFit := entryPath.frames_le
  have siblingCharge := Nat.mul_le_mul callsFit childFitsNode
  have totalReturned : entryReturned+processedCalls*childVolume≤callCapacity*(frameVolume+arity^nodeExponent) := by
    nlinarith
  have returnedFits : entryReturned+processedCalls*childVolume≤2*callCapacity*active := by
    have combinedCharge := Nat.mul_le_mul_left callCapacity nodeAndFrames
    nlinarith
  unfold volumeCoefficient
  nlinarith

/-- Every actual event prefix receives its sibling budget from schedule
counting and the original entry geometry, without an advanced-Path premise. -/
theorem schedule_prefix_volume_bound {active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned : ℕ}
    (entryPath : Path active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (eventIndex childVolume : ℕ) (childFitsNode : childVolume≤arity^nodeExponent) :
    frameVolume+2*(entryReturned+(childNames (schedule.take eventIndex)).length*childVolume)≤
      volumeCoefficient*active :=
  sibling_volume_bound entryPath _ childVolume (processed_calls_le_capacity eventIndex) childFitsNode

/-- The genuine sibling cursor pays the same scalar signed-growth power as
an entry Path, using the unchanged reservation coefficient. -/
theorem sibling_growth_power {shape : CompactGadgetReservationShape.Shape}
    {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned : ℕ}
    (entryPath : Path shape.active nodeLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (processedCalls childVolume baselinePrecision growthConstant completedAxes : ℕ)
    (callsFit : processedCalls≤callCapacity) (childFitsNode : childVolume≤arity^nodeExponent) :
    CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume
      (entryReturned+processedCalls*childVolume) completedAxes<
      2^(CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes) := by
  have levelsFit : dependencyLevels≤shape.active := by
    have levelPotential := entryPath.levels_le
    omega
  have volumesFit := sibling_volume_bound entryPath processedCalls childVolume callsFit childFitsNode
  have logarithmCharge := Nat.mul_le_mul_right (Nat.clog 2 (growthConstant+1)) levelsFit
  have widthFits : CompactRecursiveGridBudget.halfWidth baselinePrecision growthConstant
      (dependencyLevels+1) (frameVolume+2*(entryReturned+processedCalls*childVolume)+completedAxes)≤
      CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes := by
    unfold CompactRecursiveGridBudget.halfWidth CompactComplexScalarPathGuard.power
      CompactSpectatorInheritedGrid.dependencyCoefficient
    nlinarith
  exact (CompactRecursiveGridBudget.strict baselinePrecision growthConstant (dependencyLevels+1)
    (frameVolume+2*(entryReturned+processedCalls*childVolume)+completedAxes)).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) widthFits)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyEventScheduleSemantics
