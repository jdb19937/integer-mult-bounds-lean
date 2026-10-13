module

public import IntegerMultBounds.Sizes
public import IntegerMultBounds.Machine.CompactComplexLargeAxesStop

/-! The actual manuscript axis count eventually exceeds the symbolic stopping
threshold. This supplies the eventual exclusion of nonstopped exponent-one
nodes; it makes no assertion about the finite small-input regime. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexLargeAxesActual
noncomputable section
open Filter
open CompactComplexRecursiveGeometry (arity)
open Networks.ComplexRecursiveCallSchema (stopped)
attribute [local irreducible] arity

/-- The actual natural axis count tends to infinity as a real-valued sequence. -/
theorem tendsto_actual_axes : Tendsto (fun inputSize => (Sizes.d inputSize : ℝ)) atTop atTop := by
  have precisionGrowth : Tendsto
      (fun inputSize => TimeBound.precision inputSize^Parameters.epsilon/12) atTop atTop :=
    ((tendsto_rpow_atTop Sizes.epsilon_pos).comp TimeBound.tendsto_precision).atTop_div_const (by norm_num)
  exact tendsto_atTop_mono' atTop Sizes.eventually_d_ge precisionGrowth

/-- Any fixed natural axis threshold is eventually exceeded. Keep this
arithmetic generic before specializing to the manuscript stopping threshold. -/
theorem eventually_axes_above (requiredAxisCount : ℕ) :
    ∀ᶠ inputSize : ℕ in atTop,requiredAxisCount<Sizes.d inputSize := by
  have eventuallyRequiredAxes := tendsto_actual_axes.eventually_ge_atTop ((requiredAxisCount+1 : ℕ) : ℝ)
  filter_upwards [eventuallyRequiredAxes] with inputSize realAxesBound
  have naturalAxesBound : requiredAxisCount+1≤Sizes.d inputSize := by exact_mod_cast realAxesBound
  exact (Nat.lt_succ_self requiredAxisCount).trans_le naturalAxesBound

/-- The strict manuscript threshold is met without evaluating its enormous
fixed power, by specializing the generic natural-threshold theorem. -/
theorem eventually_large_actual_axes : ∀ᶠ inputSize : ℕ in atTop,arity^1000<Sizes.d inputSize :=
  eventually_axes_above (arity^1000)

/-- Exponent one is eventually a genuine leaf at the actual global axis count. -/
theorem eventually_one_stopped : ∀ᶠ inputSize : ℕ in atTop,stopped (Sizes.d inputSize) 1=true := by
  filter_upwards [eventually_large_actual_axes] with inputSize largeAxes
  exact CompactComplexLargeAxesStop.one_stopped (Sizes.d inputSize) largeAxes

/-- Eventually every actual nonstopped node has exponent at least two. -/
theorem eventually_nonstopped_exponent_ge_two :
    ∀ᶠ inputSize : ℕ in atTop,∀ nodeExponent,
      stopped (Sizes.d inputSize) nodeExponent=false → 2≤nodeExponent := by
  filter_upwards [eventually_large_actual_axes] with inputSize largeAxes
  intro nodeExponent nonstopped
  exact CompactComplexLargeAxesStop.nonstopped_exponent_ge_two (Sizes.d inputSize) nodeExponent largeAxes nonstopped

/-- The immediate child of an actual nonstopped node eventually has positive
exponent, as required by the positive-exponent recursive geometry. -/
theorem eventually_nonstopped_child_exponent_positive :
    ∀ᶠ inputSize : ℕ in atTop,∀ childExponent,
      stopped (Sizes.d inputSize) (childExponent+1)=false → 0<childExponent := by
  filter_upwards [eventually_large_actual_axes] with inputSize largeAxes
  intro childExponent nonstopped
  exact CompactComplexLargeAxesStop.nonstopped_child_exponent_positive
    (Sizes.d inputSize) childExponent largeAxes nonstopped

end
end IntegerMultBounds.Machine.CompactComplexLargeAxesActual
