module

public import IntegerMultBounds.Machine.CompactComplexActualCutoffBudget

/-! The original integer stopping classifier brackets the real cutoff width.
Its leaf and local powers therefore have precisely the manuscript beta
exponents, with the fixed arity loss confined to the negative local power. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexCutoffPowers
noncomputable section
open Networks
open CompactComplexRecursiveGeometry (arity)

private theorem thousandth_power (width : ℝ) (widthNonnegative : 0≤width) :
    (width^1000)^Parameters.beta=width := by
  rw [← Real.rpow_natCast_mul widthNonnegative]
  norm_num [Parameters.beta]

/-- The literal stopping cutoff lies between the original axis-to-beta width
and its quotient by the fixed motif arity, including exponent zero. -/
theorem cutoff_width_bounds (axes leafExponent : ℕ) (axesPositive : 0<axes)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped axes leafExponent=true)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped axes (leafExponent+1)=false) :
    (arity^leafExponent : ℕ)≤(axes : ℝ)^Parameters.beta ∧
      (axes : ℝ)^Parameters.beta≤(arity : ℝ)*(arity^leafExponent : ℕ) := by
  have betaNonnegative : 0≤Parameters.beta := by norm_num [Parameters.beta]
  have lower : (arity^leafExponent : ℕ)≤(axes : ℝ)^Parameters.beta := by
    rcases (ComplexRecursiveCallSchema.stopped_iff axes leafExponent).1 cutoffStopped with
      leafZero | stoppedWidth
    · rw [leafZero,pow_zero,Nat.cast_one]
      exact Real.one_le_rpow (by exact_mod_cast axesPositive) betaNonnegative
    · have integerBound : ((arity^leafExponent)^1000 : ℕ)≤axes := stoppedWidth.le
      have realBound := Real.rpow_le_rpow
        (Nat.cast_nonneg ((arity^leafExponent)^1000) : (0 : ℝ)≤((arity^leafExponent)^1000 : ℕ))
        (Nat.cast_le (α:=ℝ).mpr integerBound) betaNonnegative
      rw [Nat.cast_pow,thousandth_power _ (Nat.cast_nonneg _)] at realBound
      exact realBound
  have notStopped : ¬(leafExponent+1=0 ∨ (arity^(leafExponent+1))^1000<axes) :=
    of_decide_eq_false aboveCutoff
  have integerBound : axes≤(arity^(leafExponent+1))^1000 := by
    by_contra noBound
    exact notStopped (Or.inr (by omega))
  have realBound := Real.rpow_le_rpow (Nat.cast_nonneg axes : (0 : ℝ)≤axes)
    (Nat.cast_le (α:=ℝ).mpr integerBound) betaNonnegative
  rw [Nat.cast_pow,thousandth_power _ (Nat.cast_nonneg _),pow_succ,Nat.cast_mul,mul_comm] at realBound
  exact ⟨lower,realBound⟩

/-- The cutoff leaf contribution has exactly the manuscript beta times
one-minus-sigma exponent; no leaf width or recursion-depth coefficient remains. -/
theorem leaf_power_bound (axes leafExponent : ℕ) (axesPositive : 0<axes)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped axes leafExponent=true)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped axes (leafExponent+1)=false) :
    ((arity^leafExponent : ℕ) : ℝ)^(1-Parameters.sigma)≤
      (axes : ℝ)^(Parameters.beta*(1-Parameters.sigma)) := by
  have widthBound := (cutoff_width_bounds axes leafExponent axesPositive cutoffStopped aboveCutoff).1
  have exponentNonnegative : 0≤1-Parameters.sigma :=
    sub_nonneg.mpr CompactComplexRecursiveRuntimeSum.exponents.2.2.le
  have bound := Real.rpow_le_rpow (Nat.cast_nonneg _) widthBound exponentNonnegative
  rw [← Real.rpow_mul (Nat.cast_nonneg axes)] at bound
  exact bound

/-- The negative local cutoff power is bounded using the other classifier
edge. The sole rounding loss is a fixed arity-to-sigma-minus-tau factor. -/
theorem local_power_bound (axes leafExponent : ℕ) (axesPositive : 0<axes)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped axes leafExponent=true)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped axes (leafExponent+1)=false) :
    ((arity^leafExponent : ℕ) : ℝ)^(Parameters.tau-Parameters.sigma)≤
      (arity : ℝ)^(Parameters.sigma-Parameters.tau)*
        (axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma)) := by
  have widthBound := (cutoff_width_bounds axes leafExponent axesPositive cutoffStopped aboveCutoff).2
  have axesPowerPositive : 0<(axes : ℝ)^Parameters.beta :=
    Real.rpow_pos_of_pos (by exact_mod_cast axesPositive) _
  have exponentNonpositive : Parameters.tau-Parameters.sigma≤0 :=
    sub_nonpos.mpr CompactComplexRecursiveRuntimeSum.exponents.2.1
  have bound := Real.rpow_le_rpow_of_nonpos axesPowerPositive widthBound exponentNonpositive
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),←Real.rpow_mul (Nat.cast_nonneg axes)] at bound
  have arityPowerPositive : 0<(arity : ℝ)^(Parameters.tau-Parameters.sigma) :=
    Real.rpow_pos_of_pos (by norm_num [arity]) _
  have inverseEquation : ((arity : ℝ)^(Parameters.tau-Parameters.sigma))⁻¹=
      (arity : ℝ)^(Parameters.sigma-Parameters.tau) := by
    rw [←Real.rpow_neg (Nat.cast_nonneg arity)]
    congr 1
    ring
  have result : ((arity^leafExponent : ℕ) : ℝ)^(Parameters.tau-Parameters.sigma)≤
      (axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma))/
        (arity : ℝ)^(Parameters.tau-Parameters.sigma) :=
    (le_div_iff₀ arityPowerPositive).2 (by simpa only [mul_comm] using bound)
  rw [div_eq_mul_inv,inverseEquation,mul_comm] at result
  exact result

end
end IntegerMultBounds.Machine.CompactComplexCutoffPowers
