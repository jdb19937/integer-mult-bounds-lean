module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerParameters
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Compact caller bounds for the computable multiplier parameter generator.
Only its precision agrees with the manuscript regime; its dimension and chunk
are used directly, without identifying the two different exponent choices. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open Filter
noncomputable section

/-- The actual working precision uses the same logarithmic guard. -/
theorem compactCaller_runtime_guardLog {N : ℕ} (hN : 2 ≤ N) :
    CompactScalarAllowances.guardLog N = Nat.clog 2 (Mult.Sizes.p N) := by
  unfold CompactScalarAllowances.guardLog Mult.Sizes.p Mult.Sizes.b
  rw [Sizes.b_eq_clog hN]

/-- The actual integer-root chunk eventually pays the complete guard allowance. -/
theorem compactCaller_runtime_eventually_guard : ∀ᶠ N : ℕ in atTop,
    8*CompactScalarAllowances.guardLog N+16 ≤ Mult.Sizes.K N := by
  filter_upwards [eventually_ge_atTop 2, Mult.Sizes.eventually_clog_p_le_K 24] with N hN hK
  have hb := Mult.Sizes.one_le_b hN
  have hp : 2 ≤ Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hl : 1 ≤ Nat.clog 2 (Mult.Sizes.p N) := Nat.clog_pos (by decide) hp
  rw [compactCaller_runtime_guardLog hN]
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
