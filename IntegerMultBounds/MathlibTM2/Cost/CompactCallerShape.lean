module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Primitive shared-shape obligations from the actual multiplier sizes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer Filter
noncomputable section

/-- Guard room and record capacity follow from original runtime sizes, uniformly
in the selected dimension and folded low offset. -/
theorem compactCaller_runtime_eventually_shape : ∀ᶠ N : ℕ in atTop,
    ∀ D o r w : ℕ, D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D →
      Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w →
      let shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D (2^o*(3*(r*w)))
      1 ≤ shape.guard ∧ shape.guard+1 ≤ shape.chunk ∧ shape.bits+1 ≤ shape.payload := by
  filter_upwards [eventually_ge_atTop 2, compactCaller_runtime_eventually_guard,
    Mult.Sizes.eventually_pow_p_le_r 1] with N hN hguard haxis
  intro D o r w hD hfit hr hw
  have hK : 0 < Mult.Sizes.K N := by omega
  have hb := Mult.Sizes.one_le_b hN
  have hp : 2 ≤ Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hrp : Mult.Sizes.p N ≤ r := by simpa only [pow_one] using haxis.trans hr
  have hprod : D*Mult.Sizes.K N ≤ Mult.Sizes.b N*Mult.Sizes.b N :=
    Nat.mul_le_mul (hD.trans (Mult.Sizes.d_le_b N))
      ((Mult.Sizes.K_le_d N).trans (Mult.Sizes.d_le_b N))
  have hs : D*Mult.Sizes.K N+1 ≤ Mult.Sizes.p N^2 := by
    unfold Mult.Sizes.p
    nlinarith
  have hprodRW : Mult.Sizes.p N^2 ≤ r*w := by
    simpa only [pow_two] using Nat.mul_le_mul hrp hw
  have hfold : 3*(r*w) ≤ 2^o*(3*(r*w)) :=
    Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  refine ⟨?_, ?_, ?_⟩
  · change 1 ≤ CompactReservationGrowth.guard N
    unfold CompactReservationGrowth.guard
    omega
  · change CompactReservationGrowth.guard N+1 ≤ Mult.Sizes.K N
    unfold CompactReservationGrowth.guard
    omega
  · rw [compactReservation_bits hK hfit]
    change Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+1 ≤ 2^o*(3*(r*w))
    have hbits := Nat.mul_le_mul_left (Mult.Sizes.K N)
      (Nat.sub_le D (CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))
    nlinarith

end
end IntegerMultBounds.MathlibTM2.Cost
