module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
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
theorem compactCaller_uniform_eventually_shape : ∀ᶠ N : ℕ in atTop,
    ∀ K D o r w : ℕ, Mult.Sizes.K N≤K → K≤Mult.Sizes.d N → D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D →
      Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w →
      let shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D (2^o*(3*(r*w)))
      1 ≤ shape.guard ∧ shape.guard+1 ≤ shape.chunk ∧ shape.bits+1 ≤ shape.payload := by
  filter_upwards [eventually_ge_atTop 2, compactCaller_runtime_eventually_guard,
    Mult.Sizes.eventually_pow_p_le_r 1] with N hN hguard haxis
  intro K D o r w hlo hhi hD hfit hr hw
  have hK : 0 < K := by omega
  have hb := Mult.Sizes.one_le_b hN
  have hp : 2 ≤ Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hrp : Mult.Sizes.p N ≤ r := by simpa only [pow_one] using haxis.trans hr
  have hprod : D*K ≤ Mult.Sizes.b N*Mult.Sizes.b N :=
    Nat.mul_le_mul (hD.trans (Mult.Sizes.d_le_b N))
      (hhi.trans (Mult.Sizes.d_le_b N))
  have hs : D*K+1 ≤ Mult.Sizes.p N^2 := by
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
  · change CompactReservationGrowth.guard N+1 ≤ K
    unfold CompactReservationGrowth.guard
    omega
  · rw [compactReservation_bits hK hfit]
    change K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+1 ≤ 2^o*(3*(r*w))
    have hbits := Nat.mul_le_mul_left K
      (Nat.sub_le D (CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))
    nlinarith

theorem compactCaller_retuned_eventually_shape : ∀ᶠ N : ℕ in atTop,
    ∀ D o r w : ℕ, D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.CompactSizes.K N) D →
      Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w →
      let shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.CompactSizes.K N) D (2^o*(3*(r*w)))
      1 ≤ shape.guard ∧ shape.guard+1 ≤ shape.chunk ∧ shape.bits+1 ≤ shape.payload := by
  filter_upwards [compactCaller_uniform_eventually_shape] with N hshape
  intro D o r w
  exact hshape (Mult.CompactSizes.K N) D o r w
    (Mult.CompactSizes.old_K_le_K N) (Mult.CompactSizes.K_le_d N)

end
end IntegerMultBounds.MathlibTM2.Cost
