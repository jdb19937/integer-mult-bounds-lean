module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerParameters
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import IntegerMultBounds.Machine.CompactReservationGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactParameters
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
open ActivePrefixStageFullData Filter
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

/-- Actual multiplier sizes discharge both repair phases. The remaining premises
are the shared reservation capacity, actual row stock and coefficient geometry. -/
theorem compactCaller_runtime_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (D o r w extra : ℕ)
      (d : Inputs (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D (2^o*(3*(r*w))))),
      D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D →
      d.rows ≤ 2^extra*CompactGlobalRowPadding.initialRows NW m
        (Mult.Sizes.d N) (Mult.Sizes.K N) →
      extra ≤ Mult.Sizes.p N → Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w →
      ActivePrefixStageRuntimeData.Packed d 1 := by
  filter_upwards [eventually_ge_atTop 2, compactCaller_runtime_eventually_guard,
    Mult.Sizes.eventually_pow_p_le_r 1] with N hN hguard haxis
  intro D o r w extra d hD hfit hrows hextra hr hw
  have hK : 0 < Mult.Sizes.K N := by omega
  have hb := Mult.Sizes.one_le_b hN
  have hp6 : 6 ≤ Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hprod : D*Mult.Sizes.K N ≤ Mult.Sizes.b N*Mult.Sizes.b N :=
    Nat.mul_le_mul (hD.trans (Mult.Sizes.d_le_b N))
      ((Mult.Sizes.K_le_d N).trans (Mult.Sizes.d_le_b N))
  have hs : D*Mult.Sizes.K N+3 ≤ Mult.Sizes.p N^2 := by
    unfold Mult.Sizes.p
    nlinarith
  have haddress := compactCaller_address_le (payload := 2^o*(3*(r*w))) hK hfit hrows
  have haddr : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤
      Mult.Sizes.p N^2+Mult.Sizes.p N := by
    rw [Nat.mul_comm D] at hs
    omega
  have hrp : Mult.Sizes.p N ≤ r := by simpa only [pow_one] using haxis.trans hr
  have hprodRW : Mult.Sizes.p N^2 ≤ r*w := by
    simpa only [pow_two] using Nat.mul_le_mul hrp hw
  have hfold : 3*(r*w) ≤ 2^o*(3*(r*w)) :=
    Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  have hrecord : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤ 2^o*(3*(r*w)) := by
    nlinarith
  have hcubeNat : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤ Mult.Sizes.p N^3 := by
    have hmul := Nat.mul_le_mul_right (Mult.Sizes.p N^2) (show 2 ≤ Mult.Sizes.p N by omega)
    nlinarith
  have hfNat : d.stage.f-1 ≤ Mult.Sizes.p N := by
    have hf : d.stage.f ≤ Mult.Sizes.d N := d.stage.widthFits
    have hd := Mult.Sizes.d_le_b N
    unfold Mult.Sizes.p
    omega
  have hell : (Mult.Sizes.p N : ℝ) ≤ (2:ℝ)^CompactScalarAllowances.guardLog N := by
    rw [compactCaller_runtime_guardLog hN]
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (Mult.Sizes.p N)
  exact compactRuntimePacked_of_dyadic d (Mult.Sizes.p N) (CompactScalarAllowances.guardLog N)
    (by exact_mod_cast (show 0 < Mult.Sizes.p N by omega))
    (by exact_mod_cast hfNat) hell hguard rfl hrecord (by exact_mod_cast hcubeNat)

end
end IntegerMultBounds.MathlibTM2.Cost
