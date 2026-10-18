module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerGuardPower
public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The actual guard factor in the closed compact recurrence fits the layer exponent gap. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
noncomputable section

private theorem absorbGuard {d g C tau lam lam' : ℝ}
    (hd : 1≤d) (hg : 0≤g) (hC : 1≤C) (ht0 : 0≤tau) (ht1 : tau≤1)
    (hgap : lam<lam') (hguard : g≤C*d^(lam'-lam)) :
    d^lam*g^tau≤C*d^lam' := by
  have hd0 : 0<d := by linarith
  have hC0 : 0≤C := by linarith
  have hdp : 1≤d^(lam'-lam) := Real.one_le_rpow hd (by linarith)
  have hCtau : C^tau≤C := Real.rpow_le_self_of_one_le hC ht1
  have hdtau : (d^(lam'-lam))^tau≤d^(lam'-lam) :=
    Real.rpow_le_self_of_one_le hdp ht1
  have hgpow := Real.rpow_le_rpow hg hguard ht0
  rw [Real.mul_rpow hC0 (Real.rpow_nonneg hd0.le _)] at hgpow
  have hg' : g^tau≤C*d^(lam'-lam) := hgpow.trans
    (mul_le_mul hCtau hdtau (Real.rpow_nonneg (Real.rpow_nonneg hd0.le _) _) hC0)
  calc
    d^lam*g^tau≤d^lam*(C*d^(lam'-lam)) :=
      mul_le_mul_of_nonneg_left hg' (Real.rpow_nonneg hd0.le _)
    _ = C*(d^lam*d^(lam'-lam)) := by ring
    _ = C*d^lam' := by rw [←Real.rpow_add hd0]; congr 1; congr 1; ring

/-- No chunk-width power remains: only the actual precision guard is absorbed. -/
theorem compactCaller_layer_guard_absorbed (M : ℕ) (hM : 2≤M)
    (lam lam' : ℝ) (hgap : lam<lam') :
    (Mult.Sizes.d M:ℝ)^lam*(Mult.CompactSizes.guard M:ℝ)^Parameters.tau≤
      compactCallerGuardPowerCoeff (lam'-lam)*(Mult.Sizes.d M:ℝ)^lam' := by
  have hC : 1≤compactCallerGuardPowerCoeff (lam'-lam) := by
    unfold compactCallerGuardPowerCoeff compactLayerDyadic
    exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  exact absorbGuard (by exact_mod_cast Mult.Sizes.one_le_d hM)
    (Nat.cast_nonneg _) hC (by norm_num [Parameters.tau]) (by norm_num [Parameters.tau])
    hgap (compactCaller_guard_power M hM (lam'-lam) (by linarith))

/-- The proposed dyadic compact layer exponent pays its full guard factor. -/
theorem compactCaller_interim_layer_growth (M : ℕ) (hM : 2≤M) :
    (Mult.Sizes.d M:ℝ)^CompactInterim.lam*(Mult.CompactSizes.guard M:ℝ)^Parameters.tau≤
      compactCallerGuardPowerCoeff (CompactInterim.lam'-CompactInterim.lam)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam' :=
  compactCaller_layer_guard_absorbed M hM CompactInterim.lam CompactInterim.lam'
    (by norm_num [CompactInterim.lam,CompactInterim.lam'])

end
end IntegerMultBounds.MathlibTM2.Cost
