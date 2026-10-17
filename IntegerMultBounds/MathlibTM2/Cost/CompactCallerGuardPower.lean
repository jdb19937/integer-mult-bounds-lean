module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLayerBound
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Actual original-precision guards fit any positive original-dimension power. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
noncomputable section

private theorem clog_succ_log (d : ℕ) (hd : 1≤d) :
    (Nat.clog 2 (d+1):ℝ)≤Real.logb 2 (d:ℝ)+2 := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : (0:ℝ)<(d+1:ℕ)) (show ((d+1:ℕ):ℝ)≤2*(d:ℝ) by push_cast; linarith)
  rw [Real.logb_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hd0),Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hlog
  have hceil := (Nat.ceil_lt_add_one
    (Real.logb_nonneg (b:=2) (by norm_num) (show (1:ℝ)≤(d+1:ℕ) by exact_mod_cast (by omega : 1≤d+1)))).le
  have he : ⌈Real.logb 2 ((d+1:ℕ):ℝ)⌉₊=Nat.clog 2 (d+1) := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (d+1)
  rw [he] at hceil
  linarith

/-- A dyadic coefficient bounding the actual guard by one plus log dimension. -/
def compactCallerGuardLogCoeff : ℝ :=
  compactLayerDyadic (18+8*((Mult.Sizes.cExp*Mult.Sizes.upperPower:ℕ):ℝ))

/-- Includes the concrete original precision, integer roots and ceiling logarithm. -/
theorem compactCaller_guard_log (M : ℕ) (hM : 2≤M) :
    (Mult.CompactSizes.guard M:ℝ)≤compactCallerGuardLogCoeff*(1+Real.logb 2 (Mult.Sizes.d M)) := by
  have hd := Mult.Sizes.one_le_d hM
  have hmono : Nat.clog 2 (Mult.Sizes.K M+1)≤Nat.clog 2 (Mult.Sizes.d M+1) :=
    Nat.clog_mono_right 2 (Nat.add_le_add_right (Mult.Sizes.K_le_d M) 1)
  have hp := (Mult.Sizes.clog_p_le M).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hmono) 3)
  have hpR : (Nat.clog 2 (Mult.Sizes.p M):ℝ)≤
      3+((Mult.Sizes.cExp*Mult.Sizes.upperPower:ℕ):ℝ)*(Nat.clog 2 (Mult.Sizes.d M+1):ℝ) := by
    exact_mod_cast hp
  have hlog := clog_succ_log (Mult.Sizes.d M) hd
  have hnonneg : 0≤Real.logb 2 (Mult.Sizes.d M) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)
  have hC := compactLayerDyadic_le (18+8*((Mult.Sizes.cExp*Mult.Sizes.upperPower:ℕ):ℝ))
  have hbound : (Mult.CompactSizes.guard M:ℝ)≤
      (18+8*((Mult.Sizes.cExp*Mult.Sizes.upperPower:ℕ):ℝ))*(1+Real.logb 2 (Mult.Sizes.d M)) := by
    have hprod := mul_le_mul_of_nonneg_left hlog
      (Nat.cast_nonneg (α:=ℝ) (Mult.Sizes.cExp*Mult.Sizes.upperPower))
    simp only [Mult.CompactSizes.guard,Mult.CompactSizes.p,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    push_cast at hpR hprod
    nlinarith [mul_nonneg (show (0:ℝ)≤Mult.Sizes.cExp*Mult.Sizes.upperPower by positivity) hnonneg]
  exact hbound.trans (mul_le_mul_of_nonneg_right hC (by linarith))

/-- All coefficients are rounded upward to powers of two. -/
def compactCallerGuardPowerCoeff (a : ℝ) : ℝ :=
  compactLayerDyadic (compactCallerGuardLogCoeff*(1+1/(a*Real.log 2)))

theorem compactCaller_guard_power (M : ℕ) (hM : 2≤M) (a : ℝ) (ha : 0<a) :
    (Mult.CompactSizes.guard M:ℝ)≤compactCallerGuardPowerCoeff a*(Mult.Sizes.d M:ℝ)^a := by
  have hd : (1:ℝ)≤Mult.Sizes.d M := by exact_mod_cast Mult.Sizes.one_le_d hM
  have hlog := Recurrence.one_add_logb_le (by norm_num : (1:ℝ)<2) hd ha
  have hC : 0≤compactCallerGuardLogCoeff := (compactLayerDyadic_pos _).le
  have hbound := mul_le_mul_of_nonneg_left hlog hC
  have hcoeff := mul_le_mul_of_nonneg_right
    (compactLayerDyadic_le (compactCallerGuardLogCoeff*(1+1/(a*Real.log 2))))
    (Real.rpow_nonneg (Nat.cast_nonneg (Mult.Sizes.d M)) a)
  exact (compactCaller_guard_log M hM).trans
    (hbound.trans (by simpa only [compactCallerGuardPowerCoeff,mul_assoc] using hcoeff))

end
end IntegerMultBounds.MathlibTM2.Cost
