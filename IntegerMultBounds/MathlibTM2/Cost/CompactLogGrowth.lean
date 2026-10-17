module

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Dyadic logarithm bounds independent of the multiplication size parameters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
noncomputable section

/-- `⌊log₂ m⌋ + 1 ≤ 512 m^{1/256}` for `m ≥ 1`. -/
theorem compact_natLog_succ_le {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ 512 * (m : ℝ) ^ (1 / 256 : ℝ) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by exact_mod_cast Real.natLog_le_logb m 2
  have h2 : Real.log m ≤ (m : ℝ) ^ (1 / 256 : ℝ) / (1 / 256) := Real.log_le_rpow_div hm0 (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have h3 : Real.logb 2 m ≤ 511 * (m : ℝ) ^ (1 / 256 : ℝ) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : (0 : ℝ) ≤ (m : ℝ) ^ (1 / 256 : ℝ) := by positivity
    nlinarith
  have h4 : (1 : ℝ) ≤ (m : ℝ) ^ (1 / 256 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  push_cast
  linarith

/-- The Schönhage–Strassen step bound against `m^{1+δ}`, `δ = 1/128`:
`m (⌊log₂ m⌋ + 1)(⌊log₂ ⌊log₂ m⌋⌋ + 1) ≤ 262144 m^{129/128}`. -/
theorem compact_mLogLog_le {m : ℕ} (hm : 1 ≤ m) :
    ((m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) : ℕ) : ℝ) ≤
      262144 * (m : ℝ) ^ (129 / 128 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : Nat.log 2 (Nat.log 2 m) + 1 ≤ Nat.log 2 m + 1 :=
    Nat.succ_le_succ (Nat.log_le_self 2 _)
  have h2 : ((m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) : ℕ) : ℝ) ≤
      (m : ℝ) * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 2 := by
    have : m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) ≤
        m * (Nat.log 2 m + 1) ^ 2 := by
      rw [sq, ← mul_assoc]; exact Nat.mul_le_mul_left _ h1
    exact_mod_cast this
  have h3 := compact_natLog_succ_le hm
  have h4 : ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 2 ≤ (512 * (m : ℝ) ^ (1 / 256 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2
  have e : (m : ℝ) * (512 * (m : ℝ) ^ (1 / 256 : ℝ)) ^ 2 = 262144 * (m : ℝ) ^ (129 / 128 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (1 / 256 : ℝ)), ← Real.rpow_mul hm0.le,
      show (129 / 128 : ℝ) = 1 + 1 / 256 * ((2 : ℕ) : ℝ) by norm_num, Real.rpow_add hm0,
      Real.rpow_one]
    ring
  calc _ ≤ (m : ℝ) * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 2 := h2
    _ ≤ (m : ℝ) * (512 * (m : ℝ) ^ (1 / 256 : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left h4 hm0.le
    _ = 262144 * (m : ℝ) ^ (129 / 128 : ℝ) := e

end
end IntegerMultBounds.MathlibTM2.Cost
