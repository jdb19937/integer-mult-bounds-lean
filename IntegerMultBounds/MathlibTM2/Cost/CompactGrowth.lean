module

import IntegerMultBounds.MathlibTM2.Cost.Growth
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Analytic size bounds for the actual half-dimension compact chunk. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactTotal
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Mult.Sizes hiding K
noncomputable section

abbrev K := Mult.CompactSizes.K
abbrev kappa := CompactInterim.kappa
abbrev lam' := CompactInterim.lam'

/-- `B^{εa} ≤ 4 K^a` for `0 ≤ a ≤ 1`: `B^ε ≤ 2d ≤ 4 Kroot ≤ 4K`. -/
theorem compact_rpow_le_four_K_rpow {n : ℕ} (hK : 1≤K n) {a : ℝ}
    (ha : 0≤a) (ha1 : a≤1) : (b n:ℝ)^(epsilon*a)≤4*(K n:ℝ)^a := by
  have hd : 1≤d n := hK.trans (Mult.CompactSizes.K_le_d n)
  have hbase : (b n:ℝ)^epsilon≤4*K n := by
    have h1 := gr_rpow_le_two_d hd
    have h2 : (d n:ℝ)≤2*K n := by
      exact_mod_cast (Mult.CompactSizes.d_le_two_Kroot n).trans
        (Nat.mul_le_mul_left 2 (Mult.CompactSizes.Kroot_le_K n))
    linarith
  rw [Real.rpow_mul (Nat.cast_nonneg _)]
  calc
    _ ≤ (4*(K n:ℝ))^a := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hbase ha
    _ = (4:ℝ)^a*(K n:ℝ)^a := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 4*(K n:ℝ)^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num) ha1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end IntegerMultBounds.MathlibTM2.Cost.CompactTotal
