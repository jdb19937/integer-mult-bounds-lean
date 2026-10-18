module

import IntegerMultBounds.MathlibTM2.Cost.Growth
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Analytic size bounds for the actual eighth-root compact chunk. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactTotal
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Mult.Sizes hiding K cParam
noncomputable section

abbrev K := Mult.CompactSizes.K
abbrev cParam := Mult.CompactSizes.cParam
abbrev kappa := CompactInterim.kappa
abbrev lam' := CompactInterim.lam'

lemma compact_cParam_pos : 0<cParam := Mult.CompactSizes.cParam_pos
lemma compact_cParam_le_one : cParam≤1 := by
  change Mult.CompactSizes.cParam≤1
  rw [Mult.CompactSizes.cParam_eq]
  norm_num

theorem compact_K_le_d_rpow (n : ℕ) : (K n:ℝ)≤2*(d n:ℝ)^cParam := by
  change (Mult.CompactSizes.K n:ℝ)≤2*(d n:ℝ)^Mult.CompactSizes.cParam
  have h2 : (Mult.CompactSizes.K n:ℝ)≤2*Mult.CompactSizes.Kroot n := by
    exact_mod_cast Mult.CompactSizes.K_le_two_Kroot n
  have hr : (Mult.CompactSizes.Kroot n:ℝ)≤(d n:ℝ)^Mult.CompactSizes.cParam := by
    rw [Mult.CompactSizes.Kroot_eq_floor]
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

theorem compact_d_rpow_le_two_K {n : ℕ} (hK : 1≤K n) : (d n:ℝ)^cParam≤2*K n := by
  have hf := Nat.lt_floor_add_one ((d n:ℝ)^cParam)
  rw [←Mult.CompactSizes.Kroot_eq_floor] at hf
  have hk : (1:ℝ)≤Mult.CompactSizes.Kroot n := by
    have := Mult.CompactSizes.K_le_two_Kroot n
    change 1≤Mult.CompactSizes.K n at hK
    exact_mod_cast (show 1≤Mult.CompactSizes.Kroot n by omega)
  have hrk : (Mult.CompactSizes.Kroot n:ℝ)≤K n := by exact_mod_cast Mult.CompactSizes.Kroot_le_K n
  linarith

theorem compact_K_le_rpow (n : ℕ) : (K n:ℝ)≤2*(b n:ℝ)^(epsilon*cParam) :=
  (compact_K_le_d_rpow n).trans (mul_le_mul_of_nonneg_left
    (gr_d_rpow_le n compact_cParam_pos.le) (by norm_num))

theorem compact_rpow_le_four_K_rpow {n : ℕ} (hK : 1≤K n) {a : ℝ}
    (ha : 0≤a) (ha1 : a≤1) : (b n:ℝ)^(epsilon*cParam*a)≤4*(K n:ℝ)^a := by
  have hd : 1≤d n := hK.trans (Mult.CompactSizes.K_le_d n)
  have hbase : (b n:ℝ)^(epsilon*cParam)≤4*K n := by
    calc
      _ ≤ 2*(d n:ℝ)^cParam :=
        gr_rpow_le_two_d_rpow hd compact_cParam_pos.le compact_cParam_le_one
      _ ≤ 2*(2*(K n:ℝ)) := mul_le_mul_of_nonneg_left (compact_d_rpow_le_two_K hK) (by norm_num)
      _ = _ := by ring
  rw [Real.rpow_mul (Nat.cast_nonneg _)]
  calc
    _ ≤ (4*(K n:ℝ))^a := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hbase ha
    _ = (4:ℝ)^a*(K n:ℝ)^a := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 4*(K n:ℝ)^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num) ha1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end IntegerMultBounds.MathlibTM2.Cost.CompactTotal
