module

import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Cost.Total
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Linear-axis routing scale
This scale applies to the new CRT schedule and to the already-linear
resampling interchanges. It does not assert that the running multiplier has
switched to the new CRT implementation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes

noncomputable def totDirectCRT (n : ℕ) : ℝ :=
  (T n : ℝ) * p n * d n * (1 + (ℓ n : ℝ) ^ Parameters.tau)

theorem mt_directCRT_nonneg (n : ℕ) : 0 ≤ totDirectCRT n := by
  unfold totDirectCRT
  positivity

theorem mt_directCRT_swap_le (n : ℕ) :
    (d n : ℝ) * (T n * p n * (ℓ n : ℝ) ^ Parameters.tau) ≤ totDirectCRT n := by
  have h : (0 : ℝ) ≤ T n * p n * d n := by positivity
  unfold totDirectCRT
  nlinarith

theorem mt_directCRT_dTp_le (n : ℕ) :
    (d n : ℝ) * (T n * p n) ≤ totDirectCRT n := by
  have h : (0 : ℝ) ≤ (T n : ℝ) * p n * d n * (ℓ n : ℝ) ^ Parameters.tau := by positivity
  unfold totDirectCRT
  nlinarith

theorem mt_directCRT_dT_le {n : ℕ} (h : Big n) :
    (d n : ℝ) * T n ≤ totDirectCRT n := by
  have hp := mt_one_le_p h
  have hdt : (0 : ℝ) ≤ (d n : ℝ) * T n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hp hdt
  have h := mt_directCRT_dTp_le n
  nlinarith

/-- Compatibility with the old quadratic envelope while the driver is replaced. -/
theorem mt_directCRT_le_old {n : ℕ} (h : Big n) : totDirectCRT n ≤ totCRT n := by
  have hd : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hd' : (d n : ℝ) ≤ (d n : ℝ) ^ 2 := by nlinarith
  unfold totDirectCRT totCRT
  gcongr

end IntegerMultBounds.MathlibTM2.Cost
