module

public import IntegerMultBounds.Resampling.WeightNat
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.Machine

/-!
# Corrected downward samples from the executable exponential routine

`sample` uses the existing natural-number `expPiNat` evaluator, subtracts two
with natural truncation at zero, and divides by the P-grid scale. It is not the
ideal floor specification and no equality to that floor is claimed.

`Resampling.ExpTape.expNeg_hoare` already executes the uncorrected `expPiNat true`
in the repository's native register/tape model. This file proves the corrected
arithmetic result; it neither compiles the correction to that model nor bridges
that machine to MathlibTM2. Rational arguments for the similarity/Gaussian
samples and transfer into the structured coefficient constructor remain separate.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellExpSample

open IntegerMultBounds.Resampling

/-- Executable corrected numerator. Natural subtraction clamps at zero. -/
def numerator (P aa b : ℕ) : ℕ := WeightNat.expPiNat true P aa b - 2

/-- A rational P-grid sample produced by actual integer arithmetic. -/
def sample (P aa b : ℕ) : ℚ := (numerator P aa b : ℚ) / (2 : ℚ) ^ P

private theorem correction_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (herr : |(n : ℝ) - x| ≤ 3 / 2) :
    ((n-2 : ℕ) : ℝ) ≤ x ∧ x - ((n-2 : ℕ) : ℝ) ≤ 7 / 2 := by
  have h := abs_le.mp herr
  by_cases hn : 2 ≤ n
  · rw [Nat.cast_sub hn]
    norm_num
    constructor <;> linarith
  · have hn1 : n ≤ 1 := by omega
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hn1
    have hn2 : n-2=0 := by omega
    rw [hn2, Nat.cast_zero]
    constructor <;> linarith

/-- The actual expPiNat routine's error, before correction. -/
theorem raw_error (P aa b : ℕ) (hP : 13 ≤ P) (hb : 0 < b) :
    |(WeightNat.expPiNat true P aa b : ℝ) -
      2 ^ P * Real.exp (-(Real.pi * aa / b))| ≤ 3 / 2 := by
  have h := WeightTable.expPi_neg_err P aa b hP hb
  rw [WeightNat.expPi_eq_nat true P aa b hP] at h
  simpa only [Int.cast_natCast] using h

/-- Correcting by two removes any possible overshoot. -/
theorem numerator_bounds (P aa b : ℕ) (hP : 13 ≤ P) (hb : 0 < b) :
    (numerator P aa b : ℝ) ≤ 2 ^ P * Real.exp (-(Real.pi * aa / b)) ∧
    2 ^ P * Real.exp (-(Real.pi * aa / b)) - (numerator P aa b : ℝ) ≤ 7 / 2 :=
  correction_bounds _ (by positivity) (raw_error P aa b hP hb)

theorem sample_nonneg (P aa b : ℕ) : 0 ≤ sample P aa b := by
  unfold sample
  positivity

/-- A downward sample with the sharper absolute error `(7/2)/2^P`. -/
theorem sample_bounds (P aa b : ℕ) (hP : 13 ≤ P) (hb : 0 < b) :
    (sample P aa b : ℝ) ≤ Real.exp (-(Real.pi * aa / b)) ∧
    Real.exp (-(Real.pi * aa / b)) - (sample P aa b : ℝ) ≤ (7 / 2) / 2 ^ P := by
  have h := numerator_bounds P aa b hP hb
  have hpow : (0 : ℝ) < 2 ^ P := by positivity
  have heq : (sample P aa b : ℝ) = (numerator P aa b : ℝ) / 2 ^ P := by simp [sample]
  rw [heq]
  constructor
  · apply (div_le_iff₀ hpow).mpr
    nlinarith [h.1]
  · apply (mul_le_mul_iff_right₀ hpow).mp
    field_simp
    nlinarith [h.2]

/-- The selected corrected-routine guarantee: nonnegative, downward, and within
four P-grid units of the exact real exponential. -/
theorem sample_spec (P aa b : ℕ) (hP : 13 ≤ P) (hb : 0 < b) :
    0 ≤ (sample P aa b : ℝ) ∧
    (sample P aa b : ℝ) ≤ Real.exp (-(Real.pi * aa / b)) ∧
    |(sample P aa b : ℝ) - Real.exp (-(Real.pi * aa / b))| ≤ 4 / 2 ^ P := by
  have h := sample_bounds P aa b hP hb
  refine ⟨by exact_mod_cast sample_nonneg P aa b, h.1, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr h.1)]
  have hgrid : (7 / 2 : ℝ) / 2 ^ P ≤ 4 / 2 ^ P := by gcongr; norm_num
  linarith [h.2]

/-- Positivity follows when the target exponential exceeds the certified error. -/
theorem sample_pos (P aa b : ℕ) (hP : 13 ≤ P) (hb : 0 < b)
    (hlarge : 4 / (2 : ℝ) ^ P < Real.exp (-(Real.pi * aa / b))) :
    0 < sample P aa b := by
  have h := (sample_spec P aa b hP hb).2.2
  have h' := abs_le.mp h
  exact_mod_cast (show (0 : ℝ) < sample P aa b by linarith)

/-- Every corrected sample is a rational dyadic with this explicit numerator. -/
theorem sample_grid (P aa b : ℕ) : sample P aa b * (2 : ℚ) ^ P = numerator P aa b := by
  unfold sample
  exact div_mul_cancel₀ _ (by positivity)

end IntegerMultBounds.NLogN.PhaseCellExpSample
