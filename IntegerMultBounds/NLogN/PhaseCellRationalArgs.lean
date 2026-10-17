module

public import IntegerMultBounds.NLogN.PhaseCell
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Executable rational exponent arguments for the selected phase-cell samples.
Integer division implements the existing upward-tie nearest rounding. Natural
`u` represents the squared Gaussian width; no real floor or exponential is
evaluated by these argument constructors. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

def nearestQ (s t : ℕ) (j : ℤ) : ℤ := (2*(t : ℤ)*j+s) / (2*(s : ℤ))

def betaQ (s t : ℕ) (j : ℤ) : ℚ := (t : ℚ)*j/s-nearestQ s t j

def potentialQ (s t u : ℕ) (j : ℤ) : ℚ :=
  (u : ℚ)*(1/4-betaQ s t j^2)/((t : ℚ)/s-1)

def gaussianQ (s t u : ℕ) (δ : ℤ) : ℚ := (u : ℚ)*((t : ℚ)/s)*(δ : ℚ)^2

theorem nearestQ_eq (s t : ℕ) (hs : 0 < s) (j : ℤ) :
    nearestQ s t j = nearest ((t : ℝ)*j/s) := by
  have hsZ : (0 : ℤ) < 2*(s : ℤ) := by omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have heq := Int.mul_ediv_add_emod (2*(t : ℤ)*j+s) (2*(s : ℤ))
  have hlo := Int.emod_nonneg (2*(t : ℤ)*j+s) hsZ.ne'
  have hhi := Int.emod_lt_of_pos (2*(t : ℤ)*j+s) hsZ
  have heqR : 2*(s : ℝ)*(nearestQ s t j : ℝ)+
      (((2*(t : ℤ)*j+s) % (2*(s : ℤ)) : ℤ) : ℝ) = 2*(t : ℝ)*j+s := by
    exact_mod_cast heq
  have hloR : (0 : ℝ) ≤ (((2*(t : ℤ)*j+s) % (2*(s : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (((2*(t : ℤ)*j+s) % (2*(s : ℤ)) : ℤ) : ℝ) < 2*s := by
    exact_mod_cast hhi
  symm
  unfold nearest
  apply Int.floor_eq_iff.mpr
  have hdiv := div_mul_cancel₀ ((t : ℝ)*j) hsR.ne'
  constructor
  · apply (mul_le_mul_iff_right₀ hsR).mp
    nlinarith
  · apply (mul_lt_mul_iff_right₀ hsR).mp
    nlinarith

theorem betaQ_cast (s t : ℕ) (hs : 0 < s) (j : ℤ) :
    (betaQ s t j : ℝ) = beta s t j := by
  simp only [betaQ, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_intCast, nearestQ_eq s t hs j, beta, frac]

theorem potentialQ_cast (s t u : ℕ) (hs : 0 < s) (α : ℝ)
    (hu : α^2=(u : ℝ)) (j : ℤ) :
    (potentialQ s t u j : ℝ) = PhaseCell.potential s t α j := by
  simp [potentialQ, PhaseCell.potential, betaQ_cast s t hs, hu]

theorem potentialQ_nonneg (s t u : ℕ) (hs : 0 < s)
    (htheta : 0 < (t : ℝ)/s-1) (j : ℤ) : 0 ≤ potentialQ s t u j := by
  have hb : betaQ s t j^2 ≤ (1 : ℚ)/4 := by
    have h := sq_beta_le s t j
    rw [← betaQ_cast s t hs j] at h
    exact (Rat.cast_le (K := ℝ)).mp (by simpa using h)
  have hden : (0 : ℚ) < (t : ℚ)/s-1 :=
    (Rat.cast_pos (K := ℝ)).mp (by simpa using htheta)
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg u) (sub_nonneg.mpr hb)) hden.le

theorem gaussianQ_cast (s t u : ℕ) (α : ℝ) (hu : α^2=(u : ℝ)) (δ : ℤ) :
    (gaussianQ s t u δ : ℝ) = α^2*((t : ℝ)/s)*(δ : ℝ)^2 := by
  simp [gaussianQ, hu]

theorem gaussianQ_nonneg (s t u : ℕ) (δ : ℤ) : 0 ≤ gaussianQ s t u δ := by
  unfold gaussianQ
  positivity

theorem gaussianQ_neg (s t u : ℕ) (δ : ℤ) :
    gaussianQ s t u (-δ) = gaussianQ s t u δ := by simp [gaussianQ]

/-- Encoding a nonnegative rational by a natural numerator loses no sign or
precision; every rational denominator is already strictly positive. -/
theorem natural_encoding (q : ℚ) (hq : 0 ≤ q) :
    (q.num.toNat : ℚ)/(q.den : ℚ)=q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hc : (q.num.toNat : ℚ)=(q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [hc]
  exact q.num_div_den

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
