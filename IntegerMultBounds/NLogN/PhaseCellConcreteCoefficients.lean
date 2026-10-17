module

public import IntegerMultBounds.NLogN.PhaseCellExecutableCoefficients
public import IntegerMultBounds.NLogN.PhaseCellRationalArgs
import IntegerMultBounds.NLogN.PhaseCellWeightBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.Machine

/-!
# Concrete executable phase-cell coefficients

Rational nearest rounding and rational Gaussian exponents feed the existing
corrected natural exponential evaluator. Every coefficient constructor here is
ordinary executable arithmetic. The selected precision supplies positive
similarity samples and the error margin without an argument-mapping oracle.
This remains the within-cell, unaliased matrix; cross-cell sampling, periodic
aliases, band tails, row-norm assembly and tape costs are not asserted.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients

open PhaseCellExecutableCoefficients

/-- Encode a rational exponent using the existing natural exponential API.
Correctness of the encoding is used only for nonnegative exponents. -/
def encode (q : ℚ) : ExpArg := ⟨q.num.toNat, q.den, q.den_pos⟩

def similarityArg (s t u : ℕ) (j : ℤ) : ExpArg :=
  encode (PhaseCellRationalArgs.potentialQ s t u j)

def gaussianArg (s t u : ℕ) (δ : ℤ) : ExpArg :=
  encode (PhaseCellRationalArgs.gaussianQ s t u δ)

def similarity (P s t u : ℕ) (j : ℤ) : ℚ := (similarityArg s t u j).value P

def kernel (P s t u w : ℕ) (δ : ℤ) : ℚ :=
  PhaseCellExecutableCoefficients.kernel P w (gaussianArg s t u) δ

def entry (P s t u w : ℕ) (j k : ℤ) : ℚ :=
  PhaseCellExecutableCoefficients.entry P w (similarityArg s t u) (gaussianArg s t u) j k

theorem encode_target (q : ℚ) (hq : 0 ≤ q) :
    (encode q).target = Real.exp (-Real.pi * (q : ℝ)) := by
  have h : (q.num.toNat : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) (PhaseCellRationalArgs.natural_encoding q hq)
    simpa using hcast
  unfold ExpArg.target encode
  congr 1
  rw [show -(Real.pi * (q.num.toNat : ℝ) / q.den) =
    -Real.pi * ((q.num.toNat : ℝ) / q.den) by ring, h]

theorem similarity_target (s t u : ℕ) (hs : 0 < s) (α : ℝ) (hu : α^2=(u : ℝ))
    (htheta : 0 < (t : ℝ)/s-1) (j : ℤ) :
    (similarityArg s t u j).target = PhaseCell.weight s t α j := by
  unfold similarityArg
  rw [encode_target _ (PhaseCellRationalArgs.potentialQ_nonneg s t u hs htheta j),
    PhaseCellRationalArgs.potentialQ_cast s t u hs α hu j]
  rfl

theorem gaussian_target (s t u : ℕ) (α : ℝ) (hu : α^2=(u : ℝ)) (δ : ℤ) :
    (gaussianArg s t u δ).target = PhaseCellRounded.gaussian s t α δ := by
  unfold gaussianArg
  rw [encode_target _ (PhaseCellRationalArgs.gaussianQ_nonneg s t u δ),
    PhaseCellRationalArgs.gaussianQ_cast s t u α hu δ]
  rfl

theorem gaussianArg_neg (s t u : ℕ) (δ : ℤ) : gaussianArg s t u (-δ) = gaussianArg s t u δ := by
  unfold gaussianArg
  rw [PhaseCellRationalArgs.gaussianQ_neg]

theorem kernel_neg (P s t u w : ℕ) (δ : ℤ) : kernel P s t u w (-δ) = kernel P s t u w δ :=
  PhaseCellExecutableCoefficients.kernel_neg P w _ (gaussianArg_neg s t u) δ

@[simp] theorem entry_diag (P s t u w : ℕ) (j : ℤ) : entry P s t u w j j = 1 :=
  PhaseCellExecutableCoefficients.entry_diag P w _ _ j

theorem entry_outside (P s t u w : ℕ) (j k : ℤ) (hband : w < (k-j).natAbs) :
    entry P s t u w j k = 0 :=
  PhaseCellExecutableCoefficients.entry_outside P w _ _ j k hband

/-- Mapping-free accuracy for the concrete executable coefficient constructor. -/
theorem entry_error {P s t u w : ℕ} {α r : ℝ} {j k : ℤ}
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : α^2=(u : ℝ))
    (htheta : 0 < (t : ℝ)/s-1)
    (hphase : PhaseCell.phase s t j = PhaseCell.phase s t k)
    (hjk : j ≠ k) (hband : (k-j).natAbs ≤ w) (hr : 0 < r)
    (hlower : r+4/(2 : ℝ)^P ≤ PhaseCell.weight s t α k) :
    |(entry P s t u w j k : ℝ)-Real.exp (normExp s t α j (k-j))| ≤
      12*PhaseCellRounded.error P/r^2 :=
  PhaseCellExecutableCoefficients.entry_error _ _ hP hst htheta hphase hjk hband hr
    (similarity_target s t u hs α hu htheta j)
    (similarity_target s t u hs α hu htheta k) (gaussian_target s t u α hu (k-j)) hlower

/-- Four grid units fit in half of the selected lower weight. -/
theorem corrected_error_le_half_lower {P p : ℕ} (hP : 8*p+3 ≤ P) :
    4/(2 : ℝ)^P ≤ (1/(2 : ℝ)^(8*p))/2 := by
  calc 4/(2 : ℝ)^P ≤ 4/(2 : ℝ)^(8*p+3) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hP
    _ = (1/(2 : ℝ)^(8*p))/2 := by rw [pow_add]; norm_num; ring

theorem selected_precision (p : ℕ) (hp : 0 < p) :
    13 ≤ 2^15*p ∧ 8*p+3 ≤ 2^15*p := by norm_num; omega

theorem denominator_margin {P s t p : ℕ} {α d : ℝ} (j : ℤ)
    (htheta : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (hP : 8*p+3 ≤ P) :
    (1/(2 : ℝ)^(8*p))/2+4/(2 : ℝ)^P ≤ PhaseCell.weight s t α j := by
  have hweight := PhaseCellRounded.weight_lower j htheta hgap hbudget
  have herr := corrected_error_le_half_lower hP
  linarith

/-- The selected precision proves every actual similarity sample positive. -/
theorem selected_similarity_pos {s t u p : ℕ} {α d : ℝ} (j : ℤ)
    (hp : 0 < p) (hs : 0 < s) (hu : α^2=(u : ℝ))
    (htheta : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) : 0 < similarity (2^15*p) s t u j := by
  apply ExpArg.value_pos _ _ (selected_precision p hp).1
  rw [similarity_target s t u hs α hu htheta j]
  have h := denominator_margin j htheta hgap hbudget (selected_precision p hp).2
  have hpos : (0 : ℝ) < (1/(2 : ℝ)^(8*p))/2 := by positivity
  linarith

/-- Exact similarity to the shared symmetric banded Toeplitz kernel, now with
positivity discharged for the selected executable samples. -/
theorem selected_entry_similarity {s t u p w : ℕ} {α d : ℝ} (j k : ℤ)
    (hp : 0 < p) (hs : 0 < s) (hu : α^2=(u : ℝ))
    (htheta : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) :
    entry (2^15*p) s t u w j k = similarity (2^15*p) s t u j *
      kernel (2^15*p) s t u w (k-j) / similarity (2^15*p) s t u k := by
  exact PhaseCellExecutableCoefficients.entry_similarity _ _ _ _ _ _
    (ne_of_gt (selected_similarity_pos k hp hs hu htheta hgap hbudget))

/-- Concrete selected within-cell accuracy with no argument or denominator oracle. -/
theorem selected_entry_error {s t u p w : ℕ} {α d : ℝ} {j k : ℤ}
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (hu : α^2=(u : ℝ))
    (htheta : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p)
    (hphase : PhaseCell.phase s t j = PhaseCell.phase s t k)
    (hjk : j ≠ k) (hband : (k-j).natAbs ≤ w) :
    |(entry (2^15*p) s t u w j k : ℝ)-Real.exp (normExp s t α j (k-j))| ≤
      12*PhaseCellRounded.error (2^15*p)/((1/(2 : ℝ)^(8*p))/2)^2 :=
  entry_error (selected_precision p hp).1 hs hst hu htheta hphase hjk hband
    (by positivity) (denominator_margin k htheta hgap hbudget (selected_precision p hp).2)

end IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients
