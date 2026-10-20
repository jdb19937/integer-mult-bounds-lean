module

public import IntegerMultBounds.Resampling.WindowSum
public import IntegerMultBounds.NLogN.ExplicitNumeric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The off-diagonal map `Ẽ` of the Neumann iteration on the Gaussian line
machine: run with stride one (`s` outputs over `s` inputs, so the window of
output `ℓ` is centred at `ℓ`), with the weight words holding the rounded
weights `ρ(2^p·exp(…))` of the off-diagonal terms and a zero word at the
centre of every window, the two accumulator words of output `ℓ` are `2^p`
times the real and imaginary parts of `offDiagNum m (offDiagTermNum p s t α) u ℓ`. -/

@[expose] public section

namespace IntegerMultBounds.Resampling.OffDiagSum

open IntegerMultBounds.NLogN (rho0 rhoC normExp offDiagTermNum offDiagNum offDiagWindow)
open WindowSum (centre rho0_div_pow rhoC_real sum_Icc_eq_range)

/-- With stride one the window centre is the output index. -/
theorem centre_self (s k : ℕ) (hs : 0 < s) : centre s s k = k := by
  unfold centre; exact Nat.mul_div_cancel_left k hs

section Terms

variable {s : ℕ} (p : ℕ) (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
  (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)

include hu in
/-- A rounded product of a rounded real weight with an input entry: its
parts are truncated products over `2^p`. -/
theorem round_term_parts (x : ℝ) (j : ℤ) :
    rhoC p (rhoC p (x : ℂ) * u j) =
      ⟨((rho0 (2 ^ p * x) * ar j).tdiv (2 ^ p) : ℝ) / 2 ^ p,
       ((rho0 (2 ^ p * x) * ai j).tdiv (2 ^ p) : ℝ) / 2 ^ p⟩ := by
  rw [rhoC_real, hu]
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  apply Complex.ext
  · simp only [rhoC, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← rho0_div_pow]
    congr 2
    push_cast
    field_simp
  · simp only [rhoC, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← rho0_div_pow]
    congr 2
    push_cast
    field_simp

/-- The off-diagonal sum over its window, with the excluded centre term
written as zero over the full interval, as a sum over a range. -/
theorem offDiag_sum_range (f : ℤ → ℂ) (m : ℕ) :
    ∑ h ∈ offDiagWindow m, f h =
      ∑ j ∈ Finset.range (2 * m + 1), (if (-(m : ℤ) + j) = 0 then 0 else f (-(m : ℤ) + j)) := by
  unfold offDiagWindow
  rw [Finset.sum_congr rfl (g := fun h => if h = 0 then 0 else f h)
      (fun h hh => by simp [Finset.ne_of_mem_erase hh]),
    Finset.sum_erase _ (by simp)]
  have h := sum_Icc_eq_range (-(m : ℤ)) (2 * m) (fun h => if h = 0 then 0 else f h)
  rw [show -(m : ℤ) + ((2 * m : ℕ) : ℤ) = m by push_cast; ring] at h
  exact h

end Terms

/-- An off-diagonal term with an arbitrary real weight function. -/
noncomputable def offTermW (p : ℕ) {s : ℕ} (ef : ZMod s → ℤ → ℝ) (u : ZMod s → ℂ) (ℓ : ZMod s) (h : ℤ) : ℂ :=
  rhoC p (rhoC p (ef ℓ h : ℂ) * u (ℓ + h))

end IntegerMultBounds.Resampling.OffDiagSum
