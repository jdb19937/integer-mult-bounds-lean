module

public import IntegerMultBounds.NLogN.ExplicitNumeric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The window sums computed by the Gaussian line machine are the numerical
map `Ã` of the resampling interface: with the weight words holding the
rounded weights `ρ(2^p·w)` of each window and the input words holding the
numerators of a grid vector `u` (cyclically extended by `m` records at both
ends), the two accumulator words of output `k` are `2^(p+1)` times the real
and imaginary parts of `resampANum s t m (resampTermNum p s t α) u k`. -/

@[expose] public section

namespace IntegerMultBounds.Resampling.WindowSum

open IntegerMultBounds.NLogN (rho0 rhoC resampWeight resampTermNum resampANum truncWindow resampCentre)

/-- The window centre `⌊sk/t⌋`. -/
def centre (s t k : ℕ) : ℕ := s * k / t

theorem rho0_int (n : ℤ) : rho0 (n : ℝ) = n := by
  unfold rho0; split_ifs <;> simp

section Rounding

/-- Rounding toward zero of a dyadic rational is the truncated division. -/
theorem rho0_div_pow (n : ℤ) (p : ℕ) : rho0 ((n : ℝ) / 2 ^ p) = n.tdiv (2 ^ p) := by
  have hcast : ((2 : ℝ) ^ p) = ((2 ^ p : ℕ) : ℝ) := by push_cast; rfl
  have hz : ((2 ^ p : ℕ) : ℤ) = 2 ^ p := by push_cast; rfl
  unfold rho0
  split_ifs with h
  · have hn : 0 ≤ n := by
      by_contra hc
      push Not at hc
      have : (n : ℝ) / 2 ^ p < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hc) (by positivity)
      linarith
    rw [hcast, Int.floor_div_natCast, Int.floor_intCast, hz, Int.tdiv_eq_ediv_of_nonneg hn]
  · have hn : n < 0 := by
      by_contra hc
      push Not at hc
      exact h (div_nonneg (by exact_mod_cast hc) (by positivity))
    rw [← neg_neg ((n : ℝ) / 2 ^ p), Int.ceil_neg, hcast, ← neg_div, ← Int.cast_neg, Int.floor_div_natCast,
      Int.floor_intCast, hz, ← Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -n), Int.neg_tdiv, neg_neg]

end Rounding

/-- A window term with an arbitrary real weight function: round the weight,
multiply, round again. -/
noncomputable def termW (p : ℕ) {s t : ℕ} (wf : ZMod t → ℤ → ℝ) (u : ZMod s → ℂ) (k : ZMod t) (j : ℤ) : ℂ :=
  rhoC p (rhoC p (wf k j : ℂ) * u j)

section Terms

variable {s t : ℕ} [NeZero s] [NeZero t] (p : ℕ) (wf : ZMod t → ℤ → ℝ) (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
  (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)

theorem rhoC_real (x : ℝ) : rhoC p (x : ℂ) = ((rho0 (2 ^ p * x) : ℝ) / 2 ^ p : ℝ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; simp [rhoC]
  · rw [Complex.ofReal_im]; simp [rhoC, rho0]

omit [NeZero s] [NeZero t] in
include hu in
/-- One fixed-point term: its parts are truncated products over `2^p`. -/
theorem term_parts (k : ZMod t) (j : ℤ) :
    termW p wf u k j =
      ⟨((rho0 (2 ^ p * wf k j) * ar j).tdiv (2 ^ p) : ℝ) / 2 ^ p,
       ((rho0 (2 ^ p * wf k j) * ai j).tdiv (2 ^ p) : ℝ) / 2 ^ p⟩ := by
  unfold termW
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

/-- A sum over an integer interval as a sum over a range. -/
theorem sum_Icc_eq_range (a : ℤ) (n : ℕ) (f : ℤ → ℂ) :
    ∑ j ∈ Finset.Icc a (a + n), f j = ∑ i ∈ Finset.range (n + 1), f (a + i) := by
  symm
  refine Finset.sum_nbij (fun i : ℕ => a + i) (fun i hi => ?_) (fun i _ j _ h => ?_) (fun b hb => ?_)
    (fun i _ => rfl)
  · simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
  · simpa using h
  · simp only [Finset.coe_Icc, Set.mem_Icc] at hb
    refine ⟨(b - a).toNat, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]; omega
    · simp only; omega

omit [NeZero s] [NeZero t] in
theorem floor_centre (_hst : s ≤ t) (k : ℕ) (hk : k < t) :
    ⌊resampCentre s t (k : ZMod t)⌋ = (centre s t k : ℤ) := by
  unfold resampCentre centre
  rw [ZMod.val_natCast_of_lt hk, show ((s : ℝ) * k / t) = ((s * k : ℕ) : ℝ) / ((t : ℕ) : ℝ) by push_cast; ring,
    Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]

end Terms

end IntegerMultBounds.Resampling.WindowSum
