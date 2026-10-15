module

public import IntegerMultBounds.NLogN.ResamplingInverse

/-! Exact phase-cell structure of the existing normalized resampling matrix.
The phase-cell inverse construction uses this identity to replace each local
matrix by a diagonally similar Toeplitz matrix. This file proves the identity
for the existing `beta` and `normExp`; it does not assert inverse, rounding,
locality, or machine-cost bounds.

Source: the selected construction's report
`references/semantic-bulk/rad20/reports/downstream-phase-cell-inverse.md`,
section "Exact phase-cell structure" (upstream input
`bcd4ebde8692383539f8a48734e5fbf3a18a32c2`). -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCell

noncomputable section
open Real

/-- The integer nearest-rounding displacement; a phase cell has constant phase. -/
def phase (s t : ℕ) (j : ℤ) : ℤ := nearest ((t : ℝ) * j / s) - j

/-- The Gaussian similarity potential, using the same offsets as `normExp`. -/
def potential (s t : ℕ) (α : ℝ) (j : ℤ) : ℝ :=
  α ^ 2 * (1 / 4 - beta s t j ^ 2) / ((t : ℝ) / s - 1)

def weight (s t : ℕ) (α : ℝ) (j : ℤ) : ℝ :=
  Real.exp (-π * potential s t α j)

/-- On one phase cell, the offset changes linearly with the physical index. -/
theorem beta_sub_of_phase_eq (s t : ℕ) (j k : ℤ)
    (hphase : phase s t j = phase s t k) :
    beta s t k - beta s t j = ((t : ℝ) / s - 1) * (k - j) := by
  have hq : (nearest ((t : ℝ) * k / s) : ℝ) -
      nearest ((t : ℝ) * j / s) = (k : ℝ) - j := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hphase
    simp only [phase, Int.cast_sub] at h
    linarith
  unfold beta frac
  linear_combination -hq

/-- The existing lattice exponent splits into a distance term and a potential
difference, without changing the matrix or its rounding convention. -/
theorem normExp_eq (s t : ℕ) (hst : s < t) (α : ℝ) (j k : ℤ)
    (hphase : phase s t j = phase s t k) :
    normExp s t α j (k-j) =
      -π * (α ^ 2 * ((t : ℝ) / s) * ((k : ℝ)-j) ^ 2) -
        π * potential s t α j + π * potential s t α k := by
  have htheta : (t : ℝ) / s - 1 ≠ 0 := by
    by_cases hs : s = 0
    · simp [hs]
    · have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
      have hst' : (s : ℝ) < t := by exact_mod_cast hst
      have : 1 < (t : ℝ) / s := (lt_div_iff₀ hspos).mpr (by simpa using hst')
      linarith
  have hb := beta_sub_of_phase_eq s t j k hphase
  have hb' : beta s t k = beta s t j + ((t : ℝ) / s - 1) * ((k : ℝ)-j) := by
    linarith
  have hk : j+(k-j)=k := by omega
  have hdiv : (t : ℝ) * ((k-j : ℤ) : ℝ) / s = ((t : ℝ) / s) * ((k : ℝ)-j) := by
    push_cast
    ring
  unfold normExp potential
  rw [hk, hdiv, hb']
  field_simp
  ring

theorem potential_nonneg (s t : ℕ) (α : ℝ) (j : ℤ)
    (htheta : 0 < (t : ℝ) / s - 1) : 0 ≤ potential s t α j :=
  div_nonneg (mul_nonneg (sq_nonneg α) (sub_nonneg.mpr (sq_beta_le s t j))) htheta.le

/-- The actual offset bound keeps the similarity potential below `α² d`
under the selected lower bound on the relative axis gap. -/
theorem potential_le (s t : ℕ) (α d : ℝ) (j : ℤ)
    (htheta : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) :
    potential s t α j ≤ α ^ 2 * d := by
  unfold potential
  apply (div_le_iff₀ htheta).mpr
  have h := mul_le_mul_of_nonneg_left hgap (sq_nonneg α)
  nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg (beta s t j))]

theorem weight_pos (s t : ℕ) (α : ℝ) (j : ℤ) : 0 < weight s t α j :=
  Real.exp_pos _

theorem weight_le_one (s t : ℕ) (α : ℝ) (j : ℤ)
    (htheta : 0 < (t : ℝ) / s - 1) : weight s t α j ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le)
    (potential_nonneg s t α j htheta)

/-- Each actual normalized lattice coefficient inside a phase cell is a
diagonal conjugate of a Gaussian coefficient depending only on distance. -/
theorem coefficient_eq (s t : ℕ) (hst : s < t) (α : ℝ) (j k : ℤ)
    (hphase : phase s t j = phase s t k) :
    Real.exp (normExp s t α j (k-j)) =
      weight s t α j * Real.exp (-π * (α ^ 2 * ((t : ℝ) / s) *
        ((k : ℝ)-j) ^ 2)) / weight s t α k := by
  rw [normExp_eq s t hst α j k hphase]
  unfold weight
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

end
end IntegerMultBounds.NLogN.PhaseCell
