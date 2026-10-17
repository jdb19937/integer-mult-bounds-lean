module

public import IntegerMultBounds.NLogN.PhaseCellScan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Physical intervals of constant nearest-rounding phase

Exact interval and upper-size consequences of the phase scan, corresponding to
"Exact phase-cell structure" in `downstream-phase-cell-inverse.md`, selected
upstream input `bcd4ebde8692383539f8a48734e5fbf3a18a32c2`.
These statements apply also to truncated end cells. They do not assert a lower
size for end cells, an inverse theorem, or any tape cost.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellIntervals

open PhaseCell

/-- Integer translation isolates the relative axis gap without changing ties. -/
theorem phase_eq_nearest_gap (s t : ℕ) (j : ℤ) :
    phase s t j = nearest (((t : ℝ) / s - 1) * j) := by
  have heq : (t : ℝ) * j / s = ((t : ℝ) / s - 1) * j + j := by ring
  unfold phase
  rw [heq, nearest_add_int]
  omega

/-- Increasing physical indices cannot decrease phase when the axis expands. -/
theorem phase_monotone {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) :
    Monotone (phase s t) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hgap : 0 ≤ (t : ℝ) / s - 1 := by
    have : (1 : ℝ) ≤ (t : ℝ) / s := (le_div_iff₀ hsR).mpr (by simpa using hstR)
    linarith
  intro j k hjk
  rw [phase_eq_nearest_gap, phase_eq_nearest_gap]
  unfold nearest
  apply Int.floor_mono
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  linarith [mul_le_mul_of_nonneg_left hjkR hgap]

/-- Equal-phase endpoints force every intervening physical index into that cell. -/
theorem phase_eq_of_between {s t : ℕ} (hs : 0 < s) (hst : s ≤ t)
    {j k l : ℤ} (hjl : j ≤ l) (hlk : l ≤ k) (hphase : phase s t j = phase s t k) :
    phase s t l = phase s t j := by
  have hmono := phase_monotone hs hst
  exact le_antisymm ((hmono hlk).trans_eq hphase.symm) (hmono hjl)

/-- Each phase fiber is order-convex, including its intersection with a physical
input interval; no sorting or cyclic merging is needed. -/
theorem phase_fiber_ordConnected {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) (q : ℤ) :
    Set.OrdConnected {j : ℤ | phase s t j = q} := by
  constructor
  intro j hj k hk l hl
  exact (phase_eq_of_between hs hst hl.1 hl.2 (hj.trans hk.symm)).trans hj

/-- The half-open nearest-rounding convention makes the within-cell gap strict
on both sides, even if an endpoint is exactly a rounding tie. -/
theorem gap_bounds {s t : ℕ} {j k : ℤ} (hphase : phase s t j = phase s t k) :
    -1 < ((t : ℝ) / s - 1) * ((k : ℝ) - j) ∧
      ((t : ℝ) / s - 1) * ((k : ℝ) - j) < 1 := by
  have hj := frac_bounds ((t : ℝ) * j / s)
  have hk := frac_bounds ((t : ℝ) * k / s)
  have hdiff := beta_sub_of_phase_eq s t j k hphase
  change -1 / 2 ≤ beta s t j ∧ beta s t j < 1 / 2 at hj
  change -1 / 2 ≤ beta s t k ∧ beta s t k < 1 / 2 at hk
  constructor <;> linarith

theorem abs_gap_lt_one {s t : ℕ} {j k : ℤ} (hphase : phase s t j = phase s t k) :
    |((t : ℝ) / s - 1) * ((k : ℝ) - j)| < 1 :=
  abs_lt.mpr (gap_bounds hphase)

/-- A lower relative-gap bound controls the distance between any ordered
physical endpoints in the same cell. -/
theorem distance_lt_four_mul {s t d : ℕ} (hd : 0 < d)
    (hgap : 1 / (4 * (d : ℝ)) ≤ (t : ℝ) / s - 1)
    {j k : ℤ} (hjk : j ≤ k) (hphase : phase s t j = phase s t k) :
    k - j < 4 * (d : ℤ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hjkR : (0 : ℝ) ≤ (k : ℝ) - j := by exact_mod_cast sub_nonneg.mpr hjk
  have h := mul_le_mul_of_nonneg_right hgap hjkR
  have hlt := (gap_bounds hphase).2
  have hdiv : ((k : ℝ) - j) / (4 * d) < 1 := by
    have heq : (1 / (4 * (d : ℝ))) * ((k : ℝ) - j) =
        ((k : ℝ) - j) / (4 * d) := by ring
    rw [heq] at h
    exact h.trans_lt hlt
  have hdist : (k : ℝ) - j < 4 * (d : ℝ) := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * d)).mp hdiv
    simpa using this
  exact_mod_cast hdist

/-- A physical constant-phase interval has at most `4d+1` indices under the
selected lower gap bound. This bound also applies to truncated end cells. -/
theorem interval_card_le {s t d : ℕ} (hd : 0 < d)
    (hgap : 1 / (4 * (d : ℝ)) ≤ (t : ℝ) / s - 1)
    (j k : ℤ) (hphase : phase s t j = phase s t k) :
    (Finset.Icc j k).card ≤ 4 * d + 1 := by
  by_cases hjk : j ≤ k
  · have hdist := distance_lt_four_mul hd hgap hjk hphase
    rw [Int.card_Icc]
    omega
  · have hempty : Finset.Icc j k = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hjk)
    simp [hempty]

/-- The concrete scan emits a contiguous phase cell on any physical interval
whose endpoint emissions agree. -/
theorem scan_phase_eq_of_between {s t : ℕ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t < 2 * s) {j k l : ℕ} (hjl : j ≤ l) (hlk : l ≤ k)
    (hphase : (PhaseCellScan.scan s ((t : ℤ) - s) j).phase =
      (PhaseCellScan.scan s ((t : ℤ) - s) k).phase) :
    (PhaseCellScan.scan s ((t : ℤ) - s) l).phase =
      (PhaseCellScan.scan s ((t : ℤ) - s) j).phase := by
  rw [(PhaseCellScan.scan_exact hs hst ht l).1, (PhaseCellScan.scan_exact hs hst ht j).1]
  rw [(PhaseCellScan.scan_exact hs hst ht j).1, (PhaseCellScan.scan_exact hs hst ht k).1] at hphase
  exact phase_eq_of_between hs hst (by exact_mod_cast hjl) (by exact_mod_cast hlk) hphase

end IntegerMultBounds.NLogN.PhaseCellIntervals
