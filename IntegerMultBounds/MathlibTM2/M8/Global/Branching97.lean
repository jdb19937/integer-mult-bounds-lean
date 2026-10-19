module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The PR97 width exponent

`tau = 1 - 3734039/10¹²` meets the branching condition of the PR97 node: every rank sum
`s ≤ 57403754177` on `108516254` contract roles has `s / 108516254 < 529 ^ tau` (`branching`).
The exact threshold is `1 - tau < 3.73403992·10⁻⁶`; the chosen saving lies within `10⁻¹²` of it.

The certificate is rational and small. A 26-term exponential series gives
`log 529 < L = 6.27098844` (`log_bound`). With `x = (1 - tau) log 529 ≤ (1 - tau) L`,
`529 ^ (1 - tau) = exp x ≤ 1 + x + x²/2 + 2x³/9` (`Real.exp_bound'`), and
`57403754177 (1 + x + x²/2 + 2x³/9) < 529 · 108516254` at `x = (1 - tau) L`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global.Branching97

noncomputable section

/-- The rank sum the word side certifies for the PR97 node. -/
def rankBound : ℕ := 57403754177

/-- The contract roles of the PR97 node. -/
def roleCount : ℕ := 108516254

/-- Address coordinates per field. -/
def width : ℕ := 529

/-- The saving `1 - tau`. -/
def saving : ℝ := 3734039 / 10 ^ 12

/-- The width exponent of the PR97 node. -/
def tau : ℝ := 1 - saving

theorem tau_pos : 0 < tau := by norm_num [tau, saving]

theorem tau_lt_one : tau < 1 := by norm_num [tau, saving]

/-- The rational upper bound of `log 529`. -/
def logBound : ℝ := 627098844 / 10 ^ 8

theorem log_bound : Real.log 529 < logBound := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have hseries := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ logBound by norm_num [logBound]) 26
  have hsum : (529 : ℝ) < ∑ i ∈ Finset.range 26, logBound ^ i / (Nat.factorial i : ℝ) := by
    norm_num [logBound, Finset.sum_range_succ, Nat.factorial]
  exact hsum.trans_le hseries

/-- The cubic upper bound of `exp x` on `[0, 1]`. -/
theorem exp_le_cubic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + 2 / 9 * x ^ 3 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  have he : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) + x ^ 3 * (3 + 1) / ((Nat.factorial 3 : ℝ) * 3) =
      1 + x + x ^ 2 / 2 + 2 / 9 * x ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
    ring
  exact he ▸ h

/-- The whole certificate in rationals. -/
theorem rational_certificate :
    (rankBound : ℝ) * (1 + saving * logBound + (saving * logBound) ^ 2 / 2 +
      2 / 9 * (saving * logBound) ^ 3) < width * roleCount := by
  norm_num [rankBound, saving, logBound, width, roleCount]

/-- The branching condition of the PR97 node for every rank sum up to `rankBound`. -/
theorem branching (s : ℕ) (hs : s ≤ rankBound) : (s : ℝ) / roleCount < (width : ℝ) ^ tau := by
  set x := saving * Real.log 529 with hx
  have hlog : 0 < Real.log 529 := Real.log_pos (by norm_num)
  have hsav : 0 < saving := by norm_num [saving]
  have hx0 : 0 ≤ x := by positivity
  have hxL : x ≤ saving * logBound := mul_le_mul_of_nonneg_left log_bound.le hsav.le
  have hL0 : 0 ≤ saving * logBound := hx0.trans hxL
  have hx1 : x ≤ 1 := hxL.trans (by norm_num [saving, logBound])
  have hcubic : 1 + x + x ^ 2 / 2 + 2 / 9 * x ^ 3 ≤
      1 + saving * logBound + (saving * logBound) ^ 2 / 2 + 2 / 9 * (saving * logBound) ^ 3 := by
    gcongr
  have hexp : Real.exp x ≤
      1 + saving * logBound + (saving * logBound) ^ 2 / 2 + 2 / 9 * (saving * logBound) ^ 3 :=
    (exp_le_cubic hx0 hx1).trans hcubic
  have hpow : (width : ℝ) ^ tau = 529 / Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num [width])]
    have he : Real.log (width : ℝ) * tau = Real.log 529 - x := by
      rw [hx, tau]
      norm_num [width]
      ring
    rw [he, Real.exp_sub, Real.exp_log (by norm_num)]
  have hs' : (s : ℝ) ≤ rankBound := by exact_mod_cast hs
  have hW : (0 : ℝ) < roleCount := by norm_num [roleCount]
  have hE : 0 < Real.exp x := Real.exp_pos x
  have hcert := rational_certificate
  rw [hpow, div_lt_div_iff₀ hW hE]
  have hr : (0 : ℝ) ≤ rankBound := by positivity
  have h1 : (s : ℝ) * Real.exp x ≤ (rankBound : ℝ) *
      (1 + saving * logBound + (saving * logBound) ^ 2 / 2 + 2 / 9 * (saving * logBound) ^ 3) :=
    mul_le_mul hs' hexp hE.le hr
  have h2 : (529 : ℝ) * roleCount = width * roleCount := by norm_num [width]
  linarith

end
end IntegerMultBounds.MathlibTM2.M8.Global.Branching97
