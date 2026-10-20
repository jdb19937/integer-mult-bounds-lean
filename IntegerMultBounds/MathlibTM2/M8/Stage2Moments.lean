module

public import IntegerMultBounds.MathlibTM2.M8.Global.Branching97
public import IntegerMultBounds.MathlibTM2.M8.Stage2Histogram
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The moment gaps of the stage-2 supplier

The stopped recurrence (`StoppedRecurrence.stopped_closed`) needs two moment gaps of the node's
rank histogram `n_r` on `W = 108516254` contract roles and `m = 529` coordinates: the linear moment
`Σ_r (n_r/W)(r/m) = q₁ < 1` and the `τ*`-moment `Σ_r (n_r/W)(r/m)^τ* ≤ q_τ < 1`, at
`τ* = 1 - 969/10⁷` and `q_τ = 1 - 2/10⁸`. The whole-projector saving is `a* ≈ 9.69991·10⁻⁵`, so the
chosen `1 - τ*` lies within `10⁻⁸` of it.

The certificate is rational. For each rank, `L_r` bounds `log (m/r)` by an exponential series
(`log_lt`). Then `(r/m)^τ* = (r/m) exp (a log (m/r)) ≤ (r/m)(1 + y + y²/2 + 2y³/9)` at `y = a L_r`
(`rpow_le`), and the rational sum of these bounds is checked by `decide +kernel`. The rank mass of
the histogram is the stage-1 rank sum `Branching97.rankBound`.

The histogram itself comes from `scripts/pr97/stage2hist.py`; linking it to the node's moves is
the job of the reversed recursive family.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Moments

open Global.Branching97 (width roleCount)

/-- A histogram row `(r, n_r, L_r, k_r)`. -/
abbrev Row := ℕ × ℕ × ℕ × ℕ

/-- `Σ_{i<k} x^i / i!`. -/
def expSeries (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => expSeries x k + x ^ k / k.factorial

/-- The cubic upper bound of `exp` on `[0, 1]`. -/
def cubic (y : ℚ) : ℚ := 1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3

/-- The saving `a = 1 - τ*`. -/
def saving : ℚ := 969 / 10 ^ 7

/-- The `τ*`-moment gap. -/
def qτ : ℚ := 1 - 2 / 10 ^ 8

/-- The linear moment. -/
def q₁ : ℚ := 1409269 / 1409302

/-- The rational bound of `log (m/r)`. -/
def logBound (row : Row) : ℚ := (row.2.2.1 : ℚ) / 10 ^ 9

/-- A row is checked when its rank lies in `1..m`, its series exceeds `m/r` and `a L_r ≤ 1`. -/
def rowOk (row : Row) : Bool :=
  0 < row.1 && row.1 ≤ width && decide ((width : ℚ) / row.1 < expSeries (logBound row) row.2.2.2) &&
    decide (saving * logBound row ≤ 1)

/-- `Σ (n_r/W)(r/m)`. -/
def linMoment : List Row → ℚ
  | [] => 0
  | row :: rows => (row.2.1 : ℚ) / roleCount * ((row.1 : ℚ) / width) + linMoment rows

/-- The rational bound of the `τ*`-moment. -/
def tauBound : List Row → ℚ
  | [] => 0
  | row :: rows =>
    (row.2.1 : ℚ) / roleCount * ((row.1 : ℚ) / width) * cubic (saving * logBound row) + tauBound rows

/-- `Σ (n_r/W)(r/m)^τ`. -/
noncomputable def moment (τ : ℝ) : List Row → ℝ
  | [] => 0
  | row :: rows => (row.2.1 : ℝ) / roleCount * ((row.1 : ℝ) / width) ^ τ + moment τ rows

theorem expSeries_cast (x : ℚ) : ∀ k,
    (expSeries x k : ℝ) = ∑ i ∈ Finset.range k, (x : ℝ) ^ i / i.factorial
  | 0 => by simp [expSeries]
  | k + 1 => by rw [expSeries, Finset.sum_range_succ, ← expSeries_cast x k]; push_cast; rfl

theorem logBound_nonneg (row : Row) : (0 : ℝ) ≤ (logBound row : ℝ) := by
  rw [logBound]; push_cast; positivity

theorem log_lt {row : Row} (h : rowOk row = true) :
    Real.log ((width : ℝ) / row.1) < (logBound row : ℝ) := by
  simp only [rowOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, -⟩, hs⟩, -⟩ := h
  have hr' : (0 : ℝ) < row.1 := by exact_mod_cast hr
  apply (Real.log_lt_iff_lt_exp (div_pos (by norm_num [width]) hr')).mpr
  have hs' : (((width : ℚ) / row.1 : ℚ) : ℝ) < (expSeries (logBound row) row.2.2.2 : ℝ) := by
    exact_mod_cast hs
  push_cast at hs'
  rw [expSeries_cast] at hs'
  exact hs'.trans_le (Real.sum_le_exp_of_nonneg (logBound_nonneg row) _)

theorem rpow_le {row : Row} (h : rowOk row = true) :
    ((row.1 : ℝ) / width) ^ (1 - (saving : ℝ)) ≤
      (row.1 : ℝ) / width * (cubic (saving * logBound row) : ℝ) := by
  have hlog := log_lt h
  simp only [rowOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, hm⟩, -⟩, h1⟩ := h
  have hr' : (0 : ℝ) < row.1 := by exact_mod_cast hr
  have hm' : (row.1 : ℝ) ≤ width := by exact_mod_cast hm
  have hw : (0 : ℝ) < width := by norm_num [width]
  have hp : 0 < (row.1 : ℝ) / width := div_pos hr' hw
  have ha : (0 : ℝ) < saving := by norm_num [saving]
  set x := (saving : ℝ) * Real.log ((width : ℝ) / row.1) with hx
  have hlog0 : 0 ≤ Real.log ((width : ℝ) / row.1) :=
    Real.log_nonneg ((one_le_div hr').mpr hm')
  have hx0 : 0 ≤ x := mul_nonneg ha.le hlog0
  have hxL : x ≤ (saving : ℝ) * (logBound row : ℝ) := mul_le_mul_of_nonneg_left hlog.le ha.le
  have h1' : (saving : ℝ) * (logBound row : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpow : ((row.1 : ℝ) / width) ^ (1 - (saving : ℝ)) = (row.1 : ℝ) / width * Real.exp x := by
    rw [Real.rpow_def_of_pos hp, hx, Real.log_div hw.ne' hr'.ne', Real.log_div hr'.ne' hw.ne',
      ← Real.exp_log hp, Real.log_div hr'.ne' hw.ne', ← Real.exp_add]
    ring_nf
  have hexp : Real.exp x ≤ (cubic (saving * logBound row) : ℝ) := by
    have hy0 : (0 : ℝ) ≤ (saving : ℝ) * (logBound row : ℝ) := hx0.trans hxL
    calc Real.exp x ≤ 1 + x + x ^ 2 / 2 + 2 / 9 * x ^ 3 :=
          Global.Branching97.exp_le_cubic hx0 (hxL.trans h1')
      _ ≤ _ := by rw [cubic]; push_cast; gcongr
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hexp hp.le

/-- The `τ*`-moment of checked rows is at most their rational bound. -/
theorem moment_le : ∀ {rows : List Row}, rows.all rowOk = true →
    moment (1 - saving) rows ≤ tauBound rows
  | [], _ => by simp [moment, tauBound]
  | row :: rows, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [moment, tauBound]
    push_cast
    have hw : (0 : ℝ) ≤ (row.2.1 : ℝ) / roleCount := by positivity
    have := mul_le_mul_of_nonneg_left (rpow_le h.1) hw
    have := moment_le h.2
    nlinarith

/-- The linear moment in the reals. -/
theorem moment_one : ∀ rows : List Row, moment 1 rows = linMoment rows
  | [] => by simp [moment, linMoment]
  | row :: rows => by rw [moment, linMoment, moment_one rows, Real.rpow_one]; push_cast; ring

theorem histogram_ok : histogram.all rowOk = true := by decide +kernel

theorem tauBound_lt : tauBound histogram < qτ := by decide +kernel

theorem linMoment_eq : linMoment histogram = q₁ := by decide +kernel

/-- The histogram carries the stage-1 rank sum. -/
theorem rank_mass :
    (histogram.map fun row => row.1 * row.2.1).sum = Global.Branching97.rankBound := by
  decide +kernel

/-- **The `τ*`-moment gap** of the stage-2 histogram. -/
theorem tau_moment : moment (1 - saving) histogram < qτ := by
  have h := moment_le histogram_ok
  have h' : (tauBound histogram : ℝ) < qτ := by exact_mod_cast tauBound_lt
  linarith

/-- **The linear moment gap** of the stage-2 histogram. -/
theorem linear_moment : moment 1 histogram = q₁ := by
  rw [moment_one, linMoment_eq]

theorem q₁_lt_one : q₁ < 1 := by norm_num [q₁]

theorem qτ_lt_one : qτ < 1 := by norm_num [qτ]

theorem qτ_nonneg : 0 ≤ qτ := by norm_num [qτ]

end IntegerMultBounds.MathlibTM2.M8.Stage2Moments
