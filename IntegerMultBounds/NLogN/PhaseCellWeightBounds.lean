module

public import IntegerMultBounds.NLogN.PhaseCellRoundedError

/-! Selected coarse lower weights and precision for the actual rounded
within-cell constructor. This discharges its denominator premise from the
relative axis gap and normalization budget, rather than assuming positive
rounded samples. Periodic aliases, cross-cell terms and execution costs remain
separate. The precision `2^15*p` is the selected phase-cell report's work grid. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRounded

noncomputable section

theorem weight_lower {s t p : ℕ} {α d : ℝ} (j : ℤ)
    (htheta : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1))
    (hbudget : α ^ 2 * d ≤ p) :
    1 / (2 : ℝ) ^ (8*p) ≤ PhaseCell.weight s t α j := by
  have hF := (PhaseCell.potential_le s t α d j htheta hgap).trans hbudget
  have hpi : Real.exp Real.pi ≤ (2 : ℝ)^8 := by
    calc Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr Real.pi_lt_four.le
      _ = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
      _ ≤ (2 : ℝ)^8 := by norm_num
  have hupper : Real.exp (Real.pi * PhaseCell.potential s t α j) ≤ (2 : ℝ)^(8*p) := by
    calc Real.exp (Real.pi * PhaseCell.potential s t α j) ≤ Real.exp (Real.pi * p) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hF Real.pi_pos.le)
      _ = Real.exp Real.pi ^ p := by rw [mul_comm, Real.exp_nat_mul]
      _ ≤ ((2 : ℝ)^8)^p := pow_le_pow_left₀ (Real.exp_pos _).le hpi _
      _ = (2 : ℝ)^(8*p) := by rw [pow_mul]
  have h := one_div_le_one_div_of_le (Real.exp_pos _) hupper
  simpa only [PhaseCell.weight, neg_mul, Real.exp_neg, one_div] using h

theorem error_le_half_weight_lower {P p : ℕ} (hP : 8*p+1 ≤ P) :
    error P ≤ (1 / (2 : ℝ)^(8*p)) / 2 := by
  calc error P ≤ 1 / (2 : ℝ)^(8*p+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hP
    _ = (1 / (2 : ℝ)^(8*p)) / 2 := by rw [pow_succ]; ring

/-- The selected parameter budget supplies the positive denominator and one
unit of grid slack needed by the actual coefficient-error theorem. -/
theorem denominator_lower {P s t p : ℕ} {α d : ℝ} (j : ℤ)
    (htheta : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1))
    (hbudget : α ^ 2 * d ≤ p) (hP : 8*p+1 ≤ P) :
    (1 / (2 : ℝ)^(8*p)) / 2 + error P ≤ PhaseCell.weight s t α j := by
  have hweight := weight_lower j htheta hgap hbudget
  have herror := error_le_half_weight_lower hP
  linarith

theorem selected_precision (p : ℕ) (hp : 0 < p) : 8*p+1 ≤ 2^15*p := by
  norm_num
  omega

/-- No positivity oracle is needed for any selected rounded similarity weight. -/
theorem selected_similarity_pos {s t p : ℕ} {α d : ℝ} (j : ℤ)
    (hp : 0 < p) (htheta : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1))
    (hbudget : α ^ 2 * d ≤ p) :
    0 < similarity (2^15*p) s t α j := by
  have h := denominator_lower j htheta hgap hbudget (selected_precision p hp)
  have hpos : (0 : ℝ) < (1 / (2 : ℝ)^(8*p)) / 2 := by positivity
  have hlower := down_lower (2^15*p) h
  have : (0 : ℝ) < (similarity (2^15*p) s t α j : ℝ) :=
    hpos.trans_le hlower
  exact_mod_cast this

/-- Specialize the actual within-cell coefficient estimate using only the
selected axis-gap and normalization budgets, with no denominator premise. -/
theorem selected_entry_error {s t p w : ℕ} {α d : ℝ} {j k : ℤ}
    (hp : 0 < p) (hst : s < t) (htheta : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1))
    (hbudget : α ^ 2 * d ≤ p)
    (hphase : PhaseCell.phase s t j = PhaseCell.phase s t k)
    (hjk : j ≠ k) (hband : (k-j).natAbs ≤ w) :
    |(entry (2^15*p) s t w α j k : ℝ) - Real.exp (normExp s t α j (k-j))| ≤
      3 * error (2^15*p) / ((1 / (2 : ℝ)^(8*p)) / 2) ^ 2 := by
  exact entry_error hst htheta hphase hjk hband (by positivity)
    (denominator_lower k htheta hgap hbudget (selected_precision p hp))

end
end IntegerMultBounds.NLogN.PhaseCellRounded
