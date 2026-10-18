module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Factorial.Basic

/-! Numerical budget of the size-25 mixer network. Its side bank has `601404`
roles per invocation (`224802` input slots, `224802` output slots and `151800`
direct pairs), so the network has `9569028100000` wires. The projection-rank
total is at most `149516060359500000`, and the branching ratio is below
`15625 ^ (1 - 25 / 10 ^ 10)`. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Budget
noncomputable section

/-- The complex branching exponent supported by the mixer network. -/
def sigma : ℝ := 1 - 25 / 10 ^ 10

theorem sigma_lt_one : sigma < 1 := by norm_num [sigma]

theorem sigma_pos : 0 < sigma := by norm_num [sigma]

/-- Wire count and rank bound of the size-25 mixer network. -/
theorem counts :
    2 * (2300 : ℕ) ^ 3 + 3 * 2300 ^ 2 * (601404 + 26) = 9569028100000 ∧
    6 * (2300 : ℕ) ^ 2 * 26 * 25 = 20631000000 ∧
    9569028100000 * (15625 : ℕ) + 20631000000 - 2 * 2300 ^ 3 = 149516060359500000 ∧
    (2 : ℕ) ≤ 149516060359500000 ∧ 149516060359500000 < (15625 : ℕ) ^ 5 := by
  norm_num

theorem deficit :
    (1 : ℝ) - 149516060359500000 / (9569028100000 * 15625) = 14 / 565278125 ∧
    (25 / 10 ^ 10 : ℝ) * (966 / 100) < 14 / 565278125 := by
  norm_num

theorem log_bound : Real.log 15625 < 966 / 100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 966 / 100 by norm_num) 20
  have hsum : (15625 : ℝ) <
      ∑ i ∈ Finset.range 20, (966 / 100 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hsum.trans_le h

/-- The strict branching-ratio inequality of the mixer network. -/
theorem branching_bound :
    (149516060359500000 / 9569028100000 : ℝ) < (15625 : ℝ) ^ sigma := by
  have hlog := log_bound
  have hdef := deficit
  have hpos : (0 : ℝ) < 25 / 10 ^ 10 := by norm_num
  have hlin := mul_lt_mul_of_pos_left hlog hpos
  have hexp := Real.add_one_le_exp (-(25 / 10 ^ 10 : ℝ) * Real.log 15625)
  have hr : (1 : ℝ) - 14 / 565278125 <
      Real.exp (-(25 / 10 ^ 10 : ℝ) * Real.log 15625) := by
    linarith [hdef.2]
  have heq : (15625 : ℝ) ^ sigma =
      15625 * Real.exp (-(25 / 10 ^ 10 : ℝ) * Real.log 15625) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have : Real.log 15625 * sigma =
        Real.log 15625 + -(25 / 10 ^ 10 : ℝ) * Real.log 15625 := by
      unfold sigma
      ring
    rw [this, Real.exp_add, Real.exp_log (by norm_num)]
  rw [heq]
  nlinarith

end
end IntegerMultBounds.Networks.Mixer.Budget
