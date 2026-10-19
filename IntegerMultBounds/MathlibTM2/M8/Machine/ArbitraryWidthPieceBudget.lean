module

public import IntegerMultBounds.Machine.ArbitraryWidthPieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.RootExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.BudgetBound

/-! The actual proved root budgets summed over the literal arbitrary-width
partition. This bounds the power-piece calls; physical view construction and
padding must still be charged by the general-width wrapper. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceBudget
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Machine.ArbitraryWidthPieces (depths)
open RootExecution (rootBudget)

def constant : ℝ :=
  RootExecution.constant *
    (((Machine.width : ℝ)-1)*(Machine.width : ℝ)^BudgetBound.tau / ((Machine.width : ℝ)^BudgetBound.tau-1))

theorem constant_positive : 0 < constant := by
  have hx : 1 < (Machine.width : ℝ)^BudgetBound.tau :=
    Real.one_lt_rpow one_lt_width_real BudgetBound.exponent_range.1
  unfold constant
  exact mul_pos RootExecution.constant_positive
    (div_pos (mul_pos (by linarith [two_le_width_real]) (by linarith)) (by linarith))

/-- The cost of every actual power-width call in the literal partition sums
to the same certified width exponent. No wrapper execution premise is used. -/
theorem sum_bound (V e k : ℕ) (hk : Machine.width^k ≤ e) :
    ((depths Machine.width e k).map (fun j => (rootBudget j V : ℝ))).sum ≤
      constant*(V : ℝ)*(e : ℝ)^BudgetBound.tau := by
  let C := RootExecution.constant
  have hCV : 0 ≤ C*(V : ℝ) :=
    mul_nonneg RootExecution.constant_positive.le (Nat.cast_nonneg _)
  calc
    ((depths Machine.width e k).map (fun j => (rootBudget j V : ℝ))).sum =
        ∑ j ∈ Finset.range (k+1), (e/Machine.width^j%Machine.width : ℕ)*(rootBudget j V : ℝ) :=
      ArbitraryWidthPieces.real_piece_sum _ _ _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), (e/Machine.width^j%Machine.width : ℕ)*
        (C*(V : ℝ)*((Machine.width^j : ℕ) : ℝ)^BudgetBound.tau) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (RootExecution.rootBudget_bound j V) (Nat.cast_nonneg _)
    _ = C*(V : ℝ)*(∑ j ∈ Finset.range (k+1),
        (e/Machine.width^j%Machine.width : ℕ)*((Machine.width^j : ℕ) : ℝ)^BudgetBound.tau) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ C*(V : ℝ)*
        ((((Machine.width : ℝ)-1)*(Machine.width : ℝ)^BudgetBound.tau /
          ((Machine.width : ℝ)^BudgetBound.tau-1))*(e : ℝ)^BudgetBound.tau) :=
      mul_le_mul_of_nonneg_left
        (Swap.Recurrence.pieces_le two_le_width BudgetBound.exponent_range.1
          (fun j => e/Machine.width^j%Machine.width) (fun j => Nat.mod_lt _ width_pos) hk) hCV
    _ = constant*(V : ℝ)*(e : ℝ)^BudgetBound.tau := by
      unfold constant C
      ring

/-- Canonical integer-logarithm partition, with no chosen depth parameter. -/
theorem canonical_bound (V e : ℕ) (he : e ≠ 0) :
    ((depths Machine.width e (Nat.log Machine.width e)).map (fun j => (rootBudget j V : ℝ))).sum ≤
      constant*(V : ℝ)*(e : ℝ)^BudgetBound.tau :=
  sum_bound V e _ (Nat.pow_log_le_self _ he)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceBudget
