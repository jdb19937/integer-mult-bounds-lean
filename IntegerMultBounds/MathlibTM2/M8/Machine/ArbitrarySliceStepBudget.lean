module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStep
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceBudget
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.BudgetBound
public import IntegerMultBounds.MathlibTM2.M8.Machine.RootExecution

/-! The fully paid slice step, including preparation, header restoration and
offset advancement, retains the certified sublinear width exponent. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepBudget
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks

def budget (depth V : ℕ) := RootExecution.rootBudget depth V+1087*V

theorem cost_le (depth V b : ℕ) (ts bs : List Bool) (hV : 0 < V) (hb : b ≤ V)
    (ht : ts.length ≤ 2*V) (hs : bs.length ≤ 2*V) :
    ArbitrarySliceStep.cost depth V b ts bs ≤ budget depth V := by
  unfold ArbitrarySliceStep.cost budget
  omega

def coefficient : ℝ := RootExecution.constant+1087

theorem coefficient_positive : 0 < coefficient := by
  have h := RootExecution.constant_positive
  unfold coefficient
  linarith

theorem budget_bound (depth V : ℕ) :
    (budget depth V : ℝ) ≤ coefficient*V*((Machine.width^depth : ℕ) : ℝ)^BudgetBound.tau := by
  have hr := RootExecution.rootBudget_bound depth V
  have hw : (1 : ℝ) ≤ ((Machine.width^depth : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (Machine.width : ℕ)^depth from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ width_pos.ne'))
  have hp := Real.one_le_rpow hw BudgetBound.exponent_range.1.le
  have hv : (0 : ℝ) ≤ V := Nat.cast_nonneg _
  simp only [budget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,coefficient]
  nlinarith

def constant : ℝ := coefficient*
  (((Machine.width : ℝ)-1)*(Machine.width : ℝ)^BudgetBound.tau / ((Machine.width : ℝ)^BudgetBound.tau-1))

theorem constant_positive : 0 < constant := by
  have hx : 1 < (Machine.width : ℝ)^BudgetBound.tau :=
    Real.one_lt_rpow one_lt_width_real BudgetBound.exponent_range.1
  unfold constant
  exact mul_pos coefficient_positive
    (div_pos (mul_pos (by linarith [two_le_width_real]) (by linarith)) (by linarith))

theorem sum_bound (V e k : ℕ) (hk : Machine.width^k ≤ e) :
    ((ArbitraryWidthPieces.depths Machine.width e k).map (fun j => (budget j V : ℝ))).sum ≤
      constant*V*(e : ℝ)^BudgetBound.tau := by
  have hCV : 0 ≤ coefficient*(V : ℝ) := mul_nonneg coefficient_positive.le (Nat.cast_nonneg _)
  calc
    _ = ∑ j ∈ Finset.range (k+1), (e/Machine.width^j%Machine.width : ℕ)*(budget j V : ℝ) :=
      ArbitraryWidthPieces.real_piece_sum _ _ _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), (e/Machine.width^j%Machine.width : ℕ)*
        (coefficient*(V : ℝ)*((Machine.width^j : ℕ) : ℝ)^BudgetBound.tau) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (budget_bound j V) (Nat.cast_nonneg _)
    _ = coefficient*(V : ℝ)*(∑ j ∈ Finset.range (k+1),
        (e/Machine.width^j%Machine.width : ℕ)*((Machine.width^j : ℕ) : ℝ)^BudgetBound.tau) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ coefficient*(V : ℝ)*
        ((((Machine.width : ℝ)-1)*(Machine.width : ℝ)^BudgetBound.tau /
          ((Machine.width : ℝ)^BudgetBound.tau-1))*(e : ℝ)^BudgetBound.tau) :=
      mul_le_mul_of_nonneg_left
        (Swap.Recurrence.pieces_le two_le_width BudgetBound.exponent_range.1
          (fun j => e/Machine.width^j%Machine.width) (fun j => Nat.mod_lt _ width_pos) hk) hCV
    _ = constant*V*(e : ℝ)^BudgetBound.tau := by unfold constant; ring

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepBudget
