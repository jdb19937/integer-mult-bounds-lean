module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Budget
public import IntegerMultBounds.Swap.Recurrence
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The power-width bound of the recursive budget

The network's uniform branching (`BitNetwork.branching`: `s / roleCount < m^τ`) bounds the
natural recursive budget by a fixed constant times the volume times the width to the power `τ`
(`power_width_bound`, `descriptor_bound`), as `Shared50RecursiveBudgetBound` does for Shared50.
Natural floor division only decreases the bound. This module bounds the budget; the execution
traces that meet it are `Induction.contract`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.BudgetBound
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Budget (base node budget)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

/-- The width exponent of the network. -/
abbrev tau : ℝ := (Net.net).tau

theorem exponent_range : 0 < tau ∧ tau < 1 := ⟨(Net.net).tau_pos,(Net.net).tau_lt_one⟩

/-- Real normalized recurrence for the compile-time coefficients. -/
def normalized (k : ℕ) : ℕ → ℝ
  | 0 => base k
  | depth+1 => ((Net.net).rankSum : ℝ)/roleCount*normalized k depth+node k

theorem normalized_nonneg (k depth : ℕ) : 0 ≤ normalized k depth := by
  induction depth with
  | zero => exact Nat.cast_nonneg _
  | succ depth ih =>
    exact add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ih) (Nat.cast_nonneg _)

/-- Natural quotients introduce no extra cost, even for zero or nondivisible
volumes. -/
theorem budget_le_normalized (k depth V : ℕ) : (budget k depth V : ℝ) ≤ normalized k depth*V := by
  induction depth generalizing V with
  | zero => simp only [budget,normalized,Nat.cast_mul]; exact le_rfl
  | succ depth ih =>
    have hdiv : ((V/roleCount : ℕ) : ℝ) ≤ (V : ℝ)/roleCount := Nat.cast_div_le
    calc
      (budget k (depth+1) V : ℝ) =
          (node k : ℝ)*V+(Net.net).rankSum*(budget k depth (V/roleCount) : ℝ) := by
        simp only [budget,Nat.cast_add,Nat.cast_mul]
      _ ≤ (node k : ℝ)*V+(Net.net).rankSum*(normalized k depth*((V/roleCount : ℕ) : ℝ)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih _) (Nat.cast_nonneg _))
      _ ≤ (node k : ℝ)*V+(Net.net).rankSum*(normalized k depth*((V : ℝ)/roleCount)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv (normalized_nonneg k depth)) (Nat.cast_nonneg _))
      _ = normalized k (depth+1)*V := by rw [normalized]; ring

theorem branching_bound : ((Net.net).rankSum : ℝ)/roleCount ≤ (width : ℝ)^tau :=
  (Net.net).branching.le

/-- One fixed constant for a fixed compiled return-address capacity, independent
of depth, runtime width, spectators, payload volume and previous stack contents. -/
def constant (k : ℕ) : ℝ :=
  ((base k : ℝ)+(node k : ℝ))*(width : ℝ)^tau/((width : ℝ)^tau-1)

theorem constant_positive (k : ℕ) : 0 < constant k := by
  have hm : (1 : ℝ) < width := by exact_mod_cast (show 1 < width by have := two_le_width; omega)
  have hx : 1 < (width : ℝ)^tau := Real.one_lt_rpow hm (Net.net).tau_pos
  have hb : 0 < base k := by
    unfold Budget.base
    omega
  have hb' : (0 : ℝ) < base k := by exact_mod_cast hb
  have hn : (0 : ℝ) ≤ node k := Nat.cast_nonneg _
  unfold constant
  exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)

theorem normalized_bound (k depth : ℕ) :
    normalized k depth ≤ constant k*((width^depth : ℕ) : ℝ)^tau := by
  exact Swap.Recurrence.power_width_bound (F := normalized k) (m := width)
    (a := ((Net.net).rankSum : ℝ)/roleCount) (L := (base k : ℝ)) (C := (node k : ℝ))
    two_le_width (Net.net).tau_pos (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    branching_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl (fun _ => le_rfl) depth

/-- Budget-only power-width bound with the network's exponent, including every
fixed node, entry, recovery and return coefficient of the budget. -/
theorem power_width_bound (k depth V : ℕ) :
    (budget k depth V : ℝ) ≤ constant k*(V : ℝ)*((width^depth : ℕ) : ℝ)^tau := by
  calc
    (budget k depth V : ℝ) ≤ normalized k depth*V := budget_le_normalized k depth V
    _ ≤ (constant k*((width^depth : ℕ) : ℝ)^tau)*V :=
      mul_le_mul_of_nonneg_right (normalized_bound k depth) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The same bound in the runtime descriptor width and logical volume. -/
theorem descriptor_bound {depth : ℕ} {v : Descriptor} (k : ℕ) (h : Depth.Shape depth v) :
    (budget k depth (volume prime v) : ℝ) ≤
      constant k*(volume prime v : ℝ)*(v.width : ℝ)^tau := by
  rw [h.width]
  exact power_width_bound k depth (volume prime v)

/-- Uniform real bound, with no free schedule or count assumptions. -/
theorem exists_uniform_bound (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ depth V : ℕ,
    (budget k depth V : ℝ) ≤ C*(V : ℝ)*((width^depth : ℕ) : ℝ)^tau :=
  ⟨constant k,constant_positive k,power_width_bound k⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BudgetBound
