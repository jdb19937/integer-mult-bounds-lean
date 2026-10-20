module

public import IntegerMultBounds.Machine.Shared50RecursiveBank
public import IntegerMultBounds.Machine.RecursiveMixedRoleBank
public import IntegerMultBounds.Machine.Shared50OrderedPieces
public import IntegerMultBounds.Machine.RecursiveScalarSchedule
public import IntegerMultBounds.Networks.AffineFieldBijective
public import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
public import IntegerMultBounds.Machine.RecursiveWidthGuard
public import IntegerMultBounds.Machine.FiniteFlow
public import IntegerMultBounds.Machine.FiniteReturnStackAt
public import IntegerMultBounds.Machine.RecursiveFrameControl
public import Mathlib.Tactic.DeriveFintype
public import IntegerMultBounds.Machine.SharedBankFamily
public import IntegerMultBounds.Machine.RecursiveDigitRoleBank
public import IntegerMultBounds.Machine.RecursiveChildReturnRoleBank
public import IntegerMultBounds.Machine.Shared50RecursiveBankReturn
public import IntegerMultBounds.Machine.SharedBankFamilyExact
public import IntegerMultBounds.Machine.RecursiveCallProtocol
public import IntegerMultBounds.Machine.RecursiveRowsSerialization
public import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation
public import IntegerMultBounds.Machine.RecursiveRoleChildCallSetup
public import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
public import IntegerMultBounds.Swap.Recurrence
public import IntegerMultBounds.Shared50Parameters
public import Mathlib.Data.Nat.Cast.Order.Field

/-! Range of the certified Shared50 and supplier exponents, and the Shared50
branching bound against the width `125000`. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50RecursiveBudgetBound
noncomputable section
open Networks
open Shared50TapeGlobal (roleCount)

/-- The exponent of width retains the fixed certified positive saving. -/
theorem tau_range : 0 < Shared50Parameters.tau ∧ Shared50Parameters.tau < 1 := by
  norm_num [Shared50Parameters.tau]

/-- The range of the supplier exponent `Parameters.tau` of the cost chain. -/
theorem exponent_range : 0 < Parameters.tau ∧ Parameters.tau < 1 := by
  norm_num [Parameters.tau]

theorem branching_bound : (Shared50Parameters.s : ℝ)/roleCount ≤ (125000 : ℝ)^Shared50Parameters.tau := by
  rw [Shared50RecursiveNodeLayout.roleCount_eq_W]
  exact Shared50Parameters.branching_bound.le

end
end IntegerMultBounds.Machine.Shared50RecursiveBudgetBound
