module
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerScalarBudget
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd

/-! One explicit polynomial scalar budget for the actual compact caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

def compactCallerCombinedBudget (c cDiv eDiv p : ℕ) :=
  2^(c+cDiv+2)*(p+1)^(max 2 eDiv)

theorem compactCallerScalarBudget_le_combined (c cDiv eDiv p : ℕ) :
    compactCallerScalarBudget c p≤compactCallerCombinedBudget c cDiv eDiv p :=
  Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : c+2≤c+cDiv+2))
    (Nat.pow_le_pow_right (Nat.succ_pos p) (Nat.le_max_left 2 eDiv))

theorem compactCallerDivisorBudget_le_combined (c cDiv eDiv p : ℕ) :
    2^cDiv*(p+1)^eDiv≤compactCallerCombinedBudget c cDiv eDiv p :=
  Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : cDiv≤c+cDiv+2))
    (Nat.pow_le_pow_right (Nat.succ_pos p) (Nat.le_max_right 2 eDiv))

end
end IntegerMultBounds.MathlibTM2.Cost
