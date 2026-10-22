module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! A natural-number bit mask packages all target coefficients. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.MaskWeightsB

/-- The coefficient of a target in a mask. -/
def coeff (m t : Nat) : ZMod 2 := if m.testBit t then 1 else 0

/-- A structural XOR sum, used by the concrete coefficient checks. -/
def xorSum : List Nat → Nat
  | [] => 0
  | m :: ms => m ^^^ xorSum ms

@[simp] theorem coeff_zero (t : Nat) : coeff 0 t = 0 := by simp [coeff]

theorem coeff_xor (m n t : Nat) : coeff (m ^^^ n) t = coeff m t + coeff n t := by
  simp only [coeff, Nat.testBit_xor]
  cases m.testBit t <;> cases n.testBit t <;> decide +revert

theorem coeff_xorSum (ms : List Nat) (t : Nat) :
    coeff (xorSum ms) t = (ms.map fun m => coeff m t).sum := by
  induction ms with
  | nil => simp [xorSum]
  | cons m ms ih => simp only [xorSum, coeff_xor, List.map_cons, List.sum_cons, ih]

end IntegerMultBounds.MathlibTM2.M8.Local.MaskWeightsB
