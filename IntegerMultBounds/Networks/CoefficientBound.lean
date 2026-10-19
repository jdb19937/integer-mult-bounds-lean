module

-- Keep the Mathlib order import: under Mathlib, `ℕ` powers elaborate as `Monoid.npow`, and a
-- `Nat.pow` form of the same literal would make the kernel evaluate the tower when they meet.
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum

/-!
# The coefficient bound of the interchange suppliers

Every rational coefficient of a supplier's field programs has numerator and denominator at most
`coefficientBound = 2 ^ 2 ^ 2 ^ 16`, and the machine's prime exceeds it. The exponent is a chosen
witness of its value, so the kernel never reduces the tower to a literal.
-/

@[expose] public section

namespace IntegerMultBounds.Networks

theorem exists_coefficientExponent : ∃ n : ℕ, n = 2 ^ 2 ^ 16 := ⟨_, rfl⟩

/-- The exponent of the coefficient bound, `2 ^ 2 ^ 16`. -/
noncomputable def coefficientExponent : ℕ := Classical.choose exists_coefficientExponent

/-- The coefficient bound `2 ^ coefficientExponent`. -/
noncomputable def coefficientBound : ℕ := 2 ^ coefficientExponent

theorem coefficientExponent_eq : coefficientExponent = 2 ^ 2 ^ 16 :=
  Classical.choose_spec exists_coefficientExponent

/-- A power of two with exponent at most `coefficientExponent` is within the bound. -/
theorem two_pow_le_coefficientBound {a : ℕ} (ha : a ≤ coefficientExponent) :
    2 ^ a ≤ coefficientBound :=
  pow_le_pow_right₀ one_le_two ha

/-- Exponents up to `2 ^ 53000` are within `coefficientExponent`. -/
theorem le_coefficientExponent {a : ℕ} (ha : a ≤ 2 ^ 53000) : a ≤ coefficientExponent :=
  ha.trans ((pow_le_pow_right₀ one_le_two (by norm_num : 53000 ≤ 2 ^ 16)).trans_eq
    coefficientExponent_eq.symm)

end IntegerMultBounds.Networks
