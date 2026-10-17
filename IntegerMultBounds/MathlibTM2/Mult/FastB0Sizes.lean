module
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.Basic.Real.Basic
public import IntegerMultBounds.MathlibTM2.Mult.CRT
public import IntegerMultBounds.Machine
public import IntegerMultBounds.MathlibTM2.Mult.Sizes


/-!
# The window of the banded `B̃₀`

`fastWindow p α = ⌊√p⌋ / (2α) + 1`: the band half width is `8 · fastWindow`.
`fastWindow_sq`: `p ≤ 4 α² m'²`; `fastWindow_le_third`: `3 m' ≤ p` for `α ≥ 2`, `p ≥ 13`.
The Neumann `B̃₀` that this file used to size (`resampB₀NumK`, `fastB0_conditions`) was
replaced by the banded `B̃₀`; restore from `1cb2723b`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

/-! ### The parameters of `Mult/Sizes.lean` -/

section Params

/-- The window `m' = ⌊√p⌋ / (2α) + 1`. -/
def fastWindow (p a : ℕ) : ℕ := Nat.sqrt p / (2 * a) + 1

/-- The window condition `p ≤ 4 α² m'²`. -/
theorem fastWindow_sq (p a : ℕ) (ha : 1 ≤ a) :
    (p : ℝ) ≤ 4 * (a : ℝ) ^ 2 * (fastWindow p a : ℝ) ^ 2 := by
  have h1 : Nat.sqrt p + 1 ≤ 2 * a * fastWindow p a := by
    unfold fastWindow
    exact Nat.lt_mul_div_succ _ (by omega)
  have h2 := Nat.lt_succ_sqrt' p
  have h3 : p ≤ 4 * a ^ 2 * fastWindow p a ^ 2 := by
    have : (Nat.sqrt p + 1) ^ 2 ≤ (2 * a * fastWindow p a) ^ 2 := Nat.pow_le_pow_left h1 2
    rw [Nat.succ_eq_add_one] at h2
    nlinarith
  exact_mod_cast h3

theorem fastWindow_le_third {p a : ℕ} (ha : 2 ≤ a) (hp : 13 ≤ p) : 3 * fastWindow p a ≤ p := by
  unfold fastWindow
  have h1 : Nat.sqrt p / (2 * a) ≤ Nat.sqrt p / 4 := Nat.div_le_div_left (by omega) (by norm_num)
  have h2 := Nat.sqrt_le_self p
  omega

end Params

end IntegerMultBounds.MathlibTM2.Mult.FastB0
