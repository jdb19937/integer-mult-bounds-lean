module

import IntegerMultBounds.MathlibTM2.Fast.CompactFinalR
public import IntegerMultBounds.MathlibTM2.Statement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Integer multiplication below `n log n` on Mathlib's Turing machines

`mulInTime` exposes the explicit improved saving; `statement` retains the existential
interface in `Statement.lean`. Both follow from the rounded compact host multiplier
`compactR_mulInTime_final` and its checked runtime bound at `ε = 79/256`.

The exact-arithmetic chains (`mulInTime_exact`, `compact_mulInTime` and the `d^6 ≤ b` width
lemmas behind them) no longer hold above `ε = 1/4` and were removed; restore them from the parent
of the commit that introduced this note.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2

/-- The complete compact multiplier has the explicit saving `36261 · 2^-48 = ε (1-λ')`,
with `ε = 79/256` and `1-λ' = 459 · 2^-40`. -/
theorem mulInTime : MulInTime (36261 / 2 ^ 48 : ℝ) :=
  Fast.Main.compactR_mulInTime_final

/-- The saving exceeds `2^-33` by more than ten percent. -/
theorem saving_gt : 11 / 10 * (2 ^ 33 : ℝ)⁻¹ < 36261 / 2 ^ 48 := by norm_num

theorem statement : Statement :=
  ⟨_, by positivity, mulInTime⟩

end IntegerMultBounds.MathlibTM2
