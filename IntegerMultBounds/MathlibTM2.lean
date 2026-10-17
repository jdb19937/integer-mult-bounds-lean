module

public import IntegerMultBounds.MathlibTM2.Main
public import IntegerMultBounds.MathlibTM2.FastPath
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

/-!
# Integer multiplication on Mathlib's `Turing.FinTM2`

`IntegerMultBounds.MathlibTM2.Statement` states multiplication below `n log n` using only Mathlib
vocabulary. `IntegerMultBounds.MathlibTM2.statement` proves it unconditionally via the complete
fast host multiplier. The separate `statement_of_endToEnd` bridge also derives it from the
stronger compact-control target `IntegerMultBounds.Machine.EndToEnd`.
-/
