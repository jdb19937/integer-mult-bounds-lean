module

import IntegerMultBounds.MathlibTM2.Fast.MainTimeRuns
import IntegerMultBounds.MathlibTM2.Fast.MainTimeGlue
public import IntegerMultBounds.MathlibTM2.Cost.DirectTotal
public import IntegerMultBounds.MathlibTM2.Fast.MainProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The time bound of the fast multiplier

`mnTime_le`: for the time function `mnTime D Y c` of `Fast/MainProg` (the sum of the stage bounds,
the cleanup and the reset), eventually `mnTime D Y c n ≤ totDirectBound C n` for some `C`, given the
transform cost bound `cF + cO = O(totConv)` (`MnSyn.cost`) and the distribution cost bound
`cost n ≤ C n + C (b n + 1)^k` (`MnDist.costBound`). The three source-transform runs are matched in
`Fast/MainTimeRuns` (`mn_runs_le`), every other stage in `Fast/MainTimeGlue`
(`mn_time_le_of_runs`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- **The time bound of the fast multiplier.** -/
theorem mnTime_le {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (Y : MnSyn K Lb w σ) (c : ℕ) :
    ∃ C : ℕ, ∀ᶠ n in atTop, (mnTime D Y c n : ℝ) ≤ IntegerMultBounds.MathlibTM2.Cost.totDirectBound C n := by
  obtain ⟨Cr, -, hR⟩ := mn_runs_le D Y
  exact mn_time_le_of_runs D Y c hR

end IntegerMultBounds.MathlibTM2.Fast.Main
