module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsCost
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeBound
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeGlue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The compact main bound reduced to its two complete transform costs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

/-- Three actual expanded source runs, all other main stages, and cleanup satisfy
 the stronger bound whenever the two complete transform costs match the compact envelope. -/
theorem compactMain_runs_time_isBigO {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (cF cO : ℕ → ℕ) (host c extra : ℕ) {Cs : ℝ}
    (hCs : ∀ᶠ n in atTop, ((cF n + cO n : ℕ) : ℝ) ≤ Cs * CompactTotal.conv n) :
    (fun n => (compactMainTime D (fun n => compactMainRuns D cF cO n + extra) host c n : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - CompactTotal.kappa) := by
  obtain ⟨Cr, _, hR⟩ := compactMain_runs_le D cF cO hCs
  exact compactMain_time_isBigO D (compactMainRuns D cF cO) host c extra hR

end
end IntegerMultBounds.MathlibTM2.Fast.Main
