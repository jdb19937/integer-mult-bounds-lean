module

public import IntegerMultBounds.MathlibTM2.Fast.CompactBundleWires
public import IntegerMultBounds.MathlibTM2.Fast.MainFinal
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeGlue
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransforms
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Complete cost envelope for the concrete compact branch. The machine-execution
contract is still explicit; the unconditional public multiplier is not changed here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
noncomputable section

/-- The actual retuned distribution, including its charged wires update. -/
def compactRetunedDist := compactBdDist mn_postParam_bd

/-- The two complete transforms, including layout, bootstrap and cleanup. -/
def compactRetunedCF (n : ℕ) : ℕ := compactSynRetunedFwdCost n (compactBlCL n)
def compactRetunedCO (n : ℕ) : ℕ := compactSynRetunedOppCost n (compactBlCL' n)

/-- Full cost envelope with actual source stages and a fixed normalization charge. -/
def compactRetunedTime (c extra n : ℕ) : ℕ :=
  compactMainTime compactRetunedDist
    (fun n => compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n + extra)
    compactMnT c n

end
end IntegerMultBounds.MathlibTM2.Fast.Main
