module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRegs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! State capacity for the expanded main machine, including the compact native runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
noncomputable section

/-- Retain all existing stage capacities and reserve compact runtime states. -/
def compactMnQ : ℕ := max mnQ compactRuntimeStates+1

lemma compactMnQ_pos : 0<compactMnQ := by unfold compactMnQ; omega
lemma compactMnQ_legacy : mnQ≤compactMnQ := (le_max_left _ _).trans (Nat.le_add_right _ _)
lemma compactMnQ_runtime : compactRuntimeStates≤compactMnQ :=
  (le_max_right _ _).trans (Nat.le_add_right _ _)

/-- Procedure names remain a parameter until the combined dispatch table is chosen. -/
abbrev CompactMnPr (P : Type) (A : ℕ) := Pr P compactMnT compactMnQ A Unit

end
end IntegerMultBounds.MathlibTM2.Fast.Main
