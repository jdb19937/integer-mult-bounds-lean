module
import IntegerMultBounds.MathlibTM2.Fast.CompactSynDispatch
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


/-! Actual retuned round costs: compact bulk and explicit direct boundary rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node Filter
noncomputable section

private theorem dispatchBound (ell K h : ℕ) (hh : h≤ell) :
    compactSynDispatchCost ell K h≤20*ell+26 := by
  have hb : layB ell K≤ell := (Nat.mod_le _ _).trans (Nat.sub_le _ _)
  unfold compactSynDispatchCost compactSynCompareCost
  simp only [Bool.false_eq_true,ite_true,ite_false,Nat.sub_zero]
  split_ifs <;> omega

private theorem layer_le_step (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ell K w l h s : ℕ) : synLayerCost ds es ell K l w h≤synLayerStepCost ds es ell K w l h s := by
  unfold synLayerStepCost
  dsimp only
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
