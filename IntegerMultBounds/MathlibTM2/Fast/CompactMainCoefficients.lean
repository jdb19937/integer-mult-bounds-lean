module
public import IntegerMultBounds.MathlibTM2.Fast.MainChain
public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
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


/-! Numerical output facts for the actual retuned arithmetic chain. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open Filter
noncomputable section

def compactMainCoeffs (n x y : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (∏ i,s n i) => rndCoeff (b n) (∏ i,s n i) (p n)
    (numer (p n) (oppMap n (mnY n x y) ((i : ℕ) : ZMod (∏ i,s n i)))).re

lemma compactMainCoeffs_words (n x y : ℕ) :
    mnWords mnKa n x y=(compactMainCoeffs n x y).flatMap (binSyms (mnWo n)) := rfl

lemma compactMainCoeffs_length (n x y : ℕ) : (compactMainCoeffs n x y).length=S n := by
  rw [compactMainCoeffs,List.length_ofFn]
  rfl

theorem compactMainCoeffs_eventually : ∀ᶠ n : ℕ in atTop,
    1≤b n ∧ 1≤mnWo n ∧ ∀ x y : ℕ,Nat.size x≤n → Nat.size y≤n →
      (∀ z ∈ compactMainCoeffs n x y,z<2^mnWo n) ∧
      evalBase (2^b n) (compactMainCoeffs n x y)=x*y := by
  filter_upwards [eventually_big,eventually_small,eventually_margins,pipeline_correct]
    with n hbig hsmall hmarg hpipe
  obtain ⟨hEs,-⟩ := hmarg
  have hb1 := one_le_b hbig.1
  refine ⟨hb1,by unfold mnWo; omega,?_⟩
  intro x y hsx hsy
  have hY1 : ‖mnY n x y‖≤1/2 := mn_rdV_norm _
    (mn_srcMap_norm hbig hsmall hEs (mn_scaledDigits_norm hb1 _))
    (mn_srcMap_norm hbig hsmall hEs (mn_scaledDigits_norm hb1 _))
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hz
    exact mn_rndCoeff_lt ((norm_le_pi_norm _ _).trans (mn_oppMap_norm hbig hsmall hEs hY1))
  · rw [compactMainCoeffs,← mn_pipelineCoeffs_eq (srcHd0 hbig) x y]
    exact hpipe x y hsx hsy

end
end IntegerMultBounds.MathlibTM2.Fast.Main
