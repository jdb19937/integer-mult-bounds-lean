module

public import IntegerMultBounds.MathlibTM2.Fast.CompactBdRetune
import IntegerMultBounds.MathlibTM2.Fast.CompactParamPipeline
import IntegerMultBounds.MathlibTM2.Fast.DistSynCost
import IntegerMultBounds.MathlibTM2.Fast.DistCost
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Explicit cost of the retuned wire bundle, including every extra operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter


noncomputable section

theorem compactDsyWiresCost_le : ∀ᶠ n in atTop,
    compactDsyWiresCost n ≤ 2 * 10 ^ 7 * (b n + 1) ^ 7 + 30 * (r n * dsW n) := by
  filter_upwards [eventually_big] with n hbig
  have hn := hbig.1
  obtain ⟨hN, hℓ, _, hD, hw, hWW⟩ := dsy_sizes hbig
  have hK : CompactSizes.K n≤b n+2 :=
    (CompactSizes.K_le_d n).trans ((d_le_b n).trans (by omega))
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  set M := b n + 2 with hM
  have h2 : 2 ≤ M := by omega
  have hG := dsySynCostG_le (WL := dsWL n (dsW n)) hN hℓ hK hD h2
  have hWL : dsWL n (dsW n) ≤ r n * dsW n + 3 * M ^ 2 := by
    unfold dsWL
    have hN' : logT n - ℓ n ≤ M := by rw [← ds_sum_cvAx hn]; exact hN
    have : (logT n - ℓ n) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hN' 2
    nlinarith
  have hr : r n ≤ r n * dsW n := Nat.le_mul_of_pos_right _ hw1
  have hM7 : M ^ 7 ≤ 128 * (b n + 1) ^ 7 := by
    have : M ≤ 2 * (b n + 1) := by omega
    calc M ^ 7 ≤ (2 * (b n + 1)) ^ 7 := Nat.pow_le_pow_left this 7
      _ = 128 * (b n + 1) ^ 7 := by ring
  have hM2 : M ^ 2 ≤ M ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hM1 : M ≤ M ^ 7 := Nat.le_self_pow (by norm_num) M
  unfold compactDsyWiresCost compactDsyTailCost
  nlinarith


/-- The retune is charged separately, including clearing the old unary chunk. -/
theorem compactDsRetuneCost_le (n : ℕ) :
    compactDsRetuneCost n (pmW n) (K n)≤2^23*(b n+1)^3 := by
  have hpatch := compactPmOverwriteAtoms_le n
  have htable := ds_tblC_le n
  have hprod := Nat.mul_le_mul hpatch htable
  have hk : CompactSizes.K n≤b n := (CompactSizes.K_le_d n).trans (d_le_b n)
  have hold : K n≤b n := (K_le_d n).trans (d_le_b n)
  have hW : pmW n≤36*(b n+1) := by
    have hs := pm_size_le (n:=n)
    unfold pmW
    omega
  have hun := Nat.mul_le_mul hW (show 4*CompactSizes.K n+11≤15*(b n+1) by omega)
  have hb : 1≤b n+1 := by omega
  have hb2 : (b n+1)^2≤(b n+1)^3 := Nat.pow_le_pow_right hb (by decide)
  have hb1 : b n+1≤(b n+1)^3 := Nat.le_self_pow (by decide) _
  unfold compactDsRetuneCost
  norm_num only [Nat.reducePow]
  nlinarith

/-- An explicit dyadic coefficient pays both retuning and compact wire construction. -/
theorem compactBdWiresCost_le : ∀ᶠ n in atTop,
    compactBdWiresCost n≤2^25*(b n+1)^7+2^5*(r n*dsW n) := by
  filter_upwards [compactDsyWiresCost_le] with n hw
  have hp := compactDsRetuneCost_le n
  have hb : (b n+1)^3≤(b n+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold compactBdWiresCost
  norm_num only [Nat.reducePow] at hp ⊢
  nlinarith

end
end IntegerMultBounds.MathlibTM2.Fast.Main
