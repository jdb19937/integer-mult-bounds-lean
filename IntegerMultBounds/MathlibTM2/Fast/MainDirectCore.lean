module

import IntegerMultBounds.MathlibTM2.Fast.MainTimeRuns
import IntegerMultBounds.MathlibTM2.Cost.MatchBandB
import IntegerMultBounds.MathlibTM2.Cost.MatchConv
import IntegerMultBounds.MathlibTM2.Cost.MatchChirp
import IntegerMultBounds.MathlibTM2.Cost.MatchResampA
public import IntegerMultBounds.MathlibTM2.Cost.DirectScale
public import IntegerMultBounds.MathlibTM2.Fast.MainRegs
public import IntegerMultBounds.MathlibTM2.Fast.SrcStage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # Linear routing charge for the existing source-transform core

The transform costs are explicit additive parameters. The concrete direct CRT
machine must still discharge them before the final multiplier can use this bound.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Cost


attribute [local irreducible] mnT mnQ

noncomputable section

/-- The sum of the terms against which the runs are matched. -/
def mnDirectRunSum (n : ℕ) : ℝ :=
  totDirectCRT n + totResamp n + totConv n + (T n : ℝ) * totMp n + (T n : ℝ) * p n

lemma mn_directRunSum_parts {n : ℕ} (h : Big n) :
    0 ≤ totDirectCRT n ∧ 0 ≤ totResamp n ∧ 0 ≤ totConv n ∧ 0 ≤ (T n : ℝ) * totMp n ∧
      0 ≤ (T n : ℝ) * p n :=
  ⟨mt_directCRT_nonneg n, mt_resamp_nonneg n, tot_conv_nonneg h, mt_Tmp_nonneg n, mt_Tp_nonneg n⟩

lemma mn_directRunSum_ge {n : ℕ} (h : Big n) :
    totResamp n + totDirectCRT n + (T n : ℝ) * p n ≤ mnDirectRunSum n ∧
      (T n : ℝ) * totMp n ≤ mnDirectRunSum n ∧ totConv n + (T n : ℝ) * totMp n ≤ mnDirectRunSum n ∧
      (T n : ℝ) * p n ≤ mnDirectRunSum n ∧ totDirectCRT n ≤ mnDirectRunSum n ∧ totConv n ≤ mnDirectRunSum n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mn_directRunSum_parts h
  unfold mnDirectRunSum
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **One run of `srcCore`** on base files whose first cleared registers hold at most `T w`
symbols: at most `C (totDirectCRT + totResamp + totConv + T M(p) + T p) + 2 cF + cO`. -/
lemma mn_core_le_linear {K : ℕ} (cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W cF cO : ℕ)
      (V₀ : RsaV (RsaX 6) (prime + K)) (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)))
      (restA restB : List (Fin (prime + K + 4))),
      p n + 2 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (∀ x ∈ preClrA crtHd, (V₀.get x).length ≤ T n * w) →
      BandBase σ₀ w crtHd → (∀ r ∈ bandClrB crtHd, (σ₀ r).length ≤ T n * w) →
      (srcCoreCost mnM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
        C * mnDirectRunSum n + ((2 * cF + cO : ℕ) : ℝ) := by
  obtain ⟨CA, hCA⟩ := mt_rsa_stage_le_linear mnT 6 K cw cW
  obtain ⟨CB, hCB⟩ := mt_band_stage_le_linear mnT 6 K cw cW
  obtain ⟨CK, hCK⟩ := mt_ch_kernel_le cw cW
  set c4 : ℝ := mtCM cw + 21 * cw + 28
  set c5 : ℝ := 6 * cw + 19
  set c6 : ℝ := mtCvC cw
  set c7 : ℝ := ((60 * cw + 200 : ℕ) : ℝ)
  refine ⟨max CA 0 + max CB 0 + max CK 0 + 2 * max c4 0 + max c5 0 + max c6 0 + max c7 0,
    by positivity, ?_⟩
  filter_upwards [eventually_big, hCA, hCB, hCK, mt_ch_chirpMul_le cw, mt_ch_scale_le cw,
    mt_cv_box_le_conv cw, mn_ldcBlocks_le] with n h hA hB hK hC hS hV hL
  intro hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  obtain ⟨g1, g2, g3, g4, -, -⟩ := mn_directRunSum_ge h
  obtain ⟨-, -, -, q4, q5⟩ := mn_directRunSum_parts h
  have q0 : 0 ≤ totResamp n + totDirectCRT n + (T n : ℝ) * p n := by
    obtain ⟨r1, r2, -, -, r5⟩ := mn_directRunSum_parts h; linarith
  have q3 : 0 ≤ totConv n + (T n : ℝ) * totMp n := by
    obtain ⟨-, -, r3, r4, -⟩ := mn_directRunSum_parts h; linarith
  have a1 := mn_le_max_mul (hA hd0 w W V₀ crtHd restA (by omega) hwc hWc hclrA) q0 g1
  have a2 := mn_le_max_mul (hB hd0 w W σ₀ crtHd restB (by omega) hwc hWc hbB
    (by have := IntegerMultBounds.Networks.Shared50ModularControl.prime_odd; omega) hclrB) q0 g1
  have a3 := mn_le_max_mul (hK w W (by omega) hwc hWc) q4 g2
  have a4 := mn_le_max_mul (hC w (by omega) hwc) q4 g2
  have a5 := mn_le_max_mul (hS w hwc) q5 g4
  have a6 := mn_le_max_mul (hV w hpw hwc) q3 g3
  obtain ⟨hLT, hLS⟩ := hL (prime + K)
  have hX : (∏ i, t n i) ≤ T n := (mt_prod_t h).le
  have hXW : (∏ i, t n i) * w ≤ cw * (T n * p n) := by
    calc (∏ i, t n i) * w ≤ T n * (cw * p n) := Nat.mul_le_mul hX hwc
      _ = cw * (T n * p n) := by ring
  have hH := IntegerMultBounds.Schoenhage.ring_header_length_le (p n) (2 ^ ℓ n) w
  have hsm := mn_core_small h hXW hLT hLS hwc hH
  have hsm' := (Nat.cast_le (α := ℝ)).2 hsm
  rw [Nat.cast_mul (60 * cw + 200), Nat.cast_mul (T n)] at hsm'
  have a7 := mn_le_max_mul (c := c7) hsm' q5 g4
  unfold srcCoreCost srcCostA srcCostK srcCostC srcCostV srcCostB
  rw [mn_cvBoxCost_split]
  simp only [mnM_hd]
  generalize (∏ i, t n i) * (cmulCost w + 21 * w + 8) + 20 = P1 at a4 ⊢
  generalize (∏ i, t n i) * (6 * w + 4 * gamma n + 14) + 4 = P2 at a5 ⊢
  generalize (∏ i, t n i) * w = XW at a7 ⊢
  push_cast at a1 a2 a3 a4 a5 a6 a7 ⊢
  calc _ ≤ max CA 0 * mnDirectRunSum n + max CB 0 * mnDirectRunSum n + max CK 0 * mnDirectRunSum n +
        2 * (max c4 0 * mnDirectRunSum n) + max c5 0 * mnDirectRunSum n + max c6 0 * mnDirectRunSum n +
        max c7 0 * mnDirectRunSum n + (2 * (cF : ℝ) + cO) := by linarith
    _ = _ := by ring

end

end IntegerMultBounds.MathlibTM2.Fast.Main
