module

import IntegerMultBounds.MathlibTM2.Fast.MainTimeRuns
public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcMachine
import IntegerMultBounds.MathlibTM2.Cost.MatchBandB
public import IntegerMultBounds.MathlibTM2.Cost.CompactStageGrowth
public import IntegerMultBounds.MathlibTM2.Cost.MatchConv
import IntegerMultBounds.MathlibTM2.Cost.MatchChirp
import IntegerMultBounds.MathlibTM2.Cost.MatchResampA
public import IntegerMultBounds.MathlibTM2.Cost.DirectScale
public import IntegerMultBounds.MathlibTM2.Fast.SrcDirectStage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Actual expanded source-stage costs against the retuned envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Cost


attribute [local irreducible] mnT mnQ compactMnT compactMnQ

noncomputable section

/-- The sum of the terms against which the runs are matched. -/
def compactSourceSum (n : ℕ) : ℝ :=
  totDirectCRT n + totResamp n + CompactTotal.conv n + (T n : ℝ) * totMp n + (T n : ℝ) * p n

lemma compactSource_sum_parts {n : ℕ} (h : Big n) :
    0 ≤ totDirectCRT n ∧ 0 ≤ totResamp n ∧ 0 ≤ CompactTotal.conv n ∧ 0 ≤ (T n : ℝ) * totMp n ∧
      0 ≤ (T n : ℝ) * p n :=
  ⟨mt_directCRT_nonneg n, mt_resamp_nonneg n, CompactTotal.conv_nonneg h, mt_Tmp_nonneg n, mt_Tp_nonneg n⟩

lemma compactSource_sum_ge {n : ℕ} (h : Big n) :
    totResamp n + totDirectCRT n + (T n : ℝ) * p n ≤ compactSourceSum n ∧
      (T n : ℝ) * totMp n ≤ compactSourceSum n ∧ CompactTotal.conv n + (T n : ℝ) * totMp n ≤ compactSourceSum n ∧
      (T n : ℝ) * p n ≤ compactSourceSum n ∧ totDirectCRT n ≤ compactSourceSum n ∧ CompactTotal.conv n ≤ compactSourceSum n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := compactSource_sum_parts h
  unfold compactSourceSum
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem compactSource_box_le (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, p n + 2 ≤ w → w ≤ cw * p n →
      (cvBoxCost Tm (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) 0 0 : ℝ) ≤
        mtCvC Tm cw * (CompactTotal.conv n + (T n : ℝ) * totMp n) := by
  filter_upwards [mt_cv_box_le Tm cw, eventually_big] with n hn h w hw1 hw
  refine (hn w hw1 hw).trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hI := CompactTotal.conv_inner_nonneg h
    have hdK : (0 : ℝ) ≤ (d n : ℝ) * Mult.CompactSizes.K n := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hpK : (0 : ℝ) ≤ (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hℓd : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam' :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hTp := mt_Tp_nonneg n
    have e : CompactTotal.conv n = (T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n +
        (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) + (ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam') +
        (T n : ℝ) * p n * grLogLog ((r n : ℝ) * p n) := by unfold CompactTotal.conv; ring
    have hrest : 0 ≤ (T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n +
        (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) + (ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam') :=
      mul_nonneg hTp (by linarith)
    rw [e]
    linarith
  · unfold mtCvC
    have := mt_CM_nonneg Tm cw
    have hR : 0 ≤ grRingConst (6 + 4 * cw) := by
      have := gr_ringConst_ge (A := 6 + 4 * cw) (by omega)
      have : (0 : ℝ) ≤ 12 * ((6 + 4 * cw : ℕ) : ℝ) := by positivity
      linarith
    have hK : (0 : ℝ) ≤ mtCvK Tm cw := Nat.cast_nonneg _
    have hc : (0 : ℝ) ≤ 4 * (Schoenhage.Schedule.costC Schoenhage.cA Schoenhage.cB Schoenhage.cC0 : ℝ) + 261000 := by positivity
    have hTm : (0 : ℝ) ≤ (Tm : ℝ) + 1097 := by positivity
    have := mul_nonneg hTm (mul_nonneg hc hR)
    linarith

/-- **One run of `srcCore`** on base files whose first cleared registers hold at most `T w`
symbols: at most `C (totDirectCRT + totResamp + CompactTotal.conv + T M(p) + T p) + 2 cF + cO`. -/
lemma compactSource_core_le {K : ℕ} (cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W cF cO : ℕ)
      (V₀ : RsaV (RsaX 6) (prime + K)) (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)))
      (restA restB : List (Fin (prime + K + 4))),
      p n + 2 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (∀ x ∈ preClrA crtHd, (V₀.get x).length ≤ T n * w) →
      BandBase σ₀ w crtHd → (∀ r ∈ bandClrB crtHd, (σ₀ r).length ≤ T n * w) →
      (srcCoreCost compactSrcM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
        C * compactSourceSum n + ((2 * cF + cO : ℕ) : ℝ) := by
  obtain ⟨CA, hCA⟩ := mt_rsa_stage_le_linear compactMnT 6 K cw cW
  obtain ⟨CB, hCB⟩ := mt_band_stage_le_linear compactMnT 6 K cw cW
  obtain ⟨CK, hCK⟩ := mt_ch_kernel_le compactMnT cw cW
  set c4 : ℝ := mtCM compactMnT cw + 21 * cw + 28
  set c5 : ℝ := 6 * cw + 19
  set c6 : ℝ := mtCvC compactMnT cw
  set c7 : ℝ := ((60 * cw + 200 : ℕ) : ℝ)
  refine ⟨max CA 0 + max CB 0 + max CK 0 + 2 * max c4 0 + max c5 0 + max c6 0 + max c7 0,
    by positivity, ?_⟩
  filter_upwards [eventually_big, hCA, hCB, hCK, mt_ch_chirpMul_le compactMnT cw, mt_ch_scale_le cw,
    compactSource_box_le compactMnT cw, mn_ldcBlocks_le] with n h hA hB hK hC hS hV hL
  intro hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  obtain ⟨g1, g2, g3, g4, -, -⟩ := compactSource_sum_ge h
  obtain ⟨-, -, -, q4, q5⟩ := compactSource_sum_parts h
  have q0 : 0 ≤ totResamp n + totDirectCRT n + (T n : ℝ) * p n := by
    obtain ⟨r1, r2, -, -, r5⟩ := compactSource_sum_parts h; linarith
  have q3 : 0 ≤ CompactTotal.conv n + (T n : ℝ) * totMp n := by
    obtain ⟨-, -, r3, r4, -⟩ := compactSource_sum_parts h; linarith
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
  simp only [show compactSrcM.hd = crtHd from rfl]
  generalize (∏ i, t n i) * (cmulCost compactMnT w + 21 * w + 8) + 20 = P1 at a4 ⊢
  generalize (∏ i, t n i) * (6 * w + 4 * gamma n + 14) + 4 = P2 at a5 ⊢
  generalize (∏ i, t n i) * w = XW at a7 ⊢
  push_cast at a1 a2 a3 a4 a5 a6 a7 ⊢
  calc _ ≤ max CA 0 * compactSourceSum n + max CB 0 * compactSourceSum n + max CK 0 * compactSourceSum n +
        2 * (max c4 0 * compactSourceSum n) + max c5 0 * compactSourceSum n + max c6 0 * compactSourceSum n +
        max c7 0 * compactSourceSum n + (2 * (cF : ℝ) + cO) := by linarith
    _ = _ := by ring

lemma compactSource_direct_le {K : ℕ} (cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W cF cO : ℕ)
      (V₀ : RsaV (RsaX 6) (prime + K)) (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)))
      (restA restB : List (Fin (prime + K + 4))),
      p n + 2 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (∀ x ∈ preClrA crtHd, (V₀.get x).length ≤ T n * w) →
      BandBase σ₀ w crtHd → (∀ r ∈ bandClrB crtHd, (σ₀ r).length ≤ T n * w) →
      (srcDirectPCost compactSrcM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
          C * compactSourceSum n + ((2 * cF + cO : ℕ) : ℝ) ∧
        (oppDirectPCost compactSrcM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
          C * compactSourceSum n + ((2 * cF + cO : ℕ) : ℝ) := by
  obtain ⟨C0, hC0, hcore⟩ := compactSource_core_le (K := K) cw cW
  set c1 : ℝ := mtCrtDirectEntryC compactMnT cw
  set c2 : ℝ := ((4 * cw + 4 : ℕ) : ℝ)
  set c3 : ℝ := 5 * cw + 8
  set c4 : ℝ := ((2 * cw + 2 : ℕ) : ℝ)
  refine ⟨C0 + max c1 0 + max c2 0 + 2 * max c3 0 + 2 * max c4 0, by positivity, ?_⟩
  filter_upwards [eventually_big, hcore, mn_direct_crt_le compactMnT cw K, mt_ch_conj_le cw]
    with n h hco hcr hcj
  intro hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  obtain ⟨-, -, -, g4, g5, -⟩ := compactSource_sum_ge h
  obtain ⟨q1, -, -, -, q5⟩ := compactSource_sum_parts h
  have a0 := hco hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  have a1f := mn_le_max_mul (hcr w hwc true) q1 g5
  have a1i := mn_le_max_mul (hcr w hwc false) q1 g5
  have hX : (∏ i, t n i) ≤ T n := (mt_prod_t h).le
  have a2 := mn_le_max_mul (c := c2) (mn_lin_le (a := 4) (c := 4) h hX hwc) q5 g4
  have a3 := mn_le_max_mul (c := c3) (hcj w hwc) q5 g4
  have a4 := mn_le_max_mul (c := c4) (mn_lin_le (a := 2) (c := 2) h hX hwc) q5 g4
  refine ⟨?_, ?_⟩
  · unfold srcDirectPCost
    push_cast at a0 a1f a2 ⊢
    calc _ ≤ max c1 0 * compactSourceSum n + max c2 0 * compactSourceSum n +
          (C0 * compactSourceSum n + (2 * (cF : ℝ) + cO)) := by linarith
      _ ≤ (C0 + max c1 0 + max c2 0 + 2 * max c3 0 + 2 * max c4 0) * compactSourceSum n +
          (2 * (cF : ℝ) + cO) := by
        have : 0 ≤ (2 * max c3 0 + 2 * max c4 0) * compactSourceSum n :=
          mul_nonneg (by positivity) (q5.trans g4)
        nlinarith
  · unfold oppDirectPCost srcConjCost
    push_cast at a0 a1i a3 a4 ⊢
    calc _ ≤ max c1 0 * compactSourceSum n + 2 * (max c3 0 * compactSourceSum n) +
          2 * (max c4 0 * compactSourceSum n) + (C0 * compactSourceSum n + (2 * (cF : ℝ) + cO)) := by
          linarith
      _ ≤ (C0 + max c1 0 + max c2 0 + 2 * max c3 0 + 2 * max c4 0) * compactSourceSum n +
          (2 * (cF : ℝ) + cO) := by
        have : 0 ≤ max c2 0 * compactSourceSum n := mul_nonneg (le_max_right _ _) (q5.trans g4)
        nlinarith


end
end IntegerMultBounds.MathlibTM2.Fast.Main
