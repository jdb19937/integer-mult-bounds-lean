module

import IntegerMultBounds.MathlibTM2.Fast.CompactSourceCost
public import IntegerMultBounds.MathlibTM2.Cost.CompactStageGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcMachine
import IntegerMultBounds.MathlibTM2.Fast.MainTimeRuns
import IntegerMultBounds.MathlibTM2.Cost.MatchBandLoad
public import IntegerMultBounds.MathlibTM2.Cost.DirectScale
public import IntegerMultBounds.MathlibTM2.Fast.MainProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Three actual expanded source runs with explicit retuned transform costs. -/
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

def compactMainRuns {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ) (cF cO : ℕ → ℕ) (n : ℕ) : ℕ :=
  if hd0 : 0 < d n then
    srcDirectPCost compactSrcM n (w n) (D.Wt n) (cF n) (cO n) hd0 (D.V₀ n) (D.σ₀ n)
        (preRecsA n (D.Wt n) hd0 0 ++ (preRecsA n (D.Wt n) hd0 0 ++ D.restA n))
        (preRecsB n (D.Wt n) hd0 0 ++ (preRecsB n (D.Wt n) hd0 0 ++ D.restB n)) +
      srcDirectPCost compactSrcM n (w n) (D.Wt n) (cF n) (cO n) hd0 (mnV₁ D n hd0) (mnσ₁ D n hd0)
        (preRecsA n (D.Wt n) hd0 0 ++ D.restA n) (preRecsB n (D.Wt n) hd0 0 ++ D.restB n) +
      oppDirectPCost compactSrcM n (w n) (D.Wt n) (cF n) (cO n) hd0 (mnV₂ D n hd0) (mnσ₂ D n hd0)
        (D.restA n) (D.restB n)
  else 0

theorem compactMain_runs_le {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (cF cO : ℕ → ℕ) {Cs : ℝ}
    (hCs : ∀ᶠ n in atTop, ((cF n + cO n : ℕ) : ℝ) ≤ Cs * CompactTotal.conv n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, (compactMainRuns D cF cO n : ℝ) ≤
      C * (IntegerMultBounds.MathlibTM2.Cost.totDirectCRT n + IntegerMultBounds.MathlibTM2.Cost.totResamp n + CompactTotal.conv n +
        (T n : ℝ) * IntegerMultBounds.MathlibTM2.Cost.totMp n + (T n : ℝ) * p n) := by
  obtain ⟨cw, cW, hratio⟩ := D.ratio
  obtain ⟨C1, hC1, hrun⟩ := compactSource_direct_le (K := K) cw cW
  refine ⟨3 * C1 + 6 * max Cs 0, by positivity, ?_⟩
  filter_upwards [eventually_big, hratio, D.widths, D.clrA, D.clrB, hCs, hrun,
    mn_clrA_cfg cw cW, mt_band_clr_cfg cw cW, D.base] with n h hrt hwd hcA hcB hcs hr hcfgA hcfgB
    hbase
  obtain ⟨hwc, hWc⟩ := hrt
  obtain ⟨hgw, -, -⟩ := hwd
  change _ ≤ _ * compactSourceSum n
  have hd0 : 0 < d n := h.one_le_d
  have hb := h.sixteen_le_b
  have hg : 4 ≤ Chirp.chirpGuard (d n) := by unfold Chirp.chirpGuard; omega
  have hpb : p n = 6 * b n := rfl
  have hpw : p n + 2 ≤ w n := by omega
  have h11 : 11 ≤ w n := by omega
  have h101 : 101 ≤ w n := by omega
  obtain ⟨-, -, -, -, -, g6⟩ := compactSource_sum_ge h
  have hconv := CompactTotal.conv_nonneg h
  have hcs' := mn_le_max_mul hcs hconv g6
  have hS0 : 0 ≤ compactSourceSum n := hconv.trans g6
  unfold compactMainRuns
  rw [dite_eq_left hd0]
  set RA := preRecsA (A := prime + K) n (D.Wt n) hd0 0 with hRA
  set RB := preRecsB (A := prime + K) n (D.Wt n) hd0 0 with hRB
  have hA3 : 3 ≤ prime + K := by have := IntegerMultBounds.Networks.Shared50ModularControl.prime_odd; omega
  have hb0 : BandBase (D.σ₀ n) (w n) crtHd := (hbase hd0).bBase
  have hb1 : BandBase (mnσ₁ D n hd0) (w n) crtHd := bandCfgB_base hb0 hA3 _
  have hb2 : BandBase (mnσ₂ D n hd0) (w n) crtHd := bandCfgB_base hb1 hA3 _
  have b1 := (hr hd0 (w n) (D.Wt n) (cF n) (cO n) (D.V₀ n) (D.σ₀ n) (RA ++ (RA ++ D.restA n))
    (RB ++ (RB ++ D.restB n)) hpw hwc hWc hcA hb0 hcB).1
  have b2 := (hr hd0 (w n) (D.Wt n) (cF n) (cO n) (mnV₁ D n hd0) (mnσ₁ D n hd0)
    (RA ++ D.restA n) (RB ++ D.restB n) hpw hwc hWc
    (hcfgA hd0 (w n) (D.Wt n) (D.V₀ n) crtHd (RA ++ (RA ++ D.restA n)) (d n - 1) h11 hwc hWc)
    hb1 (hcfgB hd0 (w n) (D.Wt n) (D.σ₀ n) crtHd (RB ++ (RB ++ D.restB n)) (d n - 1) h101 hwc
      hWc hb0 hA3)).1
  have b3 := (hr hd0 (w n) (D.Wt n) (cF n) (cO n) (mnV₂ D n hd0) (mnσ₂ D n hd0)
    (D.restA n) (D.restB n) hpw hwc hWc
    (hcfgA hd0 (w n) (D.Wt n) (mnV₁ D n hd0) crtHd (RA ++ D.restA n) (d n - 1) h11 hwc hWc)
    hb2 (hcfgB hd0 (w n) (D.Wt n) (mnσ₁ D n hd0) crtHd (RB ++ D.restB n) (d n - 1) h101 hwc
      hWc hb1 hA3)).2
  push_cast at b1 b2 b3 hcs' ⊢
  calc _ ≤ 3 * (C1 * compactSourceSum n) + 6 * ((cF n : ℝ) + cO n) := by linarith
    _ ≤ 3 * (C1 * compactSourceSum n) + 6 * (max Cs 0 * compactSourceSum n) := by linarith
    _ = _ := by ring

end

end IntegerMultBounds.MathlibTM2.Fast.Main
