module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlAllFibers
public import IntegerMultBounds.MathlibTM2.Cost.CRTControlScan
public import IntegerMultBounds.MathlibTM2.Cost.CRTControlOffset
import IntegerMultBounds.MathlibTM2.Cost.CRTControl
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Complete physical fiber-pass cost

This accounts for the actual address initialization, descriptor scanning,
constant loads, offset computation, unary counters, data rotation, reset,
indexed loop, cleanup, and final output reversal. Descriptor generation and
workspace provisioning remain separate charges.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast TableVM

/-- Exact full-pass bound, with prefix width `L-a` and axis volume `2^a`. -/
def crtControlAllFibersCost (D W w S L a k : ℕ) : ℕ :=
  crtControlAllCost D W w (L - a) S (2 ^ a) k

/-- Binary arithmetic, scanning, and loop setup charged to one fiber.
Charging setup once per fiber is a harmless upper bound since a box is nonempty. -/
def crtControlAllPolynomialCost (D W w L : ℕ) : ℕ :=
  crtControlScanCost D W w + 34 * W + 77 + 23 * tblC W w + 9 * L

/-- The complete binary part remains cubic in total address width. -/
theorem crtControlAllPolynomialCost_le {D W w L : ℕ}
    (hD : D ≤ L) (hW : W ≤ 3 * L + 1) (hw : w ≤ W) :
    crtControlAllPolynomialCost D W w L ≤ 2 ^ 16 * (L + 1) ^ 3 := by
  have hscan := crtControlScanCost_le_polynomial hD hW hw
  have hwidth : W + 4 ≤ 5 * (L + 1) := by omega
  have hpow := Nat.pow_le_pow_left hwidth 2
  have hsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hcube : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by nlinarith [Nat.zero_le (L * (L + 1) ^ 2)]
  have htbl : tblC W w ≤ 2 ^ 10 * (L + 1) ^ 2 := by
    unfold tblC
    nlinarith
  unfold crtControlAllPolynomialCost
  norm_num at hscan htbl ⊢
  omega

/-- Exact whole-pass cost splits into a polynomial per-fiber part, the unary
offset materialization/cleanup, and ten data movements per slot plus overhead. -/
theorem crtControlAllFibersCost_decompose {D W w S L a k : ℕ} (ha : a ≤ L) :
    crtControlAllFibersCost D W w S L a k ≤
      2 ^ (L - a) * crtControlAllPolynomialCost D W w L +
      2 ^ (L - a) * crtControlOffsetUnaryCost W S + 2 ^ L * (10 * k + 9) := by
  have hvolume : 2 ^ (L - a) * 2 ^ a = 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel ha]
  have hdata := congrArg (fun x : ℕ => x * (10 * k + 9)) hvolume
  have hN : 1 ≤ 2 ^ (L - a) := Nat.one_le_two_pow
  have hsetup := Nat.mul_le_mul_right (6 * W + 9 * L + 19) hN
  have hprefix : L - a ≤ L := Nat.sub_le _ _
  unfold crtControlAllFibersCost crtControlAllCost crtControlAllPolynomialCost crtControlAllBodyCost
    crtControlScanCost crtControlOffsetUnaryCost
  nlinarith [hdata]

/-- Summing the actual physical pass costs over all pipeline axes fits a
linear number of full-volume coefficient passes, plus an absorbed binary term. -/
theorem crtControlAllFibersCost_pipeline_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ a D W w S k : Fin (d n) → ℕ,
      (∀ i, a i ≤ logT n) → (∀ i, a i = ℓ n ∨ a i = ℓ n - 1) →
      (∀ i, D i ≤ logT n) → (∀ i, W i ≤ 3 * logT n + 1) →
      (∀ i, w i ≤ W i) → (∀ i, S i ≤ 2 ^ a i) → (∀ i, k i ≤ cw * p n) →
      (∑ i, crtControlAllFibersCost (D i) (W i) (w i) (S i) (logT n) (a i) (k i)) ≤
        2 ^ 20 * T n + (2 ^ 7 + 10 * cw + 9) * d n * T n * p n := by
  filter_upwards [crtControl_polynomial_pipeline_le (2 ^ 16) 3, eventually_big]
    with n hpoly hb a D W w S k ha hwidth hD hW hw hS hk
  have hp := hpoly a (fun i => crtControlAllPolynomialCost (D i) (W i) (w i) (logT n))
    ha hwidth (fun i => crtControlAllPolynomialCost_le (hD i) (hW i) (hw i))
  have hu := crtControlOffsetUnaryCost_pipeline_le hb a W S ha hW hS
  have hp₁ : 1 ≤ p n := by have := hb.sixteen_le_b; unfold p; omega
  have hk' : ∀ i, 2 ^ logT n * (10 * k i + 9) ≤ (10 * cw + 9) * T n * p n := by
    intro i
    have hki : 10 * k i + 9 ≤ (10 * cw + 9) * p n := by nlinarith [hk i]
    calc
      _ ≤ T n * ((10 * cw + 9) * p n) := Nat.mul_le_mul_left _ hki
      _ = _ := by ring
  have hs : (∑ i, crtControlAllFibersCost (D i) (W i) (w i) (S i) (logT n) (a i) (k i)) ≤
      (∑ i, 2 ^ (logT n - a i) * crtControlAllPolynomialCost (D i) (W i) (w i) (logT n)) +
      (∑ i, 2 ^ (logT n - a i) * crtControlOffsetUnaryCost (W i) (S i)) +
      d n * ((10 * cw + 9) * T n * p n) := by
    calc
      _ ≤ ∑ i, (2 ^ (logT n - a i) * crtControlAllPolynomialCost (D i) (W i) (w i) (logT n) +
          2 ^ (logT n - a i) * crtControlOffsetUnaryCost (W i) (S i) +
          (10 * cw + 9) * T n * p n) := by
        apply Finset.sum_le_sum
        intro i _
        exact (crtControlAllFibersCost_decompose (D := D i) (W := W i) (w := w i)
          (S := S i) (k := k i) (ha i)).trans (Nat.add_le_add_left (hk' i) _)
      _ = _ := by simp [Finset.sum_add_distrib]
  norm_num at hp ⊢
  nlinarith

/-- Exact bank initialization and disposal overhead around `crtControlAllCost`.
This is the additional budget in `crtControlAllWorkspace_runs`. -/
def crtControlWorkspaceOverhead (W w : ℕ) : ℕ :=
  (10 * (4 * W + 4) + 1 + 10 * tblC W w) + (10 * (2 * W + 2) + 1)

/-- The optional width setup and disposal budget, charged once per pass. -/
def crtControlWidthsOverhead (L : ℕ) : ℕ := (12 * L + 14) + (6 * L + 8)

/-- Workspace and width provisioning fit one fixed multiple of the volume
in coefficient symbols. Descriptor generation is not part of this overhead. -/
theorem crtControl_workspace_overhead {W w L p : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) (hL : L ≤ p) (hp : 1 ≤ p) :
    crtControlWorkspaceOverhead W w + crtControlWidthsOverhead L ≤ 2 ^ 16 * 2 ^ L * p := by
  have hvol : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hLvol : L ≤ 2 ^ L := Nat.lt_two_pow_self.le
  have hleft : L + 1 ≤ 2 * 2 ^ L := by omega
  have hright : L + 1 ≤ 2 * p := by omega
  have hsq := Nat.mul_le_mul hleft hright
  have hwidth : W + 4 ≤ 5 * (L + 1) := by omega
  have hpow := Nat.pow_le_pow_left hwidth 2
  have hpvol : p ≤ 2 ^ L * p := Nat.le_mul_of_pos_left _ hvol
  unfold crtControlWorkspaceOverhead crtControlWidthsOverhead tblC
  norm_num
  nlinarith

/-- Summed provisioning overhead for any runtime number of axes. -/
theorem crtControl_workspace_overhead_total {q L p : ℕ} (W w : Fin q → ℕ)
    (hW : ∀ i, W i ≤ 3 * L + 1) (hw : ∀ i, w i ≤ W i)
    (hL : L ≤ p) (hp : 1 ≤ p) :
    (∑ i, (crtControlWorkspaceOverhead (W i) (w i) + crtControlWidthsOverhead L)) ≤
      2 ^ 16 * q * 2 ^ L * p := by
  calc
    _ ≤ ∑ _ : Fin q, 2 ^ 16 * 2 ^ L * p :=
      Finset.sum_le_sum fun i _ => crtControl_workspace_overhead (hW i) (hw i) hL hp
    _ = _ := by simp; ring

/-- Full concrete fiber passes with bank and width provisioning over every
axis. The power-of-two envelope includes all record widths `k ≤ cw*p`;
descriptor generation remains a separate charge. -/
theorem crtControlAllWorkspace_pipeline_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ a D W w S k : Fin (d n) → ℕ,
      (∀ i, a i ≤ logT n) → (∀ i, a i = ℓ n ∨ a i = ℓ n - 1) →
      (∀ i, D i ≤ logT n) → (∀ i, W i ≤ 3 * logT n + 1) →
      (∀ i, w i ≤ W i) → (∀ i, S i ≤ 2 ^ a i) → (∀ i, k i ≤ cw * p n) →
      (∑ i, (crtControlAllFibersCost (D i) (W i) (w i) (S i) (logT n) (a i) (k i) +
        crtControlWorkspaceOverhead (W i) (w i) + crtControlWidthsOverhead (logT n))) ≤
        2 ^ 21 * (cw + 1) * d n * T n * p n := by
  filter_upwards [crtControlAllFibersCost_pipeline_le cw, eventually_big]
    with n h hb a D W w S k ha hwidth hD hW hw hS hk
  have hc := h a D W w S k ha hwidth hD hW hw hS hk
  have hp : 1 ≤ p n := by have := hb.sixteen_le_b; unfold p; omega
  have hLp : logT n ≤ p n := by
    have := mt_logT_le_b hb
    unfold p
    omega
  have ho := crtControl_workspace_overhead_total W w hW hw hLp hp
  have hd : 1 ≤ d n := hb.one_le_d
  have hT : T n ≤ d n * T n * p n := by
    calc
      T n ≤ d n * T n := Nat.le_mul_of_pos_left _ hd
      _ ≤ d n * T n * p n := Nat.le_mul_of_pos_right _ hp
  have hsum : (∑ i, (crtControlAllFibersCost (D i) (W i) (w i) (S i) (logT n) (a i) (k i) +
      crtControlWorkspaceOverhead (W i) (w i) + crtControlWidthsOverhead (logT n))) =
      (∑ i, crtControlAllFibersCost (D i) (W i) (w i) (S i) (logT n) (a i) (k i)) +
      (∑ i, (crtControlWorkspaceOverhead (W i) (w i) + crtControlWidthsOverhead (logT n))) := by
    simp only [Finset.sum_add_distrib]
    omega
  rw [hsum]
  change _ ≤ 2 ^ 16 * d n * T n * p n at ho
  have hnonneg : 0 ≤ cw * (d n * T n * p n) := Nat.zero_le _
  norm_num at hc ho ⊢
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
