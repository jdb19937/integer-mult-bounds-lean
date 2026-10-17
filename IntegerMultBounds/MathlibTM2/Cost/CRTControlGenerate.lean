module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlParameters
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # Cost of actual runtime CRT descriptor production

The unary input moduli cost at most one radix per entry. Even traversing all
entries for every target remains a polynomial times the radix, hence is
absorbed by the padded volume. This is separate from all-fiber data movement.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast TableVM

private theorem crtGenerate_tbl_le {W w L : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) :
    tblC W w ≤ 2 ^ 10 * (L + 1) ^ 2 := by
  have hwidth : W + 4 ≤ 5 * (L + 1) := by omega
  have hpow := Nat.pow_le_pow_left hwidth 2
  unfold tblC
  norm_num
  nlinarith

/-- Exact checked axis execution, including both entry streams and saved zero. -/
theorem crtControlGenerateAxisCost_le {W w a b e z L : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) (ha : a ≤ L)
    (he : e ≤ L) (hz : z ≤ 4 * W) :
    crtControlGenerateAxisCost W w a b e z ≤ 2 ^ 14 * (b + 1) * (L + 1) ^ 2 := by
  have ht := crtGenerate_tbl_le hW hw
  have hm := Nat.mul_le_mul_left (b + 8) ht
  have hsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hbsq : b ≤ b * (L + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold crtControlGenerateAxisCost
  norm_num at ht hm ⊢
  nlinarith

/-- Actual bank provisioning and unary-to-binary constants cost only a cubic. -/
theorem crtControlGenerateSetupCost_le {W w i ai a0 lower L : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) (hi : i ≤ L)
    (hai : ai ≤ L) (ha0 : a0 ≤ L) (hlower : lower ≤ L) :
    crtControlGenerateSetupCost W w i ai a0 lower ≤ 2 ^ 14 * (L + 1) ^ 3 := by
  have ht := crtGenerate_tbl_le hW hw
  have hm := Nat.mul_le_mul (show i + 3 ≤ L + 3 by omega) ht
  have hsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hc : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by nlinarith [Nat.zero_le (L * (L + 1) ^ 2)]
  unfold crtControlGenerateSetupCost
  norm_num at hm ⊢
  nlinarith

/-- All concrete axis operations for all target descriptor streams together
are eventually bounded by one padded data volume. The loop, setup and final
stream cleanup are separately charged. -/
theorem crtControlGenerateAxes_pipeline_le :
    ∀ᶠ n in atTop, ∀ W w : Fin (d n) → ℕ,
      ∀ a s e z : Fin (d n) → Fin (d n) → ℕ,
      (∀ i, W i ≤ 3 * logT n + 1) → (∀ i, w i ≤ W i) →
      (∀ i j, a i j ≤ logT n) → (∀ i j, s i j ≤ r n) →
      (∀ i j, e i j ≤ logT n) → (∀ i j, z i j ≤ 4 * W i) →
      (∑ i, ∑ j, crtControlGenerateAxisCost (W i) (w i) (a i j) (s i j) (e i j) (z i j)) ≤ T n := by
  filter_upwards [mt_poly_r_le_T (2 ^ 17) 4, eventually_big] with n hpoly hb W w a s e z hW hw ha hs he hz
  have hr : 1 ≤ r n := Nat.one_le_two_pow
  have hL : logT n + 1 ≤ 2 * b n := by have := mt_logT_le_b hb; have := hb.sixteen_le_b; omega
  have hd : d n ≤ b n := d_le_b n
  have hpoint : ∀ i j, crtControlGenerateAxisCost (W i) (w i) (a i j) (s i j) (e i j) (z i j) ≤
      2 ^ 17 * b n ^ 2 * r n := by
    intro i j
    have h := crtControlGenerateAxisCost_le (b := s i j) (hW i) (hw i) (ha i j) (he i j) (hz i j)
    have hs' : s i j + 1 ≤ 2 * r n := by have := hs i j; omega
    calc
      _ ≤ 2 ^ 14 * (s i j + 1) * (logT n + 1) ^ 2 := h
      _ ≤ 2 ^ 14 * (2 * r n) * (2 * b n) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hs') (Nat.pow_le_pow_left hL 2)
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin (d n), ∑ _ : Fin (d n), 2 ^ 17 * b n ^ 2 * r n :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    _ = d n ^ 2 * (2 ^ 17 * b n ^ 2 * r n) := by simp; ring
    _ ≤ b n ^ 2 * (2 ^ 17 * b n ^ 2 * r n) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd 2)
    _ = 2 ^ 17 * b n ^ 4 * r n := by ring
    _ ≤ T n := hpoly

/-- Provisioning every target's generator bank is also absorbed by one volume. -/
theorem crtControlGenerateSetup_pipeline_le :
    ∀ᶠ n in atTop, ∀ W w i ai a0 lower : Fin (d n) → ℕ,
      (∀ j, W j ≤ 3 * logT n + 1) → (∀ j, w j ≤ W j) →
      (∀ j, i j ≤ logT n) → (∀ j, ai j ≤ logT n) →
      (∀ j, a0 j ≤ logT n) → (∀ j, lower j ≤ logT n) →
      (∑ j, crtControlGenerateSetupCost (W j) (w j) (i j) (ai j) (a0 j) (lower j)) ≤ T n := by
  filter_upwards [mt_poly_r_le_T (2 ^ 17) 4, eventually_big] with n hpoly hb W w i ai a0 lower hW hw hi hai ha0 hlower
  have hr : 1 ≤ r n := Nat.one_le_two_pow
  have hL : logT n + 1 ≤ 2 * b n := by have := mt_logT_le_b hb; have := hb.sixteen_le_b; omega
  have hd : d n ≤ b n := d_le_b n
  have hpoint : ∀ j, crtControlGenerateSetupCost (W j) (w j) (i j) (ai j) (a0 j) (lower j) ≤
      2 ^ 17 * b n ^ 3 := by
    intro j
    calc
      _ ≤ 2 ^ 14 * (logT n + 1) ^ 3 :=
        crtControlGenerateSetupCost_le (hW j) (hw j) (hi j) (hai j) (ha0 j) (hlower j)
      _ ≤ 2 ^ 14 * (2 * b n) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 3)
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin (d n), 2 ^ 17 * b n ^ 3 := Finset.sum_le_sum fun j _ => hpoint j
    _ = d n * (2 ^ 17 * b n ^ 3) := by simp
    _ ≤ b n * (2 ^ 17 * b n ^ 3) := Nat.mul_le_mul_right _ hd
    _ = 2 ^ 17 * b n ^ 4 := by ring
    _ ≤ 2 ^ 17 * b n ^ 4 * r n := Nat.le_mul_of_pos_right _ hr
    _ ≤ T n := hpoly

/-- A preserved unary source is encoded with a restored arithmetic bank. -/
theorem crtControlUnaryWordCost_le {W w n L : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) :
    crtControlUnaryWordCost W w n ≤ 2 ^ 14 * (n + 1) * (L + 1) ^ 2 := by
  have ht := crtGenerate_tbl_le hW hw
  have hm := Nat.mul_le_mul_left (n + 3) ht
  have hsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hnsq : n ≤ n * (L + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold crtControlUnaryWordCost
  norm_num at ht hm ⊢
  nlinarith

/-- Both permanent words, unary padding and fiber-address width, followed by
clearing those four outputs after the preserved-input rotation. -/
def crtControlParametersCost (W w S μ a L : ℕ) : ℕ :=
  crtControlParametersSetupCost W w S μ a L +
    (4 * W + 2 * (2 ^ a - S) + 2 * (L - a) + 8)

/-- Parameter preparation has only radix times polynomial cost per target. -/
theorem crtControlParametersCost_le {W w S μ a L radix : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) (ha : a ≤ L)
    (hS : S ≤ radix) (hμ : μ ≤ radix) (hr : 2 ^ a ≤ radix) :
    crtControlParametersCost W w S μ a L ≤ 2 ^ 17 * radix * (L + 1) ^ 2 := by
  have hs := crtControlUnaryWordCost_le (n := S) hW hw
  have hm := crtControlUnaryWordCost_le (n := μ) hW hw
  have hrad : 1 ≤ radix := Nat.one_le_two_pow.trans hr
  have hs' := Nat.mul_le_mul_right ((L + 1) ^ 2) (Nat.mul_le_mul_left (2 ^ 14) (show S + 1 ≤ 2 * radix by omega))
  have hm' := Nat.mul_le_mul_right ((L + 1) ^ 2) (Nat.mul_le_mul_left (2 ^ 14) (show μ + 1 ≤ 2 * radix by omega))
  have hsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hrl : (L + 1) ^ 2 ≤ radix * (L + 1) ^ 2 := Nat.le_mul_of_pos_left _ hrad
  have hrr : radix ≤ radix * (L + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hsub : 2 ^ a - S ≤ 2 ^ a := Nat.sub_le _ _
  have hsub' : L - a ≤ L := Nat.sub_le _ _
  unfold crtControlParametersCost crtControlParametersSetupCost
  norm_num at hs hm hs' hm' ⊢
  nlinarith

/-- The complete parameter budget for all targets is eventually below one
padded volume. Each constituent is the actual checked program's step budget. -/
theorem crtControlParameters_pipeline_le :
    ∀ᶠ n in atTop, ∀ W w S μ a : Fin (d n) → ℕ,
      (∀ j, W j ≤ 3 * logT n + 1) → (∀ j, w j ≤ W j) →
      (∀ j, a j ≤ logT n) → (∀ j, S j ≤ r n) →
      (∀ j, μ j ≤ r n) → (∀ j, 2 ^ a j ≤ r n) →
      (∑ j, crtControlParametersCost (W j) (w j) (S j) (μ j) (a j) (logT n)) ≤ T n := by
  filter_upwards [mt_poly_r_le_T (2 ^ 19) 3, eventually_big] with n hpoly hb W w S μ a hW hw ha hS hμ hr
  have hL : logT n + 1 ≤ 2 * b n := by have := mt_logT_le_b hb; have := hb.sixteen_le_b; omega
  have hd : d n ≤ b n := d_le_b n
  have hpoint : ∀ j, crtControlParametersCost (W j) (w j) (S j) (μ j) (a j) (logT n) ≤
      2 ^ 19 * b n ^ 2 * r n := by
    intro j
    calc
      _ ≤ 2 ^ 17 * r n * (logT n + 1) ^ 2 :=
        crtControlParametersCost_le (hW j) (hw j) (ha j) (hS j) (hμ j) (hr j)
      _ ≤ 2 ^ 17 * r n * (2 * b n) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 2)
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin (d n), 2 ^ 19 * b n ^ 2 * r n := Finset.sum_le_sum fun j _ => hpoint j
    _ = d n * (2 ^ 19 * b n ^ 2 * r n) := by simp
    _ ≤ b n * (2 ^ 19 * b n ^ 2 * r n) := Nat.mul_le_mul_right _ hd
    _ = 2 ^ 19 * b n ^ 3 * r n := by ring
    _ ≤ T n := hpoly

end IntegerMultBounds.MathlibTM2.Cost
