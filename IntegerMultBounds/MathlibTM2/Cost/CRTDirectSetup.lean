module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectSetup
public import IntegerMultBounds.MathlibTM2.Cost.MatchBase

/-! # Actual setup and cleanup cost for the direct CRT driver -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast

/-- Exact legacy stream lengths, including the two separators per entry. -/
theorem crtDirectSetupStream_length {d A : ℕ} (a : Fin d → ℕ) :
    (crtEnts (A := A) ((crtRevAx d).map a)).length = (∑ j, a j) + 2 * d := by
  have h := congrArg List.length (crtDirectReverseEntries (A := A) a)
  simpa only [List.length_reverse, crtDirectEntriesLength, List.sum_ofFn, List.length_ofFn] using h

/-- The complete six-output disposal budget includes both immutable copies,
the cached zero width, encoded record width, dimension count, and bank width. -/
theorem crtDirectSetupClearBound_le {d L radix : ℕ} (a s : Fin (d + 1) → ℕ) (c : ℕ)
    (ha : (∑ j, a j) ≤ L) (hd : d + 1 ≤ L) (hs : ∀ j, s j ≤ radix) :
    crtDirectSetupClearBound a s c ≤ 10 * L + L * radix + 3 * c + 1 := by
  have ha0 : a 0 ≤ L :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)).trans ha
  have hp : crtPre a (d + 1) ≤ L :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans ha
  have hsum : (∑ j, s j) ≤ (d + 1) * radix := by
    calc
      _ ≤ ∑ _ : Fin (d + 1), radix := Finset.sum_le_sum fun j _ => hs j
      _ = _ := by simp
  have hprod := Nat.mul_le_mul_right radix hd
  have henc := crt_advance_length (3 * c)
  unfold crtDirectSetupClearBound
  rw [List.sum_ofFn, List.sum_ofFn]
  omega

/-- Match the exact checked setup and cleanup budgets to a single quadratic
in scalar widths, times the maximum unary radix. -/
theorem crtDirectSetup_totalCost_le {d A L radix : ℕ} (a s : Fin (d + 1) → ℕ) (c : ℕ)
    (ha : (∑ j, a j) ≤ L) (hd : d + 1 ≤ L) (hs : ∀ j, s j ≤ radix) (hr : 1 ≤ radix) :
    crtDirectSetupCost (crtEnts (A := A) ((crtRevAx (d + 1)).map a)).length
      (crtEnts (A := A) ((crtRevAx (d + 1)).map s)).length (a 0) (crtPre a (d + 1)) c +
      crtDirectSetupClearCost a s c ≤ 2 ^ 10 * radix * (L + c + 1) ^ 2 := by
  have ha0 : a 0 ≤ L :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)).trans ha
  have hp : crtPre a (d + 1) ≤ L :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans ha
  have hsum : (∑ j, s j) ≤ (d + 1) * radix := by
    calc
      _ ≤ ∑ _ : Fin (d + 1), radix := Finset.sum_le_sum fun j _ => hs j
      _ = _ := by simp
  have hprod := Nat.mul_le_mul_right radix hd
  have hclear := crtDirectSetupClearBound_le a s c ha hd hs
  have hq : L + c + 1 ≤ (L + c + 1) ^ 2 := by nlinarith
  have hc2 : c ^ 2 ≤ (L + c + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hradq : (L + c + 1) ^ 2 ≤ radix * (L + c + 1) ^ 2 := Nat.le_mul_of_pos_left _ hr
  have hradL : L * radix ≤ radix * (L + c + 1) ^ 2 := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left radix (show L ≤ (L + c + 1) ^ 2 by omega)
  rw [crtDirectSetupStream_length, crtDirectSetupStream_length]
  unfold crtDirectSetupCost crtDirectTripleCost crtDirectSetupClearCost
  norm_num
  nlinarith

/-- Complete actual setup plus six-output cleanup is absorbed by one padded
volume eventually, including reading unary modulus entries and encoding `3c`. -/
theorem crtDirectSetup_pipeline_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ m A c : ℕ, ∀ a s : Fin (m + 1) → ℕ,
      (∑ j, a j) ≤ logT n → m + 1 ≤ logT n → (∀ j, s j ≤ r n) → c ≤ cw * p n →
      crtDirectSetupCost (crtEnts (A := A) ((crtRevAx (m + 1)).map a)).length
        (crtEnts (A := A) ((crtRevAx (m + 1)).map s)).length (a 0) (crtPre a (m + 1)) c +
        crtDirectSetupClearCost a s c ≤ T n := by
  filter_upwards [mt_poly_r_le_T (2 ^ 16 * (cw + 1) ^ 2) 2, eventually_big]
    with n hpoly hb m A c a s ha hd hs hc
  have hL := mt_logT_le_b hb
  have hb1 : 1 ≤ b n := by have := hb.sixteen_le_b; omega
  have hsize : logT n + c + 1 ≤ 8 * (cw + 1) * b n := by
    unfold p at hc
    nlinarith
  calc
    _ ≤ 2 ^ 10 * r n * (logT n + c + 1) ^ 2 :=
      crtDirectSetup_totalCost_le a s c ha hd hs Nat.one_le_two_pow
    _ ≤ 2 ^ 10 * r n * (8 * (cw + 1) * b n) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
    _ = (2 ^ 16 * (cw + 1) ^ 2) * b n ^ 2 * r n := by ring
    _ ≤ T n := hpoly

end IntegerMultBounds.MathlibTM2.Cost
