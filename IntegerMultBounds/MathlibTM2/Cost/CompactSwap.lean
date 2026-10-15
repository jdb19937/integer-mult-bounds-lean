module

public import IntegerMultBounds.MathlibTM2.Node.CompactSwap

/-!
# Volume bounds for the prepared compact interchange

Normalize the actual `compactSwap_exec` budget. The bank-size and width hypotheses
remain explicit: constructing the headers and proving the compact node layout
are separate obligations. This does not claim a compact slot-XOR or layer bound.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host

/-- Fixed coefficient after charging prepared bank contents to record volume. -/
noncomputable def compactSwapCoeff (T t₀ D : ℕ) : ℝ :=
  3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) +
    (6 * D + 34 + 2 * T + 6 * swapT t₀ + 23 : ℕ)

/-- The prepared interchange is linear in its full payload volume, with the
sublinear exponent applied only to an upper bound on the compact field width. -/
theorem compactSwapCost_le_volume (T t₀ V h H D w : ℕ)
    (hV : 1 ≤ V) (hH : H ≤ D * V) (hw : h ≤ w) (hw₁ : 1 ≤ w) :
    compactSwapCost T t₀ V h H ≤
      compactSwapCoeff T t₀ D * V * ((w : ℝ) ^ Parameters.tau + 1) := by
  have hτ : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]
  have hwidth : ((max 1 h : ℕ) : ℝ) ≤ w := by exact_mod_cast max_le hw₁ hw
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg (max 1 h)) hwidth hτ
  have hC : 0 ≤ 3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) := by
    have := swapConst_pos
    positivity
  have hmain := mul_le_mul_of_nonneg_left hp
    (mul_nonneg hC (Nat.cast_nonneg V))
  have hlin : 6 * H + 34 * V + 2 * T + 6 * swapT t₀ + 23 ≤
      (6 * D + 34 + 2 * T + 6 * swapT t₀ + 23) * V := by
    have hf := Nat.mul_le_mul_left (2 * T + 6 * swapT t₀ + 23) hV
    nlinarith
  have hlinR : ((6 * H + 34 * V + 2 * T + 6 * swapT t₀ + 23 : ℕ) : ℝ) ≤
      ((6 * D + 34 + 2 * T + 6 * swapT t₀ + 23 : ℕ) : ℝ) * V := by
    exact_mod_cast hlin
  have hp₀ : 0 ≤ (w : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg w) _
  unfold compactSwapCost compactSwapCoeff
  nlinarith [mul_nonneg
    (mul_nonneg (Nat.cast_nonneg (6 * D + 34 + 2 * T + 6 * swapT t₀ + 23))
      (Nat.cast_nonneg V)) hp₀, mul_nonneg hC (Nat.cast_nonneg V)]

end IntegerMultBounds.MathlibTM2.Cost
