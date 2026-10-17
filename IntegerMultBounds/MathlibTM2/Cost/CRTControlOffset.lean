module

import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Cost.Total
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Charging unary CRT offsets separately

Materializing the two binary lengths costs `W*(4*S+22)+2*S+12`;
clearing the preserved counters after rotation costs another `2*S+4`.
Unlike the binary descriptor arithmetic, this is not polynomial in address
width alone. Its modulus factor cancels the missing axis volume: for `q`
axes the total is at most `2^7*q*2^L*(L+1)`. At pipeline parameters this is
at most `2^7*d*T*p`, within a linear number of full-volume passes on
coefficient-sized records, and hence also within the existing `totCRT` scale.

The binary offset kernel and the data rotation itself are separate charges.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter

/-- Materialize both counters, then clear them after their use by rotation. -/
def crtControlOffsetUnaryCost (W S : ℕ) : ℕ :=
  (W * (4 * S + 22) + 2 * S + 12) + (2 * S + 4)

/-- The modulus-sensitive unary charge is linear in the padded axis volume. -/
theorem crtControlOffsetUnaryCost_le {L W S a : ℕ}
    (hW : W ≤ 3 * L + 1) (hS : S ≤ 2 ^ a) :
    crtControlOffsetUnaryCost W S ≤ 2 ^ 7 * (L + 1) * 2 ^ a := by
  have hx : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h₁ : 4 * S + 22 ≤ 26 * 2 ^ a := by omega
  have h₂ := Nat.mul_le_mul_left W h₁
  have h₃ := Nat.mul_le_mul_right (2 ^ a) (show 26 * W + 20 ≤ 2 ^ 7 * (L + 1) by omega)
  unfold crtControlOffsetUnaryCost
  nlinarith

/-- Multiplying by the number of fibers cancels the padded axis volume. -/
theorem crtControlOffsetUnaryCost_fibers_le {L W S a : ℕ}
    (ha : a ≤ L) (hW : W ≤ 3 * L + 1) (hS : S ≤ 2 ^ a) :
    2 ^ (L - a) * crtControlOffsetUnaryCost W S ≤ 2 ^ 7 * 2 ^ L * (L + 1) := by
  calc
    2 ^ (L - a) * crtControlOffsetUnaryCost W S ≤
        2 ^ (L - a) * (2 ^ 7 * (L + 1) * 2 ^ a) :=
      Nat.mul_le_mul_left _ (crtControlOffsetUnaryCost_le hW hS)
    _ = 2 ^ 7 * (2 ^ (L - a) * 2 ^ a) * (L + 1) := by ring
    _ = 2 ^ 7 * 2 ^ L * (L + 1) := by rw [← pow_add, Nat.sub_add_cancel ha]

/-- All unary offset conversion and cleanup across `q` axes. No lower
bound on the axis widths or moduli is needed for this accounting lemma. -/
theorem crtControlOffsetUnaryCost_total_le {L q : ℕ} (a W S : Fin q → ℕ)
    (ha : ∀ i, a i ≤ L) (hW : ∀ i, W i ≤ 3 * L + 1)
    (hS : ∀ i, S i ≤ 2 ^ a i) :
    (∑ i, 2 ^ (L - a i) * crtControlOffsetUnaryCost (W i) (S i)) ≤
      2 ^ 7 * q * 2 ^ L * (L + 1) := by
  calc
    (∑ i, 2 ^ (L - a i) * crtControlOffsetUnaryCost (W i) (S i)) ≤
        ∑ _ : Fin q, 2 ^ 7 * 2 ^ L * (L + 1) :=
      Finset.sum_le_sum fun i _ => crtControlOffsetUnaryCost_fibers_le (ha i) (hW i) (hS i)
    _ = 2 ^ 7 * q * 2 ^ L * (L + 1) := by simp; ring

/-- At pipeline parameters the unary charge fits `d` full-volume passes of
`p`-symbol records, without using the quadratic interchange budget. -/
theorem crtControlOffsetUnaryCost_pipeline_le {n : ℕ} (h : Big n)
    (a W S : Fin (d n) → ℕ) (ha : ∀ i, a i ≤ logT n)
    (hW : ∀ i, W i ≤ 3 * logT n + 1) (hS : ∀ i, S i ≤ 2 ^ a i) :
    (∑ i, 2 ^ (logT n - a i) * crtControlOffsetUnaryCost (W i) (S i)) ≤
      2 ^ 7 * d n * T n * p n := by
  have hLp : logT n + 1 ≤ p n := by
    have := mt_logT_le_b h
    have := h.sixteen_le_b
    unfold p
    omega
  exact (crtControlOffsetUnaryCost_total_le a W S ha hW hS).trans
    (Nat.mul_le_mul_left (2 ^ 7 * d n * T n) hLp)

/-- Eventual form for use beside the descriptor arithmetic estimates. -/
theorem crtControlOffsetUnaryCost_eventually_le :
    ∀ᶠ n in atTop, ∀ a W S : Fin (d n) → ℕ,
      (∀ i, a i ≤ logT n) → (∀ i, W i ≤ 3 * logT n + 1) →
      (∀ i, S i ≤ 2 ^ a i) →
      (∑ i, 2 ^ (logT n - a i) * crtControlOffsetUnaryCost (W i) (S i)) ≤
        2 ^ 7 * d n * T n * p n := by
  filter_upwards [eventually_big] with n h a W S ha hW hS
  exact crtControlOffsetUnaryCost_pipeline_le h a W S ha hW hS

/-- Compatibility with the current total CRT scale, keeping the tighter
linear-pass bound available separately. -/
theorem crtControlOffsetUnaryCost_le_totCRT {n : ℕ} (h : Big n)
    (a W S : Fin (d n) → ℕ) (ha : ∀ i, a i ≤ logT n)
    (hW : ∀ i, W i ≤ 3 * logT n + 1) (hS : ∀ i, S i ≤ 2 ^ a i) :
    ((∑ i, 2 ^ (logT n - a i) * crtControlOffsetUnaryCost (W i) (S i)) : ℝ) ≤
      2 ^ 7 * totCRT n := by
  have hc : ((∑ i, 2 ^ (logT n - a i) * crtControlOffsetUnaryCost (W i) (S i)) : ℝ) ≤
      2 ^ 7 * (d n : ℝ) * T n * p n := by
    exact_mod_cast crtControlOffsetUnaryCost_pipeline_le h a W S ha hW hS
  have hd : (d n : ℝ) ≤ (d n : ℝ) ^ 2 := by
    have hd₁ : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hd (mt_Tp_nonneg n)
  have hrest : 0 ≤ (T n : ℝ) * p n * (d n : ℝ) ^ 2 * (ℓ n : ℝ) ^ Parameters.tau := by
    have := Real.rpow_nonneg (Nat.cast_nonneg (ℓ n)) Parameters.tau
    positivity
  rw [mt_crt_eq]
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
