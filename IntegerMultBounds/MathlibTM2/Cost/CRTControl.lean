module

import IntegerMultBounds.MathlibTM2.Cost.MatchSynPipe
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Absorbing polynomial CRT control arithmetic

These bounds count a polynomial arithmetic budget once per fiber. They do not
assert a running-time bound for a CRT scanner or its tape implementation.
For an axis of width `ℓ` or `ℓ - 1`, its `2^(L-a)` fibers absorb any fixed
polynomial in the total address width `L ≤ b`. Even summing over at most `b`
axes is eventually linear in the padded volume.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter

/-- The number of fibers times `2^ℓ` is at most twice the box volume.
The upper bound on the axis width is essential because natural subtraction
would otherwise truncate. -/
theorem crtControl_fibers_mul_radix_le {L a ℓ : ℕ}
    (ha : a ≤ L) (hwidth : a = ℓ ∨ a = ℓ - 1) :
    2 ^ (L - a) * 2 ^ ℓ ≤ 2 * 2 ^ L := by
  have hℓ : ℓ ≤ a + 1 := by rcases hwidth with h | h <;> omega
  calc
    2 ^ (L - a) * 2 ^ ℓ = 2 ^ (L - a + ℓ) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 * 2 ^ L := by rw [pow_succ]; omega

/-- A per-fiber budget bounded by a constant times the radix costs at most
that constant times twice the volume. -/
theorem crtControl_fiber_cost_le {L a ℓ C cost : ℕ}
    (ha : a ≤ L) (hwidth : a = ℓ ∨ a = ℓ - 1)
    (hcost : cost ≤ C * 2 ^ ℓ) :
    2 ^ (L - a) * cost ≤ 2 * C * 2 ^ L := by
  calc
    2 ^ (L - a) * cost ≤ 2 ^ (L - a) * (C * 2 ^ ℓ) :=
      Nat.mul_le_mul_left _ hcost
    _ = C * (2 ^ (L - a) * 2 ^ ℓ) := by ring
    _ ≤ C * (2 * 2 ^ L) := Nat.mul_le_mul_left _ (crtControl_fibers_mul_radix_le ha hwidth)
    _ = 2 * C * 2 ^ L := by ring

/-- Any fixed polynomial budget in the address width is absorbed by the
radix eventually, uniformly over all address widths at most `b n`. -/
theorem crtControl_polynomial_le_radix (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ L : ℕ, L ≤ b n →
      A * (L + 1) ^ k ≤ (A * 2 ^ k) * r n := by
  filter_upwards [mr_b_pow_le_r k, eventually_big] with n hr hb L hL
  have hwidth : L + 1 ≤ 2 * b n := by have := hb.sixteen_le_b; omega
  calc
    A * (L + 1) ^ k ≤ A * (2 * b n) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth k)
    _ = (A * 2 ^ k) * b n ^ k := by rw [mul_pow]; ring
    _ ≤ (A * 2 ^ k) * r n := Nat.mul_le_mul_left _ hr

/-- Polynomial arithmetic once per fiber is eventually linear in volume,
uniformly over the two allowed axis widths and the polynomial's budget. -/
theorem crtControl_polynomial_fiber_le (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ L a cost : ℕ, L ≤ b n → a ≤ L →
      (a = ℓ n ∨ a = ℓ n - 1) → cost ≤ A * (L + 1) ^ k →
      2 ^ (L - a) * cost ≤ 2 * (A * 2 ^ k) * 2 ^ L := by
  filter_upwards [crtControl_polynomial_le_radix A k] with n h L a cost hL ha hw hc
  exact crtControl_fiber_cost_le ha hw (hc.trans (h L hL))

/-- A polynomial budget summed over at most `b` axes is still absorbed by
the radix; the additional factor uses one additional power in the growth lemma. -/
theorem crtControl_axes_polynomial_le_radix (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ L q : ℕ, L ≤ b n → q ≤ b n →
      q * (A * (L + 1) ^ k) ≤ (A * 2 ^ k) * r n := by
  filter_upwards [mr_b_pow_le_r (k + 1), eventually_big] with n hr hb L q hL hq
  have hwidth : L + 1 ≤ 2 * b n := by have := hb.sixteen_le_b; omega
  calc
    q * (A * (L + 1) ^ k) ≤ b n * (A * (2 * b n) ^ k) :=
      Nat.mul_le_mul hq (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth k))
    _ = (A * 2 ^ k) * b n ^ (k + 1) := by rw [mul_pow, pow_succ]; ring
    _ ≤ (A * 2 ^ k) * r n := Nat.mul_le_mul_left _ hr

/-- Total arithmetic over all fibers of at most `b` axes is eventually linear
in volume. The hypothesis is an arithmetic budget, not a machine-step contract. -/
theorem crtControl_polynomial_total_le (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ L q : ℕ, ∀ a cost : Fin q → ℕ,
      L ≤ b n → q ≤ b n → (∀ i, a i ≤ L) →
      (∀ i, a i = ℓ n ∨ a i = ℓ n - 1) →
      (∀ i, cost i ≤ A * (L + 1) ^ k) →
      (∑ i, 2 ^ (L - a i) * cost i) ≤ 2 * (A * 2 ^ k) * 2 ^ L := by
  filter_upwards [crtControl_axes_polynomial_le_radix A k] with n h L q a cost hL hq ha hw hc
  have hr := h L q hL hq
  have hradix : 0 < r n := by unfold r; positivity
  have hsum : (∑ i, 2 ^ (L - a i) * cost i) * r n ≤
      (q * (A * (L + 1) ^ k)) * (2 * 2 ^ L) := by
    rw [Finset.sum_mul]
    calc
      (∑ i, 2 ^ (L - a i) * cost i * r n) ≤
          ∑ i : Fin q, (A * (L + 1) ^ k) * (2 * 2 ^ L) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          2 ^ (L - a i) * cost i * r n = cost i * (2 ^ (L - a i) * r n) := by ring
          _ ≤ (A * (L + 1) ^ k) * (2 * 2 ^ L) :=
            Nat.mul_le_mul (hc i) (crtControl_fibers_mul_radix_le (ha i) (hw i))
      _ = (q * (A * (L + 1) ^ k)) * (2 * 2 ^ L) := by simp; ring
  have hbound := hsum.trans (Nat.mul_le_mul_right (2 * 2 ^ L) hr)
  have heq : (A * 2 ^ k * r n) * (2 * 2 ^ L) =
      (2 * (A * 2 ^ k) * 2 ^ L) * r n := by ring
  rw [heq] at hbound
  exact le_of_mul_le_mul_right hbound hradix

/-- Pipeline specialization: polynomial arithmetic on every fiber of all
`d n` axes costs at most a fixed multiple of the padded volume `T n`.
The machine must separately supply the per-fiber arithmetic budget. -/
theorem crtControl_polynomial_pipeline_le (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ a cost : Fin (d n) → ℕ,
      (∀ i, a i ≤ logT n) →
      (∀ i, a i = ℓ n ∨ a i = ℓ n - 1) →
      (∀ i, cost i ≤ A * (logT n + 1) ^ k) →
      (∑ i, 2 ^ (logT n - a i) * cost i) ≤ 2 * (A * 2 ^ k) * T n := by
  filter_upwards [crtControl_polynomial_total_le A k, eventually_big] with n h hb a cost ha hw hc
  have hd : d n ≤ b n := d_le_b n
  exact h (logT n) (d n) a cost (mt_logT_le_b hb) hd ha hw hc

end IntegerMultBounds.MathlibTM2.Cost
