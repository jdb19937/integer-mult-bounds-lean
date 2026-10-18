module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modular reduction without long division

The machine reduces modulo the prime `p` with multiplications, shifts and additions only, so each
reduction costs a constant number of products of `O(log p)`-bit numbers.

**Montgomery reduction.** For a radix `R` and `p'` with `R ∣ p p' + 1`, `redc p R p' t` is
`(t + m p) / R` for the digit `m = (t mod R) p' mod R`, minus `p` if it is not below `p`.
`redc_dvd`: the division is exact. For `t < p R`, `redc_lt`: the value is below `p`, and
`redc_cast`: it is `t R⁻¹` in `ZMod p`.

**The inverse modulo a power of two.** `henselStep p k y = y (2 + (p mod 2 ^ (2k)) y) mod 2 ^ (2k)`
lifts `2 ^ k ∣ p y + 1` to `2 ^ (2k) ∣ p y' + 1` (`henselStep_dvd`), because
`p y (2 + p y) + 1 = (p y + 1) ^ 2`. From `y = 1` (`p` odd), `i` steps give
`2 ^ (2 ^ i) ∣ p (henselInv p i) + 1` (`henselInv_dvd`), and reducing modulo `R = 2 ^ r` for
`r ≤ 2 ^ i` gives the Montgomery constant (`montInv_dvd`).

**Barrett reduction.** With `μ = ⌊4 ^ w / p⌋` and `x < 4 ^ w`, the quotient `q = ⌊x μ / 4 ^ w⌋`
satisfies `q p ≤ x < q p + 2 p` (`barrett_le`, `barrett_lt`), so `x mod p` is `x - q p` after at
most one subtraction of `p` (`barrett_mod`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.DFT

/-! ### Montgomery reduction -/

/-- The Montgomery digit `(t mod R) p' mod R`. -/
def redcDigit (R p' t : ℕ) : ℕ := t % R * p' % R

/-- `(t + m p) / R` for the Montgomery digit `m`. -/
def redcRaw (p R p' t : ℕ) : ℕ := (t + redcDigit R p' t * p) / R

/-- Montgomery's REDC: `t R⁻¹ mod p` for `t < p R`. -/
def redc (p R p' t : ℕ) : ℕ :=
  if redcRaw p R p' t < p then redcRaw p R p' t else redcRaw p R p' t - p

/-- The Montgomery digit makes `t + m p` a multiple of `R`. -/
theorem redc_dvd (p R p' t : ℕ) (hp' : R ∣ p * p' + 1) : R ∣ t + redcDigit R p' t * p := by
  rw [← ZMod.natCast_eq_zero_iff] at hp' ⊢
  simp only [redcDigit, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at hp' ⊢
  linear_combination (t : ZMod R) * hp'

theorem redcRaw_lt (p R p' t : ℕ) (hR : 0 < R) (ht : t < p * R) : redcRaw p R p' t < 2 * p := by
  have hm : redcDigit R p' t < R := Nat.mod_lt _ hR
  unfold redcRaw
  rw [Nat.div_lt_iff_lt_mul hR]
  calc t + redcDigit R p' t * p < p * R + R * p :=
        Nat.add_lt_add_of_lt_of_le ht (Nat.mul_le_mul_right p hm.le)
    _ = 2 * p * R := by ring

theorem redcRaw_cast (p R p' t : ℕ) (hp' : R ∣ p * p' + 1) :
    (redcRaw p R p' t : ZMod p) * R = t := by
  rw [redcRaw, ← Nat.cast_mul, Nat.div_mul_cancel (redc_dvd p R p' t hp')]
  simp

theorem redc_lt (p R p' t : ℕ) (hR : 0 < R) (ht : t < p * R) : redc p R p' t < p := by
  have := redcRaw_lt p R p' t hR ht
  unfold redc
  split_ifs <;> omega

/-- REDC divides by `R` in `ZMod p`. -/
theorem redc_cast (p R p' t : ℕ) (hp' : R ∣ p * p' + 1) : (redc p R p' t : ZMod p) * R = t := by
  unfold redc
  split_ifs with h
  · exact redcRaw_cast p R p' t hp'
  · rw [Nat.cast_sub (by omega), ZMod.natCast_self, sub_zero]
    exact redcRaw_cast p R p' t hp'

/-! ### The inverse modulo a power of two -/

/-- One Hensel step for `-p⁻¹` modulo `2 ^ (2 k)`. -/
def henselStep (p k y : ℕ) : ℕ := y * (2 + p % 2 ^ (2 * k) * y) % 2 ^ (2 * k)

theorem henselStep_dvd (p k y : ℕ) (h : 2 ^ k ∣ p * y + 1) :
    2 ^ (2 * k) ∣ p * henselStep p k y + 1 := by
  have hsq : 2 ^ (2 * k) ∣ (p * y + 1) ^ 2 := by
    rw [show 2 ^ (2 * k) = (2 ^ k) ^ 2 by ring]
    exact pow_dvd_pow_of_dvd h 2
  rw [← ZMod.natCast_eq_zero_iff] at hsq ⊢
  simp only [henselStep, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod,
    Nat.cast_one, Nat.cast_ofNat] at hsq ⊢
  linear_combination hsq

/-- `i` Hensel steps from `1`. -/
def henselInv (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => henselStep p (2 ^ i) (henselInv p i)

theorem henselInv_dvd (p : ℕ) (hp : 2 ∣ p + 1) (i : ℕ) : 2 ^ 2 ^ i ∣ p * henselInv p i + 1 := by
  induction i with
  | zero => simpa [henselInv] using hp
  | succ i ih =>
    show 2 ^ 2 ^ (i + 1) ∣ p * henselStep p (2 ^ i) (henselInv p i) + 1
    rw [pow_succ, mul_comm (2 ^ i) 2]
    exact henselStep_dvd p (2 ^ i) _ ih

/-- The Montgomery constant for `R = 2 ^ r`. -/
theorem montInv_dvd (p r i : ℕ) (hp : 2 ∣ p + 1) (hr : r ≤ 2 ^ i) :
    2 ^ r ∣ p * (henselInv p i % 2 ^ r) + 1 := by
  have h := (pow_dvd_pow 2 hr).trans (henselInv_dvd p hp i)
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at h ⊢
  exact h

/-! ### Barrett reduction -/

/-- The Barrett quotient never exceeds the true quotient. -/
theorem barrett_le (p w x : ℕ) : x * (4 ^ w / p) / 4 ^ w * p ≤ x := by
  have hR : 0 < 4 ^ w := by positivity
  have hq : x * (4 ^ w / p) / 4 ^ w * 4 ^ w ≤ x * (4 ^ w / p) := Nat.div_mul_le_self _ _
  have hμ : 4 ^ w / p * p ≤ 4 ^ w := Nat.div_mul_le_self _ _
  generalize 4 ^ w / p = μ at hq hμ ⊢
  generalize x * μ / 4 ^ w = q at hq ⊢
  generalize 4 ^ w = R at hR hq hμ
  refine Nat.le_of_mul_le_mul_right ?_ hR
  calc q * p * R = q * R * p := by ring
    _ ≤ x * μ * p := Nat.mul_le_mul_right _ hq
    _ = x * (μ * p) := by ring
    _ ≤ x * R := Nat.mul_le_mul_left _ hμ

/-- The Barrett remainder is below `2 p`. -/
theorem barrett_lt (p w x : ℕ) (hp : 0 < p) (hx : x < 4 ^ w) :
    x < x * (4 ^ w / p) / 4 ^ w * p + 2 * p := by
  have hR : 0 < 4 ^ w := by positivity
  have hμ : 4 ^ w < 4 ^ w / p * p + p := Nat.lt_div_mul_add hp
  have hq : x * (4 ^ w / p) < x * (4 ^ w / p) / 4 ^ w * 4 ^ w + 4 ^ w := Nat.lt_div_mul_add hR
  generalize 4 ^ w / p = μ at hμ hq ⊢
  generalize x * μ / 4 ^ w = q at hq ⊢
  generalize 4 ^ w = R at hR hx hμ hq
  refine Nat.lt_of_mul_lt_mul_right (a := R) ?_
  calc x * R ≤ x * (μ * p + p) := Nat.mul_le_mul_left _ hμ.le
    _ = x * μ * p + x * p := by ring
    _ ≤ (q * R + R) * p + x * p := Nat.add_le_add_right (Nat.mul_le_mul_right _ hq.le) _
    _ < (q * R + R) * p + R * p := Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hx hp) _
    _ = (q * p + 2 * p) * R := by ring

/-- Barrett reduction: `x mod p` from the estimated quotient and one conditional subtraction. -/
theorem barrett_mod (p w x : ℕ) (hp : 0 < p) (hx : x < 4 ^ w) :
    x % p = if x - x * (4 ^ w / p) / 4 ^ w * p < p then x - x * (4 ^ w / p) / 4 ^ w * p
      else x - x * (4 ^ w / p) / 4 ^ w * p - p := by
  have hle := barrett_le p w x
  have hlt := barrett_lt p w x hp hx
  generalize x * (4 ^ w / p) / 4 ^ w = q at hle hlt ⊢
  obtain ⟨r, rfl⟩ : ∃ r, x = r + q * p := ⟨x - q * p, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_mul_mod_self_right]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (show r ≥ p by omega), Nat.mod_eq_of_lt (show r - p < p by omega)]

end IntegerMultBounds.MathlibTM2.DFT
