module

public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The reciprocal by Newton iteration

For a divisor `d` of `2 k` bits (`2 ^ (2k-1) ≤ d < 2 ^ (2k)`) and `a = ⌊4 ^ k / ⌊d / 2 ^ k⌋⌋`, the
reciprocal of its top `k` bits at half the precision, the Newton step
`y = 2 ^ (k+1) a - (⌊d a² / 4 ^ k⌋ + 1)` satisfies `y d < 16 ^ k < (y + 9) d`
(`newton_step`): the exact reciprocal `⌊16 ^ k / d⌋` is `y` plus at most `8` corrections. With
`X = 2 ^ k`, `4 ^ k = X ²`, `16 ^ k = X ⁴` and `X ² (X ⁴ - y d)` lies between `(X ³ - a d)²` and
`(X ³ - a d)² + d X ²`, while `-2 X ² < X ³ - a d < X ²`.

`barrett2_le`, `barrett2_lt`: Barrett reduction with `μ = ⌊2 ^ s / p⌋` and `x < 2 ^ s`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The Newton guess for `⌊16 ^ k / d⌋` from `a`. -/
def newtonGuess (k d a : ℕ) : ℕ := 2 ^ (k + 1) * a - (d * a ^ 2 / 4 ^ k + 1)

section Ints

variable {X dh ℓ a z : ℤ}

/-- `u = X ³ - a d` lies in `(-2 X ², X ²)`, for `d = dh X + ℓ`. -/
theorem newton_u (hX : 2 ≤ X) (hℓ0 : 0 ≤ ℓ) (hℓX : ℓ < X) (hdhX : dh < X)
    (ha1 : a * dh ≤ X * X) (ha2 : X * X < (a + 1) * dh) (hale : a ≤ 2 * X) :
    -(2 * (X * X)) < X * X * X - a * (dh * X + ℓ) ∧ X * X * X - a * (dh * X + ℓ) < X * X := by
  have hX0 : (0 : ℤ) < X := by linarith
  have e : a * (dh * X + ℓ) = a * dh * X + a * ℓ := by ring
  have h1 : a * dh * X ≤ X * X * X := mul_le_mul_of_nonneg_right ha1 hX0.le
  have h2 : a * ℓ < 2 * X * X :=
    calc a * ℓ ≤ 2 * X * ℓ := mul_le_mul_of_nonneg_right hale hℓ0
      _ < 2 * X * X := mul_lt_mul_of_pos_left hℓX (by linarith)
  have h3 : X * X * X < (a + 1) * dh * X := mul_lt_mul_of_pos_right ha2 hX0
  have h4 : dh * X < X * X := mul_lt_mul_of_pos_right hdhX hX0
  have h5 : 0 ≤ a * ℓ := mul_nonneg (by nlinarith) hℓ0
  have e2 : (a + 1) * dh * X = a * dh * X + dh * X := by ring
  constructor <;> nlinarith

/-- The subtraction in the Newton guess does not truncate. -/
theorem newton_iii (hX : 2 ≤ X) (hage : X ≤ a)
    (hu : -(2 * (X * X)) < X * X * X - a * (dh * X + ℓ))
    (hz1 : z * (X * X) ≤ (dh * X + ℓ) * a ^ 2) : z + 1 ≤ 2 * X * a := by
  have hXX : (0 : ℤ) < X * X := by nlinarith
  have ia0 : (0 : ℤ) < a := by linarith
  have h1 : a * (dh * X + ℓ) < X * X * X + 2 * (X * X) := by linarith
  have h2 : (dh * X + ℓ) * a ^ 2 < a * (X + 2) * (X * X) := by
    have := mul_lt_mul_of_pos_left h1 ia0
    have e1 : (dh * X + ℓ) * a ^ 2 = a * (a * (dh * X + ℓ)) := by ring
    have e2 : a * (X + 2) * (X * X) = a * (X * X * X + 2 * (X * X)) := by ring
    rw [e1, e2]; exact this
  have h3 : z * (X * X) < a * (X + 2) * (X * X) := lt_of_le_of_lt hz1 h2
  have h4 : z < a * (X + 2) := lt_of_mul_lt_mul_right h3 hXX.le
  have h5 : a * (X + 2) ≤ 2 * X * a := by nlinarith
  linarith

/-- The identity behind both bounds. -/
theorem newton_id (d : ℤ) :
    X * X * (X * X * (X * X) - (2 * X * a - (z + 1)) * d) =
      (X * X * X - a * d) ^ 2 + ((z + 1) * (X * X) * d - d * a ^ 2 * d) := by ring

/-- The Newton guess is below the reciprocal. -/
theorem newton_i (hX : 2 ≤ X) {d : ℤ} (hd0 : 0 < d)
    (hz2 : d * a ^ 2 < (z + 1) * (X * X)) :
    (2 * X * a - (z + 1)) * d < X * X * (X * X) := by
  have hXX : (0 : ℤ) < X * X := by nlinarith
  have h1 : d * a ^ 2 * d < (z + 1) * (X * X) * d := mul_lt_mul_of_pos_right hz2 hd0
  have h2 : 0 < X * X * (X * X * (X * X) - (2 * X * a - (z + 1)) * d) := by
    rw [newton_id]; nlinarith [sq_nonneg (X * X * X - a * d)]
  have h3 := pos_of_mul_pos_right h2 hXX.le
  linarith

/-- The reciprocal is less than `9` above the Newton guess. -/
theorem newton_ii (hX : 2 ≤ X) {d : ℤ} (hd0 : 0 < d) (hd2 : X * X ≤ 2 * d)
    (hu1 : -(2 * (X * X)) < X * X * X - a * d) (hu2 : X * X * X - a * d < X * X)
    (hz1 : z * (X * X) ≤ d * a ^ 2) :
    X * X * (X * X) < (2 * X * a - (z + 1) + 9) * d := by
  have hXX : (0 : ℤ) < X * X := by nlinarith
  have h1 : (z + 1) * (X * X) * d ≤ (d * a ^ 2 + X * X) * d :=
    mul_le_mul_of_nonneg_right (by linarith) hd0.le
  have hsq : (X * X * X - a * d) ^ 2 < 4 * (X * X) * (X * X) := by
    have p1 : 0 < 2 * (X * X) - (X * X * X - a * d) := by linarith
    have p2 : 0 < 2 * (X * X) + (X * X * X - a * d) := by linarith
    have := mul_pos p1 p2
    nlinarith
  have h2 : X * X * (X * X * (X * X) - (2 * X * a - (z + 1)) * d) <
      X * X * (4 * (X * X) + d) := by
    rw [newton_id]; nlinarith
  have h3 : X * X * (X * X) - (2 * X * a - (z + 1)) * d < 4 * (X * X) + d :=
    lt_of_mul_lt_mul_left h2 hXX.le
  nlinarith

end Ints

/-- The Newton step: `y d < 16 ^ k < (y + 9) d` for `y = newtonGuess k d a`, and the subtraction
in `newtonGuess` does not truncate. -/
theorem newton_step {k d : ℕ} (hk : 1 ≤ k) (hd : 4 ^ k ≤ 2 * d) (hd' : d < 4 ^ k) :
    d * (4 ^ k / (d / 2 ^ k)) ^ 2 / 4 ^ k + 1 ≤ 2 ^ (k + 1) * (4 ^ k / (d / 2 ^ k)) ∧
      newtonGuess k d (4 ^ k / (d / 2 ^ k)) * d < 16 ^ k ∧
      16 ^ k < (newtonGuess k d (4 ^ k / (d / 2 ^ k)) + 9) * d := by
  set X := 2 ^ k with hX
  have hX2 : (2 : ℕ) ≤ X := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hXe : 2 ∣ X := dvd_pow_self 2 (by omega)
  have h4 : (4 : ℕ) ^ k = X * X := by rw [hX, ← mul_pow]; norm_num
  have h16 : (16 : ℕ) ^ k = X * X * (X * X) := by rw [hX, ← mul_pow, ← mul_pow]; norm_num
  have h2k : (2 : ℕ) ^ (k + 1) = 2 * X := by rw [pow_succ, hX]; ring
  simp only [newtonGuess]
  rw [h4] at hd hd' ⊢
  rw [h16, h2k]
  have hdX : d = d / X * X + d % X := (Nat.div_add_mod' d X).symm
  set dh := d / X with hdh
  set ℓ := d % X with hℓ
  have hℓX : ℓ < X := Nat.mod_lt _ (by omega)
  have hdh_lt : dh < X := Nat.div_lt_of_lt_mul hd'
  have hdh_ge : X ≤ 2 * dh := by
    by_contra h
    push_neg at h
    have : 2 * d < X * X := by
      calc 2 * d = 2 * (dh * X + ℓ) := by rw [← hdX]
        _ < 2 * (dh * X + X) := by omega
        _ = (2 * dh + 2) * X := by ring
        _ ≤ X * X := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdh_pos : 0 < dh := by omega
  set a := X * X / dh with ha
  have ha1 : a * dh ≤ X * X := Nat.div_mul_le_self _ _
  have ha2 : X * X < (a + 1) * dh := by
    have := Nat.lt_div_mul_add (a := X * X) hdh_pos
    rw [add_mul, one_mul]
    exact this
  have ha_le : a ≤ 2 * X := by
    have hax : a * X ≤ 2 * X * X :=
      calc a * X ≤ a * (2 * dh) := Nat.mul_le_mul_left _ hdh_ge
        _ = 2 * (a * dh) := by ring
        _ ≤ 2 * (X * X) := Nat.mul_le_mul_left _ ha1
        _ = 2 * X * X := by ring
    exact Nat.le_of_mul_le_mul_right hax (by omega : 0 < X)
  have ha_ge : X ≤ a := by
    by_contra h
    push_neg at h
    have h1 : (a + 1) * dh ≤ X * dh := Nat.mul_le_mul_right _ h
    have h2 : X * dh < X * X := Nat.mul_lt_mul_of_pos_left hdh_lt (by omega)
    omega
  set z := d * a ^ 2 / (X * X) with hz
  have hXX : 0 < X * X := by positivity
  have hz1 : z * (X * X) ≤ d * a ^ 2 := Nat.div_mul_le_self _ _
  have hz2 : d * a ^ 2 < (z + 1) * (X * X) := by
    have := Nat.lt_div_mul_add (a := d * a ^ 2) hXX
    rw [add_mul, one_mul]
    exact this
  -- the integer bounds
  have id : (d : ℤ) = dh * X + ℓ := by exact_mod_cast hdX
  have iX : (2 : ℤ) ≤ X := by exact_mod_cast hX2
  have hu := newton_u (X := X) (dh := dh) (ℓ := ℓ) (a := a) iX (by positivity)
    (by exact_mod_cast hℓX) (by exact_mod_cast hdh_lt) (by exact_mod_cast ha1)
    (by exact_mod_cast ha2) (by exact_mod_cast ha_le)
  rw [← id] at hu
  have iz1 : (z : ℤ) * (X * X) ≤ d * a ^ 2 := by exact_mod_cast hz1
  have iz2 : (d : ℤ) * a ^ 2 < (z + 1) * (X * X) := by exact_mod_cast hz2
  have hiii' := newton_iii (X := X) (dh := dh) (ℓ := ℓ) (a := a) (z := z) iX
    (by exact_mod_cast ha_ge) (by rw [← id]; exact hu.1) (by rw [← id]; exact iz1)
  have hiii : z + 1 ≤ 2 * X * a := by exact_mod_cast hiii'
  have id0 : (0 : ℤ) < d := by exact_mod_cast (show 0 < d by omega)
  have hi := newton_i iX id0 iz2
  have hii := newton_ii iX id0 (by exact_mod_cast hd) hu.1 hu.2 iz1
  refine ⟨hiii, ?_, ?_⟩
  · have : (((2 * X * a - (z + 1) : ℕ) * d : ℕ) : ℤ) < ((X * X * (X * X) : ℕ) : ℤ) := by
      push_cast [hiii]; exact hi
    exact_mod_cast this
  · have : ((X * X * (X * X) : ℕ) : ℤ) < (((2 * X * a - (z + 1) : ℕ) + 9) * d : ℕ) := by
      push_cast [hiii]; exact hii
    exact_mod_cast this

/-! ### Barrett reduction for a power of two -/

theorem barrett2_le (p s x : ℕ) : x * (2 ^ s / p) / 2 ^ s * p ≤ x := by
  have hR : 0 < 2 ^ s := by positivity
  have hq : x * (2 ^ s / p) / 2 ^ s * 2 ^ s ≤ x * (2 ^ s / p) := Nat.div_mul_le_self _ _
  have hμ : 2 ^ s / p * p ≤ 2 ^ s := Nat.div_mul_le_self _ _
  generalize 2 ^ s / p = μ at hq hμ ⊢
  generalize x * μ / 2 ^ s = q at hq ⊢
  generalize 2 ^ s = R at hR hq hμ
  refine Nat.le_of_mul_le_mul_right ?_ hR
  calc q * p * R = q * R * p := by ring
    _ ≤ x * μ * p := Nat.mul_le_mul_right _ hq
    _ = x * (μ * p) := by ring
    _ ≤ x * R := Nat.mul_le_mul_left _ hμ

theorem barrett2_lt (p s x : ℕ) (hp : 0 < p) (hx : x < 2 ^ s) :
    x < x * (2 ^ s / p) / 2 ^ s * p + 2 * p := by
  have hR : 0 < 2 ^ s := by positivity
  have hμ : 2 ^ s < 2 ^ s / p * p + p := Nat.lt_div_mul_add hp
  have hq : x * (2 ^ s / p) < x * (2 ^ s / p) / 2 ^ s * 2 ^ s + 2 ^ s := Nat.lt_div_mul_add hR
  generalize 2 ^ s / p = μ at hμ hq ⊢
  generalize x * μ / 2 ^ s = q at hq ⊢
  generalize 2 ^ s = R at hR hx hμ hq
  refine Nat.lt_of_mul_lt_mul_right (a := R) ?_
  calc x * R ≤ x * (μ * p + p) := Nat.mul_le_mul_left _ hμ.le
    _ = x * μ * p + x * p := by ring
    _ ≤ (q * R + R) * p + x * p := Nat.add_le_add_right (Nat.mul_le_mul_right _ hq.le) _
    _ < (q * R + R) * p + R * p := Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hx hp) _
    _ = (q * p + 2 * p) * R := by ring

end IntegerMultBounds.MathlibTM2.DFT
