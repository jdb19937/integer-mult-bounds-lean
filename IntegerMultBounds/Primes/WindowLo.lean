module

public import IntegerMultBounds.MathlibTM2.Mult.Moduli
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The window ends in integer arithmetic

The window of relative width `η = 1/(4d)` below `t` is `(winLo d t, winHi d t]`, with
`winLo d t = ⌊(1 - 2η) t⌋₊` and `winHi d t = ⌊(1 - η) t⌋₊`. Both are `winFloor k t =
t - ⌈t/k⌉`, computed as `t - (t + k - 1)/k` (`winFloor_eq_floor`).

* `ceil_spec`: `q = (t + k - 1)/k` satisfies `t ≤ k q < t + k`.
* `axisBounds_of_mem`: a number of the window satisfies `Moduli.AxisBounds d s t`.
* `winHi_lt`, `three_le_winLo`, `winHi_le_winLo_two_mul`: the window lies below `t`, above `3`
  for `t ≥ 8`, and below the window of `2t`.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open IntegerMultBounds.MathlibTM2.Mult

/-- `t - ⌈t/k⌉`, the floor of `(1 - 1/k) t`. -/
def winFloor (k t : ℕ) : ℕ := t - (t + k - 1) / k

/-- `⌊(1 - 2η) t⌋₊`, `η = 1/(4d)`. -/
def winLo (d t : ℕ) : ℕ := winFloor (2 * d) t

/-- `⌊(1 - η) t⌋₊`, `η = 1/(4d)`. -/
def winHi (d t : ℕ) : ℕ := winFloor (4 * d) t

/-- `q = ⌈t/k⌉` satisfies `t ≤ k q < t + k`. -/
theorem ceil_spec {k : ℕ} (hk : 0 < k) (t : ℕ) :
    t ≤ k * ((t + k - 1) / k) ∧ k * ((t + k - 1) / k) < t + k := by
  have h := Nat.div_add_mod (t + k - 1) k
  have hr := Nat.mod_lt (t + k - 1) hk
  omega

theorem ceil_le_self {k : ℕ} (hk : 0 < k) (t : ℕ) : (t + k - 1) / k ≤ t := by
  have h := (ceil_spec hk t).2
  by_contra hc
  have : k * (t + 1) ≤ k * ((t + k - 1) / k) := Nat.mul_le_mul_left k (by omega)
  nlinarith

/-- The integer form of the window ends is the floor of the real one. -/
theorem winFloor_eq_floor {k : ℕ} (hk : 0 < k) (t : ℕ) :
    winFloor k t = ⌊(1 - 1 / (k : ℝ)) * t⌋₊ := by
  obtain ⟨hlo, hhi⟩ := ceil_spec hk t
  have hle := ceil_le_self hk t
  set q := (t + k - 1) / k
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 ≤ (1 - 1 / (k : ℝ)) * t := by
    have : 1 / (k : ℝ) ≤ 1 := by
      rw [div_le_one hk']
      exact_mod_cast hk
    exact mul_nonneg (by linarith) (Nat.cast_nonneg t)
  symm
  rw [Nat.floor_eq_iff hx, winFloor, Nat.cast_sub hle]
  have hloR : (t : ℝ) ≤ k * q := by exact_mod_cast hlo
  have hhiR : (k : ℝ) * q < t + k := by exact_mod_cast hhi
  have e : (1 - 1 / (k : ℝ)) * t = t - t / k := by field_simp
  rw [e]
  constructor
  · have : (t : ℝ) / k ≤ q := by rw [div_le_iff₀ hk']; linarith
    linarith
  · have : (q : ℝ) - 1 < t / k := by rw [lt_div_iff₀ hk']; linarith
    linarith

theorem winLo_eq_floor {d : ℕ} (hd : 1 ≤ d) (t : ℕ) :
    winLo d t = ⌊(1 - 1 / (2 * (d : ℝ))) * t⌋₊ := by
  rw [winLo, winFloor_eq_floor (by omega)]
  push_cast
  rfl

theorem winHi_eq_floor {d : ℕ} (hd : 1 ≤ d) (t : ℕ) :
    winHi d t = ⌊(1 - 1 / (4 * (d : ℝ))) * t⌋₊ := by
  rw [winHi, winFloor_eq_floor (by omega)]
  push_cast
  rfl

/-- A number of the window `(winLo d t, winHi d t]` satisfies the axis bounds. -/
theorem axisBounds_of_mem {d s t : ℕ} (hd : 1 ≤ d) (hlo : winLo d t < s) (hhi : s ≤ winHi d t) :
    Moduli.AxisBounds d s t := by
  obtain ⟨h2lo, h2hi⟩ := ceil_spec (k := 2 * d) (by omega) t
  obtain ⟨h4lo, h4hi⟩ := ceil_spec (k := 4 * d) (by omega) t
  have hq2 := ceil_le_self (k := 2 * d) (by omega) t
  have hq4 := ceil_le_self (k := 4 * d) (by omega) t
  unfold winLo winHi winFloor at *
  set q₂ := (t + 2 * d - 1) / (2 * d)
  set q₄ := (t + 4 * d - 1) / (4 * d)
  have hs₁ : t + 1 ≤ s + q₂ := by omega
  have hs₂ : s + q₄ ≤ t := by omega
  constructor
  · have := Nat.mul_le_mul_left (2 * d) hs₁
    nlinarith
  · have := Nat.mul_le_mul_left (4 * d) hs₂
    nlinarith

theorem winHi_lt {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) : winHi d t < t := by
  obtain ⟨h4lo, -⟩ := ceil_spec (k := 4 * d) (by omega) t
  unfold winHi winFloor
  generalize (t + 4 * d - 1) / (4 * d) = q at *
  have : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      omega
    · exact h
  omega

theorem three_le_winLo {d t : ℕ} (hd : 1 ≤ d) (ht : 8 ≤ t) : 3 ≤ winLo d t := by
  obtain ⟨-, h2hi⟩ := ceil_spec (k := 2 * d) (by omega) t
  unfold winLo winFloor
  set q := (t + 2 * d - 1) / (2 * d)
  have h2q : 2 * q ≤ t + 1 := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · omega
    · have h1 : 2 * d * (q - 1) < t := by
        have e : 2 * d * (q - 1) + 2 * d = 2 * d * q := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      have h2 : 2 * (q - 1) ≤ 2 * d * (q - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
  omega

/-- The window below `t` ends below the window below `2t`. -/
theorem winHi_le_winLo_two_mul {d t : ℕ} (hd : 1 ≤ d) : winHi d t ≤ winLo d (2 * t) := by
  have hq := ceil_le_self (k := 2 * d) (by omega) (2 * t)
  obtain ⟨-, h2hi⟩ := ceil_spec (k := 2 * d) (by omega) (2 * t)
  unfold winHi winLo winFloor
  generalize (2 * t + 2 * d - 1) / (2 * d) = q at *
  generalize (t + 4 * d - 1) / (4 * d) = q₄
  have hqt : q ≤ t := by
    by_contra hc
    have : 2 * d * (t + 1) ≤ 2 * d * q := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  omega

end IntegerMultBounds.Primes
