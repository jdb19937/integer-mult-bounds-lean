module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-! Odd pairwise coprime source lengths without short-interval primes. The
assembly only needs the source lengths `sᵢ` to be odd and pairwise coprime with
`(1 - 2η) tᵢ < sᵢ ≤ (1 - η) tᵢ`, `η = 1/(4d)`, where every `tᵢ` is `X` or
`2X`. Lengths `1 + k·M` with `M = 2·d!` share no prime up to `d`, and choosing
the offset as a multiple of `guard d` rules out every larger common prime between
the two groups. Only `X ≥ bound d` is needed. -/

@[expose] public section

namespace IntegerMultBounds.NLogN.CoprimeLengths

open Finset

/-- An even modulus divisible by every positive integer up to `d`. -/
def modulus (d : ℕ) : ℕ := 2 * d.factorial

/-- The product of `1 + m · modulus d` over `m < 4d`. -/
def guard (d : ℕ) : ℕ := ∏ m ∈ range (4 * d), (1 + m * modulus d)

/-- The base length from which the construction fits its intervals. -/
def bound (d : ℕ) : ℕ := 4 * d * (1 + guard d * modulus d + 2 * d * modulus d)

theorem modulus_pos (d : ℕ) : 0 < modulus d := by
  unfold modulus; positivity

theorem guard_pos (d : ℕ) : 0 < guard d :=
  prod_pos fun _ _ => by positivity

/-- A prime dividing the modulus divides no `1 + k · modulus`. -/
theorem not_dvd_one_add {d q : ℕ} (hq : q.Prime) (hqM : q ∣ modulus d) (k : ℕ) :
    ¬ q ∣ 1 + k * modulus d := by
  intro h
  have hk : q ∣ k * modulus d := Dvd.dvd.mul_left hqM k
  exact hq.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left hk).mp h))

/-- Every prime up to `d` divides the modulus. -/
theorem prime_dvd_modulus {d q e : ℕ} (hq : q.Prime) (he : 0 < e) (hed : e ≤ d) (hqe : q ∣ e) :
    q ∣ modulus d :=
  Dvd.dvd.mul_left (Nat.dvd_factorial hq.pos ((Nat.le_of_dvd he hqe).trans hed)) 2

/-- No prime divides `1 + k · M` and `1 + k' · M` when `0 < k' - k ≤ d`. -/
theorem no_common_prime {d q k k' : ℕ} (hq : q.Prime) (hkk : k < k') (hd : k' - k ≤ d)
    (hk : q ∣ 1 + k * modulus d) (hk' : q ∣ 1 + k' * modulus d) : False := by
  have hsplit : 1 + k' * modulus d = (1 + k * modulus d) + (k' - k) * modulus d := by
    have : k' = k + (k' - k) := by omega
    conv_lhs => rw [this]
    ring
  rw [hsplit] at hk'
  have hprod : q ∣ (k' - k) * modulus d := (Nat.dvd_add_right hk).mp hk'
  rcases (Nat.Prime.dvd_mul hq).mp hprod with h | h
  · exact not_dvd_one_add hq (prime_dvd_modulus hq (by omega) hd h) k hk
  · exact not_dvd_one_add hq h k hk

theorem coprime_same {d k k' : ℕ} (hne : k ≠ k') (hd : k - k' ≤ d) (hd' : k' - k ≤ d) :
    Nat.Coprime (1 + k * modulus d) (1 + k' * modulus d) := by
  refine Nat.coprime_of_dvd fun q hq h h' => ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact no_common_prime hq hlt hd' h h'
  · exact no_common_prime hq hlt hd h' h

/-- Lengths `1 + (c + j) M` and `1 + (2c + k₂) M` are coprime when `guard d ∣ c`
and `j ≠ k₂` lie in `[d + 1, 2d]`. -/
theorem coprime_cross {d c j k₂ : ℕ} (hc : guard d ∣ c) (hj : d + 1 ≤ j) (hj' : j ≤ 2 * d)
    (hk₂ : d + 1 ≤ k₂) (hk₂' : k₂ ≤ 2 * d) (hne : j ≠ k₂) :
    Nat.Coprime (1 + (c + j) * modulus d) (1 + (2 * c + k₂) * modulus d) := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = 2 * j - k₂ := ⟨_, rfl⟩
  have hjm : j - m ≤ d := by omega
  have hmj : m - j ≤ d := by omega
  have hmlt : m < 4 * d := by omega
  have htwoj : 2 * j = k₂ + m := by omega
  have hcase : j < m ∨ m < j := by omega
  refine Nat.coprime_of_dvd fun q hq hA hB => ?_
  set M := modulus d
  have htwice : 2 * (1 + (c + j) * M) = (1 + (2 * c + k₂) * M) + (1 + m * M) := by
    calc 2 * (1 + (c + j) * M) = 1 + (2 * c + 2 * j) * M + 1 := by ring
      _ = 1 + (2 * c + k₂) * M + (1 + m * M) := by rw [htwoj]; ring
  have hm : q ∣ 1 + m * M := by
    have h2 : q ∣ 2 * (1 + (c + j) * M) := Dvd.dvd.mul_left hA 2
    rw [htwice] at h2
    exact (Nat.dvd_add_right hB).mp h2
  have hqc : q ∣ c :=
    hm.trans ((dvd_prod_of_mem _ (mem_range.mpr hmlt)).trans hc)
  have hj1 : q ∣ 1 + j * M := by
    have hcM : q ∣ c * M := Dvd.dvd.mul_right hqc M
    have : 1 + (c + j) * M = c * M + (1 + j * M) := by ring
    rw [this] at hA
    exact (Nat.dvd_add_right hcM).mp hA
  rcases hcase with hlt | hlt
  · exact no_common_prime hq hlt hmj hj1 hm
  · exact no_common_prime hq hlt hjm hm hj1

/-- The source lengths: index `i` uses `k = d + 1 + i`, with offset `c` for the
short axes (`tᵢ = X`) and `2c` for the long axes (`tᵢ = 2X`). -/
def length (d c : ℕ) (long : Bool) (i : ℕ) : ℕ :=
  1 + ((if long then 2 * c else c) + (d + 1 + i)) * modulus d

theorem length_odd (d c : ℕ) (long : Bool) (i : ℕ) : Odd (length d c long i) := by
  unfold length modulus
  exact Even.one_add (Even.mul_left (even_two.mul_right _) _)

theorem length_coprime {d c : ℕ} (hc : guard d ∣ c) {i i' : ℕ} (hi : i < d) (hi' : i' < d)
    (hne : i ≠ i') (long long' : Bool) :
    Nat.Coprime (length d c long i) (length d c long' i') := by
  unfold length
  cases long <;> cases long' <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact coprime_same (by omega) (by omega) (by omega)
  · exact coprime_cross hc (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact (coprime_cross hc (by omega) (by omega) (by omega) (by omega) (by omega)).symm
  · rw [show 2 * c + (d + 1 + i) = (2 * c) + (d + 1 + i) from rfl]
    have := coprime_same (d := d) (k := 2 * c + (d + 1 + i)) (k' := 2 * c + (d + 1 + i'))
      (by omega) (by omega) (by omega)
    exact this

/-- For `X ≥ bound d` there are odd, pairwise coprime `sᵢ` with
`(1 - 2η) tᵢ < sᵢ ≤ (1 - η) tᵢ`, `η = 1/(4d)`, whenever each `tᵢ` is `X` or `2X`. -/
theorem exists_lengths {d X : ℕ} (hd : 1 ≤ d) (hX : bound d ≤ X) (t : Fin d → ℕ)
    (ht : ∀ i, t i = X ∨ t i = 2 * X) :
    ∃ s : Fin d → ℕ, (∀ i, Odd (s i)) ∧ Pairwise (fun i i' => Nat.Coprime (s i) (s i')) ∧
      ∀ i, (4 * d - 2) * t i < 4 * d * s i ∧ 4 * d * s i ≤ (4 * d - 1) * t i := by
  set M := modulus d
  set G := guard d
  set W := 4 * d
  have hM := modulus_pos d
  have hG := guard_pos d
  have hW : 4 ≤ W := by omega
  have hP : 0 < W * G * M := by positivity
  set u := (W - 2) * X / (W * G * M) + 1
  have hlo : (W - 2) * X < W * G * M * u := Nat.lt_mul_div_succ _ hP
  have hhi : W * G * M * u ≤ (W - 2) * X + W * G * M := by
    have := Nat.div_mul_le_self ((W - 2) * X) (W * G * M)
    simp only [u, mul_add, mul_one]
    linarith [mul_comm (W * G * M) ((W - 2) * X / (W * G * M))]
  let long : Fin d → Bool := fun i => decide (t i = 2 * X)
  refine ⟨fun i => length d (G * u) (long i) i, fun i => length_odd _ _ _ _,
    fun i i' hne => length_coprime (Dvd.intro u rfl) i.2 i'.2 (Fin.val_ne_of_ne hne) _ _, ?_⟩
  intro i
  have hi := i.2
  have hXb : W * (1 + G * M + 2 * d * M) ≤ X := hX
  have hc : W * (G * u * M) = W * G * M * u := by ring
  have hW2 : W - 2 + 1 = W - 1 := by omega
  have hXpos : 0 < X := by
    have : 0 < W * (1 + G * M + 2 * d * M) := by positivity
    omega
  rcases ht i with h | h
  · have hl : long i = false := by
      simp only [long, decide_eq_false_iff_not, h]; omega
    simp only [hl, h, length, Bool.false_eq_true, ↓reduceIte]
    constructor
    · nlinarith
    · have hk : (G * u + (d + 1 + i)) * M ≤ G * u * M + 2 * d * M := by nlinarith
      have : (W - 1) * X = (W - 2) * X + X := by
        rw [← hW2, add_mul, one_mul]
      nlinarith
  · have hl : long i = true := by simp [long, h]
    simp only [hl, h, length, ↓reduceIte]
    constructor
    · nlinarith
    · have hk : (2 * (G * u) + (d + 1 + i)) * M ≤ 2 * (G * u * M) + 2 * d * M := by nlinarith
      have : (W - 1) * (2 * X) = (W - 2) * (2 * X) + 2 * X := by
        rw [← hW2, add_mul, one_mul]
      nlinarith

/-- The threshold is at most `2^(84 d³)`. -/
theorem bound_le {d : ℕ} (hd : 1 ≤ d) : bound d ≤ 2 ^ (84 * d ^ 3) := by
  set B := 2 ^ (4 * d) with hBdef
  have hB4 : 4 * d ≤ B := by
    have := Nat.lt_two_pow_self (n := 4 * d)
    omega
  have hB16 : 16 ≤ B := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ B := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB1 : 1 ≤ B := by omega
  have hM : modulus d ≤ B ^ (d + 1) := by
    unfold modulus
    calc 2 * d.factorial ≤ B * d ^ d := Nat.mul_le_mul (by omega) (Nat.factorial_le_pow d)
      _ ≤ B * B ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
      _ = B ^ (d + 1) := by ring
  have hfac : ∀ m ∈ range (4 * d), 1 + m * modulus d ≤ B ^ (d + 3) := by
    intro m hm
    have hm' : m ≤ B := by have := mem_range.mp hm; omega
    calc 1 + m * modulus d ≤ B ^ (d + 2) + B * B ^ (d + 1) := by
          gcongr
          · exact Nat.one_le_pow _ _ (by omega)
      _ = 2 * B ^ (d + 2) := by ring
      _ ≤ B * B ^ (d + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = B ^ (d + 3) := by ring
  have hG : guard d ≤ B ^ ((d + 3) * (4 * d)) := by
    unfold guard
    calc ∏ m ∈ range (4 * d), (1 + m * modulus d) ≤ (B ^ (d + 3)) ^ (range (4 * d)).card :=
          prod_le_pow_card _ _ _ hfac
      _ = B ^ ((d + 3) * (4 * d)) := by rw [card_range, ← pow_mul]
  have hMpos := modulus_pos d
  have hGpos := guard_pos d
  have hsum : 1 + guard d * modulus d + 2 * d * modulus d ≤ B * B * (guard d * modulus d) := by
    have h1 : 1 ≤ guard d * modulus d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : 2 * d * modulus d ≤ B * (guard d * modulus d) := by
      calc 2 * d * modulus d ≤ B * modulus d := Nat.mul_le_mul_right _ (by omega)
        _ ≤ B * (guard d * modulus d) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hGpos)
    have hBB : (B + 2) * (guard d * modulus d) ≤ B * B * (guard d * modulus d) :=
      Nat.mul_le_mul_right _ (by nlinarith)
    have hexpand : (B + 2) * (guard d * modulus d) =
        B * (guard d * modulus d) + 2 * (guard d * modulus d) := by ring
    omega
  have hexp : 3 + (d + 3) * (4 * d) + (d + 1) ≤ 21 * d ^ 2 := by nlinarith
  calc bound d = 4 * d * (1 + guard d * modulus d + 2 * d * modulus d) := rfl
    _ ≤ B * (B * B * (guard d * modulus d)) := Nat.mul_le_mul hB4 hsum
    _ ≤ B * (B * B * (B ^ ((d + 3) * (4 * d)) * B ^ (d + 1))) := by gcongr
    _ = B ^ (3 + (d + 3) * (4 * d) + (d + 1)) := by ring
    _ ≤ B ^ (21 * d ^ 2) := Nat.pow_le_pow_right hB1 hexp
    _ = 2 ^ (84 * d ^ 3) := by rw [hBdef, ← pow_mul]; ring_nf

end IntegerMultBounds.NLogN.CoprimeLengths
