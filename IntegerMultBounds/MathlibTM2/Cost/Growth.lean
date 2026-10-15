module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Size

/-!
# Growth of the size parameters

Bounds on the parameters of `Mult/Sizes.lean` in powers of `B = b n = ⌈log₂ n⌉`, the comparison
of `B` with `L = log n`, and closure lemmas for `IsBigO` against `n L^e`. Here `ε = 2^{-30}`
(`epsilon`) and `c = 2^{-34}` (`cParam`).

* `gr_log_le_b`, `gr_b_le_two_log`: `L ≤ B` for every `n`, and `B ≤ 2L` for `n ≥ 8`.
* `gr_d_le_rpow`, `gr_rpow_le_two_d`: `d ≤ B^ε ≤ 2d` (the second for `d ≥ 1`), and the powers
  `gr_d_rpow_le`, `gr_rpow_le_two_d_rpow`: `d^a ≤ B^{εa} ≤ 2 d^a` for `0 ≤ a ≤ 1`.
* `gr_K_le_rpow`, `gr_rpow_le_four_K_rpow`: `K ≤ B^{εc}` and `B^{εca} ≤ 4 K^a` (`K ≥ 1`).
* `gr_Tb_le`, `gr_Tp_le`, `gr_le_Tp`: `T B ≤ 8n` and `24 n ≤ T p ≤ 48 n`.
* `gr_dℓ_le`, `gr_ℓ_le_div_add`, `gr_ℓ_le_rpow`: `d ℓ ≤ 2B`, `ℓ ≤ B/d + 1`, `ℓ ≤ 4 B^{1-ε}`.
* `gr_r_eq`, `gr_logb_rp`, `gr_logb_rp_le`: `r = 2^ℓ`, `log₂ (r p) = ℓ + log₂ p`, and eventually
  `log₂ (r p) ≤ 2ℓ`.
* `gr_alpha_le`: `α ≤ 4 d^{1/2} B^{1/4}`; `gr_gamma_le`: `γ ≤ B/4`; `gr_S_le_T`: `S ≤ T`.
* `gr_pow_b_le`: `B^C ≤ n` eventually, for every fixed `C`.
* `gr_p_rpow_le`: `p^x ≤ 6 B^x` for `x ≤ 1`.
* `gr_mLogLog_le`: `m (⌊log₂ m⌋ + 1)(⌊log₂ ⌊log₂ m⌋⌋ + 1) ≤ 625 m^{9/8}`, the Schönhage–Strassen
  step bound against `m^{1+δ}`, `δ = 1/8`.
* `grLogLog X = (log₂ X + 1)(log₂ (log₂ X + 1) + 1)`; `gr_sizeProd_le`, `gr_ringBound_le`: the
  packed ring product's bound `rpRingBound N` (`Fast/RingProd`) on `N ≤ A X` bits is at most a
  constant (depending on `A` and the vendored `costC`) times `X · grLogLog X`;
  `gr_two_pow_size_le`: `2^(size x) ≤ 2x`, for the packed width `wOf`.
* `gr_mul_le`, `gr_div_le`: products of power bounds and division by a power lower bound.
* `gr_isBigO_b_rpow`, `gr_isBigO_rpow_mono`, `gr_isBigO_log_mul`: `n B^a = O(n L^a)`,
  `n L^a = O(n L^e)` for `a ≤ e`, and `n L^a (log L)^k = O(n L^e)` for `a < e`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter Asymptotics

/-! ### Arithmetic of power bounds -/

/-- Multiplying two power bounds: `X ≤ A B^x`, `Y ≤ A' B^y` give `X Y ≤ A A' B^{x+y}`. -/
theorem gr_mul_le {B X Y A A' x y : ℝ} (hB : 0 < B) (hY : 0 ≤ Y) (hA : 0 ≤ A)
    (hX : X ≤ A * B ^ x) (hY' : Y ≤ A' * B ^ y) : X * Y ≤ A * A' * B ^ (x + y) := by
  rw [Real.rpow_add hB]
  have hBx : 0 ≤ A * B ^ x := mul_nonneg hA (Real.rpow_nonneg hB.le x)
  calc X * Y ≤ (A * B ^ x) * Y := mul_le_mul_of_nonneg_right hX hY
    _ ≤ (A * B ^ x) * (A' * B ^ y) := mul_le_mul_of_nonneg_left hY' hBx
    _ = A * A' * (B ^ x * B ^ y) := by ring

/-- Dividing by a power lower bound: `B^a ≤ A X` gives `B / X ≤ A B^{1-a}`. -/
theorem gr_div_le {B X A a : ℝ} (hB : 0 < B) (hX : 0 < X) (h : B ^ a ≤ A * X) :
    B / X ≤ A * B ^ (1 - a) := by
  have ha : 0 < B ^ a := Real.rpow_pos_of_pos hB a
  rw [Real.rpow_sub hB, Real.rpow_one, div_le_iff₀ hX]
  calc B = B * B ^ a / B ^ a := by field_simp
    _ ≤ B * (A * X) / B ^ a := by gcongr
    _ = A * (B / B ^ a) * X := by ring

/-- `B^x ≤ B^e` for `1 ≤ B` and `x ≤ e`, with a constant in front. -/
theorem gr_le_rpow_of_le {B X A x e : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (hX : X ≤ A * B ^ x)
    (hxe : x ≤ e) : X ≤ A * B ^ e :=
  hX.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB hxe) hA)

/-! ### `b` against `log n` -/

/-- `log n ≤ b`. -/
theorem gr_log_le_b (n : ℕ) : Real.log n ≤ b n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (n : ℝ) ≤ 2 ^ b n := by exact_mod_cast le_two_pow_b n
  have h2 : Real.log n ≤ Real.log (2 ^ b n) :=
    Real.log_le_log (by exact_mod_cast hn) h1
  rw [Real.log_pow] at h2
  have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h4 : (0 : ℝ) ≤ b n := Nat.cast_nonneg _
  nlinarith

/-- `b ≤ 2 log n` for `n ≥ 8`. -/
theorem gr_b_le_two_log {n : ℕ} (hn : 8 ≤ n) : (b n : ℝ) ≤ 2 * Real.log n := by
  have h1 : ((2 ^ b n : ℕ) : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast two_pow_b_lt (by omega)
  push_cast at h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2 : Real.log (2 ^ b n) < Real.log (2 * n) := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_mul (by norm_num) hn0.ne'] at h2
  have h3 : Real.log 8 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have key : Real.log 2 + Real.log n ≤ 2 * Real.log n * Real.log 2 := by nlinarith
  have h4 : (b n : ℝ) * Real.log 2 < (2 * Real.log n) * Real.log 2 := by linarith
  exact (lt_of_mul_lt_mul_right h4 (by linarith)).le

/-! ### `d` and `K` -/

theorem gr_epsilon_pos : 0 < epsilon := by rw [epsilon_eq]; norm_num

theorem gr_epsilon_le_one : epsilon ≤ 1 := by rw [epsilon_eq]; norm_num

theorem gr_cParam_pos : 0 < cParam := by rw [cParam_eq]; norm_num

theorem gr_cParam_le_one : cParam ≤ 1 := by rw [cParam_eq]; norm_num

/-- `d ≤ B^ε`. -/
theorem gr_d_le_rpow (n : ℕ) : (d n : ℝ) ≤ (b n : ℝ) ^ epsilon := by
  rw [d_eq_floor]; exact Nat.floor_le (by positivity)

/-- `B^ε < d + 1`. -/
theorem gr_rpow_lt_d_succ (n : ℕ) : (b n : ℝ) ^ epsilon < d n + 1 := by
  rw [d_eq_floor]; exact Nat.lt_floor_add_one _

/-- `B^ε ≤ 2d` for `d ≥ 1`. -/
theorem gr_rpow_le_two_d {n : ℕ} (hd : 1 ≤ d n) : (b n : ℝ) ^ epsilon ≤ 2 * d n := by
  have h1 := gr_rpow_lt_d_succ n
  have h2 : (1 : ℝ) ≤ d n := by exact_mod_cast hd
  linarith

/-- `d^a ≤ B^{εa}` for `a ≥ 0`. -/
theorem gr_d_rpow_le (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (d n : ℝ) ^ a ≤ (b n : ℝ) ^ (epsilon * a) := by
  rw [Real.rpow_mul (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (gr_d_le_rpow n) ha

/-- `B^{εa} ≤ 2 d^a` for `d ≥ 1`, `0 ≤ a ≤ 1`. -/
theorem gr_rpow_le_two_d_rpow {n : ℕ} (hd : 1 ≤ d n) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (b n : ℝ) ^ (epsilon * a) ≤ 2 * (d n : ℝ) ^ a := by
  rw [Real.rpow_mul (Nat.cast_nonneg _)]
  calc ((b n : ℝ) ^ epsilon) ^ a ≤ (2 * (d n : ℝ)) ^ a :=
        Real.rpow_le_rpow (by positivity) (gr_rpow_le_two_d hd) ha
    _ = (2 : ℝ) ^ a * (d n : ℝ) ^ a := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 2 * (d n : ℝ) ^ a := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num) ha1

/-- `K ≤ d^c`. -/
theorem gr_K_le_d_rpow (n : ℕ) : (K n : ℝ) ≤ (d n : ℝ) ^ cParam := by
  rw [K_eq_floor]; exact Nat.floor_le (by positivity)

/-- `d^c ≤ 2K` for `K ≥ 1`. -/
theorem gr_d_rpow_le_two_K {n : ℕ} (hK : 1 ≤ K n) : (d n : ℝ) ^ cParam ≤ 2 * K n := by
  have h1 : (d n : ℝ) ^ cParam < K n + 1 := by rw [K_eq_floor]; exact Nat.lt_floor_add_one _
  have h2 : (1 : ℝ) ≤ K n := by exact_mod_cast hK
  linarith

/-- `K ≤ B^{εc}`. -/
theorem gr_K_le_rpow (n : ℕ) : (K n : ℝ) ≤ (b n : ℝ) ^ (epsilon * cParam) :=
  (gr_K_le_d_rpow n).trans (gr_d_rpow_le n gr_cParam_pos.le)

/-- `B^{εca} ≤ 4 K^a` for `K ≥ 1`, `0 ≤ a ≤ 1`. -/
theorem gr_rpow_le_four_K_rpow {n : ℕ} (hK : 1 ≤ K n) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (b n : ℝ) ^ (epsilon * cParam * a) ≤ 4 * (K n : ℝ) ^ a := by
  have hd : 1 ≤ d n := hK.trans (K_le_d n)
  have h1 : (b n : ℝ) ^ (epsilon * cParam) ≤ 4 * K n :=
    calc (b n : ℝ) ^ (epsilon * cParam) ≤ 2 * (d n : ℝ) ^ cParam :=
          gr_rpow_le_two_d_rpow hd gr_cParam_pos.le gr_cParam_le_one
      _ ≤ 2 * (2 * K n) := by gcongr; exact gr_d_rpow_le_two_K hK
      _ = 4 * K n := by ring
  rw [Real.rpow_mul (Nat.cast_nonneg _)]
  calc ((b n : ℝ) ^ (epsilon * cParam)) ^ a ≤ (4 * (K n : ℝ)) ^ a :=
        Real.rpow_le_rpow (by positivity) h1 ha
    _ = (4 : ℝ) ^ a * (K n : ℝ) ^ a := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 4 * (K n : ℝ) ^ a := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num) ha1

/-- `1 ≤ K` for all large `n`. -/
theorem gr_one_le_K : ∀ᶠ n in atTop, 1 ≤ K n := tendsto_atTop.1 tendsto_K 1

/-! ### `T`, `p`, `ℓ`, `r` -/

/-- `T B ≤ 8n`. -/
theorem gr_Tb_le {n : ℕ} (hn : 2 ≤ n) : (T n : ℝ) * b n ≤ 8 * n := by
  have : (b n * T n : ℝ) < 8 * n := by exact_mod_cast bT_lt hn
  linarith

/-- `T p ≤ 48 n`. -/
theorem gr_Tp_le {n : ℕ} (hn : 2 ≤ n) : (T n : ℝ) * p n ≤ 48 * n := by
  have : (T n * p n : ℝ) < 48 * n := by exact_mod_cast (volume_bounds hn).2
  linarith

/-- `24 n ≤ T p`. -/
theorem gr_le_Tp {n : ℕ} (hn : 2 ≤ n) : 24 * (n : ℝ) ≤ T n * p n := by
  exact_mod_cast (volume_bounds hn).1

/-- `p = 6B`. -/
theorem gr_p_eq (n : ℕ) : (p n : ℝ) = 6 * b n := by unfold p; push_cast; ring

/-- `p^x ≤ 6 B^x` for `x ≤ 1`. -/
theorem gr_p_rpow_le (n : ℕ) {x : ℝ} (hx1 : x ≤ 1) :
    (p n : ℝ) ^ x ≤ 6 * (b n : ℝ) ^ x := by
  rw [gr_p_eq, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
  gcongr
  exact Real.rpow_le_self_of_one_le (by norm_num) hx1

/-- `d ℓ ≤ 2B`. -/
theorem gr_dℓ_le {n : ℕ} (h : Big n) : (d n : ℝ) * ℓ n ≤ 2 * b n := by
  have h1 : (3 * d n * ℓ n : ℝ) ≤ p n := by exact_mod_cast h.ℓ_bounds.2
  rw [gr_p_eq] at h1
  linarith

/-- `ℓ ≤ B/d + 1`, from `ℓ = ⌈log₂ T / d⌉` and `log₂ T < B`. -/
theorem gr_ℓ_le_div_add {n : ℕ} (h : Big n) : (ℓ n : ℝ) ≤ b n / d n + 1 := by
  have hd : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have h1 : (d n * ℓ n : ℝ) < logT n + d n := by exact_mod_cast dℓ_lt h.one_le_d
  have h2 : (logT n : ℝ) < b n := by exact_mod_cast h.logT_bounds.2
  rw [div_add_one hd.ne', le_div_iff₀ hd]
  linarith

/-- `ℓ ≤ 4 B^{1-ε}`. -/
theorem gr_ℓ_le_rpow {n : ℕ} (h : Big n) : (ℓ n : ℝ) ≤ 4 * (b n : ℝ) ^ (1 - epsilon) := by
  have hd : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have hB : (0 : ℝ) < b n := by exact_mod_cast (show 0 < b n by have := h.sixteen_le_b; omega)
  have h1 : (ℓ n : ℝ) ≤ 2 * (b n / d n) := by
    rw [← mul_div_assoc, le_div_iff₀ hd]
    have := gr_dℓ_le h
    linarith
  have h2 : (b n : ℝ) / d n ≤ 2 * (b n : ℝ) ^ (1 - epsilon) :=
    gr_div_le hB hd (gr_rpow_le_two_d h.one_le_d)
  linarith

/-- `r = 2^ℓ`. -/
theorem gr_r_eq (n : ℕ) : (r n : ℝ) = 2 ^ ℓ n := by unfold r; push_cast; rfl

/-- `log₂ (r p) = ℓ + log₂ p`. -/
theorem gr_logb_rp {n : ℕ} (hp : 1 ≤ p n) :
    Real.logb 2 ((r n : ℝ) * p n) = ℓ n + Real.logb 2 (p n) := by
  have hp0 : (p n : ℝ) ≠ 0 := by exact_mod_cast (show p n ≠ 0 by omega)
  rw [Real.logb_mul (by rw [gr_r_eq]; positivity) hp0, gr_r_eq, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one]

/-- `0 ≤ log₂ (r p)` for `p ≥ 1`. -/
theorem gr_logb_rp_nonneg {n : ℕ} (hp : 1 ≤ p n) : 0 ≤ Real.logb 2 ((r n : ℝ) * p n) := by
  rw [gr_logb_rp hp]
  have : 0 ≤ Real.logb 2 (p n) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hp)
  positivity

/-- `log₂ (r p) ≤ 2ℓ` for all large `n` (`log₂ p ≤ K < ℓ`). -/
theorem gr_logb_rp_le : ∀ᶠ n in atTop, Real.logb 2 ((r n : ℝ) * p n) ≤ 2 * ℓ n := by
  filter_upwards [eventually_big, eventually_logb_p_le_K 1] with n h hK
  have hp : 1 ≤ p n := by have := h.thirteen_le_p; omega
  rw [gr_logb_rp hp]
  have h1 : (K n + 1 : ℝ) ≤ ℓ n := by exact_mod_cast h.K_succ_le_ℓ
  linarith

/-! ### `α`, `γ`, `S` -/

/-- `α ≤ 4 d^{1/2} B^{1/4}`, from `α⁴ ≤ 192 d² B`. -/
theorem gr_alpha_le {n : ℕ} (hn : 2 ≤ n) :
    (alpha n : ℝ) ≤ 4 * (d n : ℝ) ^ (1 / 2 : ℝ) * (b n : ℝ) ^ (1 / 4 : ℝ) := by
  have hD : (0 : ℝ) ≤ d n := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ b n := Nat.cast_nonneg _
  have h1 : (alpha n : ℝ) ^ 4 ≤ 192 * (d n : ℝ) ^ 2 * b n := by
    exact_mod_cast alpha_pow_four_le hn
  have e1 : ((d n : ℝ) ^ (1 / 2 : ℝ)) ^ 4 = (d n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD]; norm_num
  have e2 : ((b n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = b n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]; norm_num
  have h2 : (alpha n : ℝ) ^ 4 ≤ (4 * (d n : ℝ) ^ (1 / 2 : ℝ) * (b n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [mul_pow, mul_pow, e1, e2]
    have : (0 : ℝ) ≤ (d n : ℝ) ^ 2 * b n := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num)).1 h2

/-- `γ ≤ B/4` for all large `n`. -/
theorem gr_gamma_le : ∀ᶠ n in atTop, (gamma n : ℝ) ≤ b n / 4 :=
  eventually_big.mono fun _ h => h.gamma_le_real

/-- `S ≤ T` for all large `n`. -/
theorem gr_S_le_T : ∀ᶠ n in atTop, S n ≤ T n :=
  eventually_big.mono fun _ h => h.S_lt_T.le

/-- `B^C ≤ n` for all large `n`. -/
theorem gr_pow_b_le (C : ℕ) : ∀ᶠ n in atTop, (b n : ℝ) ^ C ≤ n := by
  filter_upwards [eventually_ge_atTop 2, tendsto_b.eventually (eventually_mul_pow_le_two_pow 2 C)]
    with n hn h
  have h2 := two_pow_b_lt hn
  have : b n ^ C ≤ n := by omega
  exact_mod_cast this

/-! ### Schönhage–Strassen step bound -/

/-- `⌊log₂ m⌋ + 1 ≤ 25 m^{1/16}` for `m ≥ 1`. -/
theorem gr_natLog_succ_le {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ 25 * (m : ℝ) ^ (1 / 16 : ℝ) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by exact_mod_cast Real.natLog_le_logb m 2
  have h2 : Real.log m ≤ (m : ℝ) ^ (1 / 16 : ℝ) / (1 / 16) := Real.log_le_rpow_div hm0 (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have h3 : Real.logb 2 m ≤ 24 * (m : ℝ) ^ (1 / 16 : ℝ) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : (0 : ℝ) ≤ (m : ℝ) ^ (1 / 16 : ℝ) := by positivity
    nlinarith
  have h4 : (1 : ℝ) ≤ (m : ℝ) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  push_cast
  linarith

/-- The Schönhage–Strassen step bound against `m^{1+δ}`, `δ = 1/8`:
`m (⌊log₂ m⌋ + 1)(⌊log₂ ⌊log₂ m⌋⌋ + 1) ≤ 625 m^{9/8}`. -/
theorem gr_mLogLog_le {m : ℕ} (hm : 1 ≤ m) :
    ((m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) : ℕ) : ℝ) ≤
      625 * (m : ℝ) ^ (9 / 8 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : Nat.log 2 (Nat.log 2 m) + 1 ≤ Nat.log 2 m + 1 :=
    Nat.succ_le_succ (Nat.log_le_self 2 _)
  have h2 : ((m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) : ℕ) : ℝ) ≤
      (m : ℝ) * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 2 := by
    have : m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) ≤
        m * (Nat.log 2 m + 1) ^ 2 := by
      rw [sq, ← mul_assoc]; exact Nat.mul_le_mul_left _ h1
    exact_mod_cast this
  have h3 := gr_natLog_succ_le hm
  have h4 : ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 2 ≤ (25 * (m : ℝ) ^ (1 / 16 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2
  have e : (m : ℝ) * (25 * (m : ℝ) ^ (1 / 16 : ℝ)) ^ 2 = 625 * (m : ℝ) ^ (9 / 8 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (1 / 16 : ℝ)), ← Real.rpow_mul hm0.le,
      show (9 / 8 : ℝ) = 1 + 1 / 16 * ((2 : ℕ) : ℝ) by norm_num, Real.rpow_add hm0,
      Real.rpow_one]
    ring
  calc _ ≤ (m : ℝ) * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 2 := h2
    _ ≤ (m : ℝ) * (25 * (m : ℝ) ^ (1 / 16 : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left h4 hm0.le
    _ = 625 * (m : ℝ) ^ (9 / 8 : ℝ) := e

/-! ### Packed ring products -/

/-- The factor `log X · log log X` of one packed ring product on `O(X)` bits:
`(log₂ X + 1)(log₂ (log₂ X + 1) + 1)`. -/
noncomputable def grLogLog (X : ℝ) : ℝ :=
  (Real.logb 2 X + 1) * (Real.logb 2 (Real.logb 2 X + 1) + 1)

theorem gr_logb_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ Real.logb 2 X :=
  Real.logb_nonneg one_lt_two hX

theorem gr_one_le_logLog {X : ℝ} (hX : 1 ≤ X) : 1 ≤ grLogLog X := by
  have h1 := gr_logb_nonneg hX
  have h2 : 0 ≤ Real.logb 2 (Real.logb 2 X + 1) := gr_logb_nonneg (by linarith)
  unfold grLogLog
  nlinarith

/-- `size N ≤ log₂ N + 1`. -/
theorem gr_size_le_logb (N : ℕ) : (Nat.size N : ℝ) ≤ Real.logb 2 N + 1 := by
  have h1 : Nat.size N ≤ Nat.log 2 N + 1 :=
    Nat.size_le.2 (Nat.lt_pow_succ_log_self (by norm_num) N)
  have h2 : (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := by exact_mod_cast Real.natLog_le_logb N 2
  have h1' : (Nat.size N : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by exact_mod_cast h1
  linarith

/-- `2^(size x) ≤ 2x` for `x ≥ 1`; with `wOf p l w = 2^(size (mW p l w))` (vendored
`Schoenhage.RingConst`) the packed size is `wOf p l w · 2^l ≤ 2 (2p + l + 2w) 2^l`. -/
theorem gr_two_pow_size_le {x : ℕ} (hx : 1 ≤ x) : 2 ^ Nat.size x ≤ 2 * x := by
  have h1 : 0 < Nat.size x := Nat.size_pos.2 (by omega)
  have h2 : 2 ^ (Nat.size x - 1) ≤ x := by
    by_contra hc
    have := Nat.size_le.2 (not_le.1 hc)
    omega
  have e : 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- The constant of `gr_sizeProd_le`: `2A (log₂ A + 2)(3 log₂ (log₂ A + 2) + 3)`. -/
noncomputable def grRingConst (A : ℕ) : ℝ :=
  2 * A * (Real.logb 2 A + 2) * (3 * Real.logb 2 (Real.logb 2 A + 2) + 3)

theorem gr_ringConst_ge {A : ℕ} (hA : 1 ≤ A) : 12 * (A : ℝ) ≤ grRingConst A := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have ha := gr_logb_nonneg hA1
  have hb : 0 ≤ Real.logb 2 (Real.logb 2 A + 2) := gr_logb_nonneg (by linarith)
  unfold grRingConst
  have h1 : (2 : ℝ) ≤ Real.logb 2 A + 2 := by linarith
  have h2 : (3 : ℝ) ≤ 3 * Real.logb 2 (Real.logb 2 A + 2) + 3 := by linarith
  have h3 : 2 * (A : ℝ) * 2 ≤ 2 * A * (Real.logb 2 A + 2) := by nlinarith
  calc 12 * (A : ℝ) = 2 * A * 2 * 3 := by ring
    _ ≤ 2 * A * (Real.logb 2 A + 2) * (3 * Real.logb 2 (Real.logb 2 A + 2) + 3) :=
        mul_le_mul h3 h2 (by norm_num) (by positivity)

/-- The size factors of the packed ring product on `N ≤ A X` bits (`Fast/RingProd`'s
`rpRingBound` with `bitlen = Nat.size`):
`(N + 1)(size N + 1)(size (size N ^ 3) + 1) ≤ grRingConst A · X · grLogLog X`. -/
theorem gr_sizeProd_le {N A : ℕ} {X : ℝ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hN1 : 1 ≤ N)
    (hN : (N : ℝ) ≤ A * X) :
    ((N : ℝ) + 1) * ((Nat.size N : ℝ) + 1) * ((Nat.size (Nat.size N ^ 3) : ℝ) + 1) ≤
      grRingConst A * X * grLogLog X := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hs : (Nat.size N : ℝ) ≤ Real.logb 2 A + Real.logb 2 X + 1 := by
    have h1 := gr_size_le_logb N
    have h2 : Real.logb 2 N ≤ Real.logb 2 (A * X) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) hN
    rw [Real.logb_mul (by linarith) (by linarith)] at h2
    linarith
  have hs1 : (1 : ℝ) ≤ Nat.size N := by
    have : 0 < Nat.size N := Nat.size_pos.2 (by omega)
    exact_mod_cast this
  have h3 := gr_size_le_logb (Nat.size N ^ 3)
  push_cast at h3
  rw [Real.logb_pow] at h3
  push_cast at h3
  unfold grRingConst grLogLog
  set a := Real.logb 2 (A : ℝ) with ha_def
  set l := Real.logb 2 X with hl_def
  have ha : 0 ≤ a := gr_logb_nonneg hA1
  have hl : 0 ≤ l := gr_logb_nonneg hX
  have f1 : (N : ℝ) + 1 ≤ 2 * A * X := by nlinarith
  have f2 : (Nat.size N : ℝ) + 1 ≤ (a + 2) * (l + 1) := by nlinarith
  have f3 : (Nat.size (Nat.size N ^ 3) : ℝ) + 1 ≤
      (3 * Real.logb 2 (a + 2) + 3) * (Real.logb 2 (l + 1) + 1) := by
    have h4 : Real.logb 2 (Nat.size N) ≤ Real.logb 2 ((a + 2) * (l + 1)) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) (by nlinarith)
    rw [Real.logb_mul (by linarith) (by linarith)] at h4
    have h5 : 0 ≤ Real.logb 2 (a + 2) := gr_logb_nonneg (by linarith)
    have h6 : 0 ≤ Real.logb 2 (l + 1) := gr_logb_nonneg (by linarith)
    nlinarith
  have hs0 : (0 : ℝ) ≤ (Nat.size (Nat.size N ^ 3) : ℝ) + 1 := by positivity
  calc ((N : ℝ) + 1) * ((Nat.size N : ℝ) + 1) * ((Nat.size (Nat.size N ^ 3) : ℝ) + 1) ≤
      (2 * A * X) * ((a + 2) * (l + 1)) *
        ((3 * Real.logb 2 (a + 2) + 3) * (Real.logb 2 (l + 1) + 1)) :=
        mul_le_mul (mul_le_mul f1 f2 (by positivity) (by positivity)) f3 hs0 (by positivity)
    _ = 2 * A * (a + 2) * (3 * Real.logb 2 (a + 2) + 3) * X *
        ((l + 1) * (Real.logb 2 (l + 1) + 1)) := by ring

/-- The packed ring-product bound `4 c (N + 1)(size N + 1)(size (size N ^ 3) + 1) + 11000 N +
250000` (`Fast/RingProd`'s `rpRingBound` with `c = costC cA cB cC0`) on `N ≤ A X` bits is at
most `(4c + 261000) · grRingConst A · X · grLogLog X`. -/
theorem gr_ringBound_le {N A : ℕ} {X c : ℝ} (hc : 0 ≤ c) (hA : 1 ≤ A) (hX : 1 ≤ X)
    (hN1 : 1 ≤ N) (hN : (N : ℝ) ≤ A * X) :
    4 * c * ((N : ℝ) + 1) * ((Nat.size N : ℝ) + 1) * ((Nat.size (Nat.size N ^ 3) : ℝ) + 1) +
        11000 * (N : ℝ) + 250000 ≤ (4 * c + 261000) * (grRingConst A * X * grLogLog X) := by
  have h1 := gr_sizeProd_le hA hX hN1 hN
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hR := gr_ringConst_ge hA
  have hL := gr_one_le_logLog hX
  have hP : (A : ℝ) * X ≤ grRingConst A * X * grLogLog X := by
    have h2 : (A : ℝ) * X ≤ grRingConst A * X := by nlinarith
    have h3 : 0 ≤ grRingConst A * X := by nlinarith
    nlinarith
  have h4 : 11000 * (N : ℝ) + 250000 ≤ 261000 * (grRingConst A * X * grLogLog X) := by
    nlinarith
  have e : 4 * c * ((N : ℝ) + 1) * ((Nat.size N : ℝ) + 1) *
      ((Nat.size (Nat.size N ^ 3) : ℝ) + 1) =
      4 * c * (((N : ℝ) + 1) * ((Nat.size N : ℝ) + 1) *
        ((Nat.size (Nat.size N ^ 3) : ℝ) + 1)) := by ring
  rw [e]
  have h5 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 4 * c by linarith)
  nlinarith

/-! ### Closure of `IsBigO` against `n L^e` -/

theorem gr_one_le_log {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < n by omega))]
  have := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- `n B^a = O(n L^a)` for `a ≥ 0`, from `B ≤ 2L`. -/
theorem gr_isBigO_b_rpow {a : ℝ} (ha : 0 ≤ a) :
    (fun n : ℕ => (n : ℝ) * (b n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ a := by
  apply IsBigO.of_bound ((2 : ℝ) ^ a)
  filter_upwards [eventually_ge_atTop 8] with n hn
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (n : ℝ) * (b n : ℝ) ^ a ≤ (n : ℝ) * (2 * Real.log n) ^ a := by
        gcongr; exact gr_b_le_two_log hn
    _ = (2 : ℝ) ^ a * ((n : ℝ) * Real.log n ^ a) := by
        rw [Real.mul_rpow (by norm_num) hL]; ring

/-- `n L^a = O(n L^e)` for `a ≤ e`. -/
theorem gr_isBigO_rpow_mono {a e : ℝ} (h : a ≤ e) :
    (fun n : ℕ => (n : ℝ) * Real.log n ^ a) =O[atTop]
      fun n : ℕ => (n : ℝ) * Real.log n ^ e := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hL := gr_one_le_log hn
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  gcongr

/-- `n L^a (log L)^k = O(n L^e)` for `a < e` and every real `k`. -/
theorem gr_isBigO_log_mul {a e : ℝ} (h : a < e) (k : ℝ) :
    (fun n : ℕ => (n : ℝ) * Real.log n ^ a * Real.log (Real.log n) ^ k) =O[atTop]
      fun n : ℕ => (n : ℝ) * Real.log n ^ e := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ho := (isLittleO_log_rpow_rpow_atTop k (sub_pos.2 h)).comp_tendsto hL
  have hm := (isBigO_refl (fun n : ℕ => (n : ℝ) * Real.log n ^ a) atTop).mul_isLittleO ho
  refine hm.isBigO.trans_eventuallyEq ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hL1 := gr_one_le_log hn
  simp only [Function.comp]
  rw [mul_assoc, ← Real.rpow_add (by linarith), add_sub_cancel]

end IntegerMultBounds.MathlibTM2.Cost
