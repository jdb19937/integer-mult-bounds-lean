module

public import IntegerMultBounds.Vendor.StrongPNT
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Primes in short windows below `t`

The CRT moduli of the near-one dimension route need `d` distinct primes in a window of
relative width `η = 1/(4d)` just below a bound `t`, with `d` at most a power of `log t`. This
file derives them from the strong prime number theorem
`ψ(x) = x + O(x exp(-c √(log x)))` (`Erdos970.Strong_PNT`, `IntegerMultBounds/Vendor`).

* `chebyshevPsi_eq`: the vendored Chebyshev function is Mathlib's `Chebyshev.psi`.
* `psi_strong_bound`: the strong PNT as an explicit bound on `Chebyshev.psi`.
* `theta_sub_le_card_mul_log`: the primes in `(a, b]` carry `θ b - θ a`, each at most `log b`.
* `primes_in_window`: for every real `B`, eventually in `t`, every `d ≥ 1` with
  `d ≤ (log t)^B` has at least `d` primes in `(⌊(1 - 2η) t⌋₊, ⌊(1 - η) t⌋₊]`, `η = 1/(4d)`.
* `mem_window`: such a prime `p` satisfies `(1 - 2η) t < p ≤ (1 - η) t`.
* `primes_in_window_two_pow`: the same below `t = 2^ℓ` for `d ≤ ℓ^B`, `B : ℕ`.

The proof counts primes through `θ`: the window carries
`θ((1-η)t) - θ((1-2η)t) ≥ ψ((1-η)t) - ψ((1-2η)t) - 2 √t log t`, the strong PNT at both ends
(both at least `t/2`) gives `ψ((1-η)t) - ψ((1-2η)t) ≥ ηt - 2Ct exp(-c √(log(t/2)))`, and every
prime of the window weighs at most `log t`. The error terms are below `ηt/4` each once
`exp(-c √(log t)) (log t)^B` is small and `(log t)^(B+1) ≤ √t/32`, and the count reaches `d`
once `8 (log t)^(2B+1) ≤ t`.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open Filter Real Asymptotics

/-! ### The vendored Chebyshev function -/

/-- The strong PNT's Chebyshev function is Mathlib's. -/
theorem chebyshevPsi_eq (x : ℝ) : Erdos970.ChebyshevPsi x = Chebyshev.psi x := by
  unfold Erdos970.ChebyshevPsi
  rcases lt_or_ge x 0 with hx | hx
  · have h1 : ⌊x + 1⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have h2 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [Chebyshev.psi, h1, h2]
  · rw [Nat.floor_add_one hx, Nat.range_succ_eq_Icc_zero, ← Chebyshev.psi_eq_sum_Icc]

theorem chebyshevPsi_eq_psi : Erdos970.ChebyshevPsi = Chebyshev.psi :=
  funext chebyshevPsi_eq

/-- The strong PNT as an explicit bound on `Chebyshev.psi`. -/
theorem psi_strong_bound : ∃ c > 0, ∃ C > 0, ∃ X : ℝ, ∀ x ≥ X,
    |Chebyshev.psi x - x| ≤ C * x * exp (-c * log x ^ ((1 : ℝ) / 2)) := by
  obtain ⟨c, hc, hO⟩ := Erdos970.Strong_PNT
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨X, hX⟩ := eventually_atTop.mp hC
  refine ⟨c, hc, max C 1, by positivity, max X 0, fun x hx => ?_⟩
  have h := hX x (le_of_max_le_left hx)
  have hx0 : 0 ≤ x := le_of_max_le_right hx
  simp only [Pi.sub_apply, id_eq, chebyshevPsi_eq, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0,
    abs_of_pos (exp_pos _)] at h
  calc |Chebyshev.psi x - x| ≤ C * (x * exp (-c * log x ^ ((1 : ℝ) / 2))) := h
    _ ≤ max C 1 * (x * exp (-c * log x ^ ((1 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max C 1 * x * exp (-c * log x ^ ((1 : ℝ) / 2)) := by ring

/-! ### Counting primes through `θ` -/

/-- The primes in `(a, b]` carry `θ b - θ a`, each with weight at most `log b`. -/
theorem theta_sub_le_card_mul_log {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta b - Chebyshev.theta a ≤
      ((Finset.Ioc a b).filter Nat.Prime).card * log b := by
  have hsplit : Chebyshev.theta b = Chebyshev.theta a +
      ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, log p := by
    simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab).symm
  have hle : ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, log p ≤
      ((Finset.Ioc a b).filter Nat.Prime).card • log b := by
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    obtain ⟨hp, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hap, hpb⟩ := Finset.mem_Ioc.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le a).trans_lt hap
    exact log_le_log hp0 (by exact_mod_cast hpb)
  rw [nsmul_eq_mul] at hle
  linarith

/-! ### Eventual size conditions -/

/-- `log t ^ r` is eventually below any fixed multiple of `t ^ s`, `s > 0`. -/
theorem eventually_log_rpow_le (r : ℝ) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, log t ^ r ≤ ε * t ^ s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop r hs).bound hε, eventually_ge_atTop 0]
    with t ht ht0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg ht0 s)] at ht
  exact (le_abs_self _).trans ht

/-- The strong PNT error beats any power of `log t`. -/
theorem eventually_exp_mul_log_rpow_le {c : ℝ} (hc : 0 < c) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, exp (-c * log (t / 2) ^ ((1 : ℝ) / 2)) * log t ^ B ≤ ε := by
  set k := c / (2 : ℝ) ^ ((1 : ℝ) / 2)
  have hk : 0 < k := div_pos hc (rpow_pos_of_pos two_pos _)
  have hv : Tendsto (fun t : ℝ => log t ^ ((1 : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * B) k hk).comp hv
  filter_upwards [(tendsto_order.1 hh).2 ε hε, eventually_ge_atTop 4] with t ht ht4
  simp only [Function.comp_apply] at ht
  have hlog4 : log 4 ≤ log t := log_le_log (by norm_num) ht4
  have hlog4' : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlt : 0 ≤ log t := by linarith [Real.log_two_gt_d9]
  have hhalf : log t / 2 ≤ log (t / 2) := by
    rw [Real.log_div (by linarith) (by norm_num)]
    linarith
  have hroot : log t ^ ((1 : ℝ) / 2) / (2 : ℝ) ^ ((1 : ℝ) / 2) ≤
      log (t / 2) ^ ((1 : ℝ) / 2) := by
    rw [← div_rpow hlt (by norm_num)]
    exact rpow_le_rpow (by positivity) hhalf (by norm_num)
  have hexp : exp (-c * log (t / 2) ^ ((1 : ℝ) / 2)) ≤
      exp (-k * log t ^ ((1 : ℝ) / 2)) := by
    apply exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hroot hc.le
    have e : k * log t ^ ((1 : ℝ) / 2) =
        c * (log t ^ ((1 : ℝ) / 2) / (2 : ℝ) ^ ((1 : ℝ) / 2)) := by
      simp only [k]
      ring
    linarith
  have hpow : log t ^ B = (log t ^ ((1 : ℝ) / 2)) ^ (2 * B) := by
    rw [← rpow_mul hlt]
    congr 1
    ring
  calc exp (-c * log (t / 2) ^ ((1 : ℝ) / 2)) * log t ^ B
      ≤ exp (-k * log t ^ ((1 : ℝ) / 2)) * log t ^ B :=
        mul_le_mul_of_nonneg_right hexp (rpow_nonneg hlt B)
    _ = (log t ^ ((1 : ℝ) / 2)) ^ (2 * B) * exp (-k * log t ^ ((1 : ℝ) / 2)) := by
        rw [hpow, mul_comm]
    _ ≤ ε := ht.le

/-! ### The window -/

/-- A natural number in `(⌊lo⌋₊, ⌊hi⌋₊]` lies strictly above `lo` and at most at `hi`; at
`lo = (1 - 2η) t`, `hi = (1 - η) t` this is membership in the real window. -/
theorem mem_window {lo hi : ℝ} (hhi : 0 ≤ hi) {p : ℕ}
    (hp : p ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊) : lo < p ∧ (p : ℝ) ≤ hi := by
  obtain ⟨hlo, hhi'⟩ := Finset.mem_Ioc.mp hp
  refine ⟨?_, (Nat.le_floor_iff hhi).mp hhi'⟩
  rcases lt_or_ge lo 0 with h | h
  · exact h.trans_le (Nat.cast_nonneg p)
  · exact (Nat.floor_lt h).mp hlo

/-- **Primes in short windows.** For every real `B`, eventually in `t`, every `d ≥ 1` with
`d ≤ (log t)^B` has at least `d` primes `p` with `⌊(1 - 2η) t⌋₊ < p ≤ ⌊(1 - η) t⌋₊`,
`η = 1/(4d)`. -/
theorem primes_in_window (B : ℝ) :
    ∀ᶠ t : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ log t ^ B →
      d ≤ ((Finset.Ioc ⌊(1 - 1 / (2 * (d : ℝ))) * t⌋₊
        ⌊(1 - 1 / (4 * (d : ℝ))) * t⌋₊).filter Nat.Prime).card := by
  obtain ⟨c, hc, C, hC, X, hX⟩ := psi_strong_bound
  filter_upwards [eventually_ge_atTop (max (2 * X) 4),
    eventually_exp_mul_log_rpow_le hc B (by positivity : (0 : ℝ) < 1 / (32 * C)),
    eventually_log_rpow_le (B + 1) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 32),
    eventually_log_rpow_le (2 * B + 1) one_pos (by norm_num : (0 : ℝ) < 1 / 8)]
    with t ht hA hB hC8 d hd hdB
  have ht4 : 4 ≤ t := le_of_max_le_right ht
  have htX : X ≤ t / 2 := by linarith [le_max_left (2 * X) 4]
  have ht0 : 0 < t := by linarith
  -- `log t ≥ 1`
  have hlog4 : log 4 ≤ log t := log_le_log (by norm_num) ht4
  have hlog4' : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlt1 : 1 ≤ log t := by linarith [Real.log_two_gt_d9]
  have hlt0 : 0 < log t := by linarith
  set D : ℝ := (d : ℝ) with hDdef
  have hD1 : 1 ≤ D := by rw [hDdef]; exact_mod_cast hd
  have hD0 : 0 < D := by linarith
  set x₁ := (1 - 1 / (4 * D)) * t with hx₁
  set x₂ := (1 - 1 / (2 * D)) * t with hx₂
  have hq1 : 1 / (4 * D) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq2 : 1 / (2 * D) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq0 : 0 < 1 / (4 * D) := by positivity
  have hx₂half : t / 2 ≤ x₂ := by
    have := mul_le_mul_of_nonneg_right hq2 ht0.le
    rw [hx₂]; linarith
  have hx₁t : x₁ ≤ t := by
    have := mul_le_mul_of_nonneg_right hq0.le ht0.le
    rw [hx₁]; linarith
  have hx₁₂ : x₁ - x₂ = t / (4 * D) := by
    rw [hx₁, hx₂]; field_simp; ring
  have hx₂₁ : x₂ ≤ x₁ := by
    have : 0 < t / (4 * D) := by positivity
    linarith
  -- the PNT error at both ends is at most `C t E₀`
  set E₀ := exp (-c * log (t / 2) ^ ((1 : ℝ) / 2)) with hE₀
  have hE (x : ℝ) (hx : t / 2 ≤ x) : exp (-c * log x ^ ((1 : ℝ) / 2)) ≤ E₀ := by
    apply exp_le_exp.mpr
    have h2 : 0 ≤ log (t / 2) := log_nonneg (by linarith)
    have hm : log (t / 2) ≤ log x := log_le_log (by linarith) hx
    have := mul_le_mul_of_nonneg_left (rpow_le_rpow h2 hm (by norm_num : (0 : ℝ) ≤ 1 / 2)) hc.le
    linarith
  have hψ₁ : x₁ - C * t * E₀ ≤ Chebyshev.psi x₁ := by
    have h := hX x₁ (by linarith)
    have hb : C * x₁ * exp (-c * log x₁ ^ ((1 : ℝ) / 2)) ≤ C * t * E₀ := by
      have h1 := hE x₁ (by linarith)
      have hx₁0 : 0 ≤ x₁ := by linarith
      calc C * x₁ * exp (-c * log x₁ ^ ((1 : ℝ) / 2)) ≤ C * t * exp (-c * log x₁ ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx₁t hC.le) (exp_pos _).le
        _ ≤ C * t * E₀ := mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [neg_abs_le (Chebyshev.psi x₁ - x₁)]
  have hψ₂ : Chebyshev.psi x₂ ≤ x₂ + C * t * E₀ := by
    have h := hX x₂ (by linarith)
    have hb : C * x₂ * exp (-c * log x₂ ^ ((1 : ℝ) / 2)) ≤ C * t * E₀ := by
      have h1 := hE x₂ hx₂half
      have hx₂0 : 0 ≤ x₂ := by linarith
      calc C * x₂ * exp (-c * log x₂ ^ ((1 : ℝ) / 2)) ≤ C * t * exp (-c * log x₂ ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC.le) (exp_pos _).le
        _ ≤ C * t * E₀ := mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [le_abs_self (Chebyshev.psi x₂ - x₂)]
  -- from `ψ` to `θ`
  have hθ₁ : Chebyshev.psi x₁ - 2 * √t * log t ≤ Chebyshev.theta x₁ := by
    have h := Chebyshev.psi_sub_theta_le (x := x₁) (by linarith)
    have hs : √x₁ ≤ √t := Real.sqrt_le_sqrt hx₁t
    have hl : log x₁ ≤ log t := log_le_log (by linarith) hx₁t
    have hl0 : 0 ≤ log x₁ := log_nonneg (by linarith)
    have : 2 * √x₁ * log x₁ ≤ 2 * √t * log t := by
      have := mul_le_mul hs hl hl0 (Real.sqrt_nonneg t)
      linarith
    linarith
  have hθ₂ : Chebyshev.theta x₂ ≤ Chebyshev.psi x₂ := Chebyshev.theta_le_psi x₂
  -- the three size conditions at `d`
  have hlB : D ≤ log t ^ B := hdB
  have hA' : 2 * C * t * E₀ ≤ t / (16 * D) := by
    have h1 : 32 * C * E₀ * D ≤ 1 := by
      have hE0 : 0 ≤ E₀ := (exp_pos _).le
      have := mul_le_mul_of_nonneg_left hlB (by positivity : 0 ≤ 32 * C * E₀)
      have hA2 : 32 * C * (E₀ * log t ^ B) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 32 * C)
        rwa [show 32 * C * (1 / (32 * C)) = 1 by field_simp] at this
      linarith
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 ht0.le
    linarith
  have hB' : 2 * √t * log t ≤ t / (16 * D) := by
    have hsq : √t * √t = t := Real.mul_self_sqrt ht0.le
    have hpow : log t ^ (B + 1) = log t ^ B * log t := rpow_add_one hlt0.ne' B
    have h1 : 32 * (D * log t) ≤ √t := by
      have := mul_le_mul_of_nonneg_right hlB hlt0.le
      rw [← Real.sqrt_eq_rpow, hpow] at hB
      linarith
    rw [le_div_iff₀ (by positivity)]
    have hs0 : 0 ≤ √t := Real.sqrt_nonneg t
    have := mul_le_mul_of_nonneg_left h1 hs0
    linarith
  have hC' : D * log t ≤ t / (8 * D) := by
    have hpow : log t ^ (2 * B + 1) = (log t ^ B) ^ 2 * log t := by
      rw [rpow_add_one hlt0.ne', mul_comm 2 B, rpow_mul hlt0.le, Real.rpow_two]
    have hD2 : D ^ 2 ≤ (log t ^ B) ^ 2 := pow_le_pow_left₀ hD0.le hlB 2
    rw [rpow_one, hpow] at hC8
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hD2 hlt0.le
    linarith
  -- the count
  set a := ⌊x₂⌋₊
  set b := ⌊x₁⌋₊
  have hab : a ≤ b := Nat.floor_le_floor hx₂₁
  have hb1 : (1 : ℝ) ≤ b := by
    have : (1 : ℝ) ≤ x₁ := by linarith
    exact_mod_cast (Nat.one_le_floor_iff x₁).mpr this
  have hcount := theta_sub_le_card_mul_log hab
  rw [← Chebyshev.theta_eq_theta_coe_floor, ← Chebyshev.theta_eq_theta_coe_floor] at hcount
  have hlogb : log b ≤ log t := log_le_log (by linarith) ((Nat.floor_le (by linarith)).trans hx₁t)
  set N := ((Finset.Ioc a b).filter Nat.Prime).card
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hmain : D * log t ≤ N * log t := by
    have h1 : Chebyshev.theta x₁ - Chebyshev.theta x₂ ≤ N * log t :=
      hcount.trans (mul_le_mul_of_nonneg_left hlogb hN0)
    have h2 : t / (8 * D) ≤ Chebyshev.theta x₁ - Chebyshev.theta x₂ := by
      have e : t / (4 * D) - t / (16 * D) - t / (16 * D) = t / (8 * D) := by
        field_simp; ring
      linarith
    linarith
  have hDN : D ≤ N := le_of_mul_le_mul_right hmain hlt0
  rw [hDdef] at hDN
  exact_mod_cast hDN

/-- **Primes in short windows below `2^ℓ`.** For every natural `B`, eventually in `ℓ`, every
`d ≥ 1` with `d ≤ ℓ^B` has at least `d` primes `p` with
`⌊(1 - 2η) 2^ℓ⌋₊ < p ≤ ⌊(1 - η) 2^ℓ⌋₊`, `η = 1/(4d)`. -/
theorem primes_in_window_two_pow (B : ℕ) :
    ∀ᶠ ℓ : ℕ in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ ℓ ^ B →
      d ≤ ((Finset.Ioc ⌊(1 - 1 / (2 * (d : ℝ))) * 2 ^ ℓ⌋₊
        ⌊(1 - 1 / (4 * (d : ℝ))) * 2 ^ ℓ⌋₊).filter Nat.Prime).card := by
  have h2 : Tendsto (fun ℓ : ℕ => (2 : ℝ) ^ ℓ) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hlog2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hbig : ∀ᶠ ℓ : ℕ in atTop, 1 ≤ (ℓ : ℝ) * log 2 ^ ((B : ℝ) + 1) := by
    have hpos : 0 < log 2 ^ ((B : ℝ) + 1) := rpow_pos_of_pos hlog2 _
    filter_upwards [eventually_ge_atTop ⌈1 / log 2 ^ ((B : ℝ) + 1)⌉₊] with ℓ hℓ
    have := (Nat.ceil_le.mp hℓ)
    rw [div_le_iff₀ hpos] at this
    linarith
  filter_upwards [h2.eventually (primes_in_window ((B : ℝ) + 1)), hbig] with ℓ hℓ hℓ1
    d hd hdℓ
  refine hℓ d hd ?_
  have hl0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  rw [Real.log_pow, mul_rpow hl0 hlog2.le, rpow_add_one' hl0 (by positivity), rpow_natCast]
  have hd' : (d : ℝ) ≤ (ℓ : ℝ) ^ B := by exact_mod_cast hdℓ
  have hpowB : (0 : ℝ) ≤ (ℓ : ℝ) ^ B := pow_nonneg hl0 B
  calc (d : ℝ) ≤ (ℓ : ℝ) ^ B * 1 := by rw [mul_one]; exact hd'
    _ ≤ (ℓ : ℝ) ^ B * ((ℓ : ℝ) * log 2 ^ ((B : ℝ) + 1)) := mul_le_mul_of_nonneg_left hℓ1 hpowB
    _ = (ℓ : ℝ) ^ B * ℓ * log 2 ^ ((B : ℝ) + 1) := by ring

end IntegerMultBounds.Primes
