module

public import IntegerMultBounds.MathlibTM2.Cost.CompactGrowth
public import IntegerMultBounds.MathlibTM2.Cost.Total
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Actual compact convolution and unchanged auxiliary stage exponents at the stronger saving.
These analytic envelopes still require the executable total-cost matching theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactTotal
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Mult.Sizes hiding K
noncomputable section

/-- Every shared stage margin covers the proposed compact saving. -/
theorem exp_facts :
    0≤1-kappa ∧ epsilon≤1-kappa ∧
      epsilon*(1-Parameters.tau)+Parameters.tau≤1-kappa ∧
      epsilon+epsilon*Mult.Sizes.cParam*(1/2)+(1/2+totDelta)≤1-kappa ∧
      1-epsilon*(1-lam')≤1-kappa ∧
      1-epsilon+epsilon*Mult.Sizes.cParam≤1-kappa ∧ totDelta≤1-kappa := by
  rw [epsilon_eq, Mult.Sizes.cParam_eq]
  norm_num [kappa,lam',CompactInterim.kappa,CompactInterim.lam',Parameters.tau,totDelta]

/-- The convolution envelope with the uniform balanced chunk and the new layer exponent: the
prefix costs `T p d`, the chunk exchanges `T p · p K^(τ-1)`, the layer `T p ℓ d^λ'`. -/
def conv (n : ℕ) : ℝ :=
  (T n:ℝ)*p n*((d n:ℝ)+(p n:ℝ)*(K n:ℝ)^(Parameters.tau-1)+
    (ℓ n:ℝ)*(d n:ℝ)^lam'+grLogLog ((r n:ℝ)*p n))

variable {n : ℕ}

/-- **The prefix is paid by the chunk exchanges.** Under `Big` the prefix of an axis holds at
most `(ℓ - 1)/Kroot` slots (`CompactSizes.mod_K_succ_le`); with `3 d ℓ ≤ p`, `K ≤ 2 Kroot` and
`K^(τ-1) ≥ 1/K`, the `d` axes give `d (b + 1) ≤ p K^(τ-1)`. -/
theorem prefix_le (h : Big n) :
    (d n:ℝ)*((((ℓ n-1)%K n : ℕ) : ℝ)+1)≤(p n:ℝ)*(K n:ℝ)^(Parameters.tau-1) := by
  have hq := Mult.CompactSizes.mod_K_succ_le h
  have hK2 := Mult.CompactSizes.K_le_two_Kroot n
  have hK1 : 1≤K n := Mult.CompactSizes.one_le_K h.1
  have h3 : 3*d n*ℓ n≤p n := h.ℓ_bounds.2
  have hn1 : ((ℓ n-1)%K n+1)*Mult.CompactSizes.Kroot n≤ℓ n :=
    ((Nat.mul_le_mul_right _ hq).trans (Nat.div_mul_le_self _ _)).trans (Nat.sub_le _ _)
  have hn2 : 3*(d n*((ℓ n-1)%K n+1))*K n≤2*p n := by
    calc 3*(d n*((ℓ n-1)%K n+1))*K n≤3*(d n*((ℓ n-1)%K n+1))*(2*Mult.CompactSizes.Kroot n) :=
          Nat.mul_le_mul_left _ hK2
      _ = 2*(3*d n*(((ℓ n-1)%K n+1)*Mult.CompactSizes.Kroot n)) := by ring
      _ ≤ 2*(3*d n*ℓ n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hn1)
      _ ≤ 2*p n := Nat.mul_le_mul_left _ h3
  have hK0 : (0:ℝ)<K n := by exact_mod_cast hK1
  have hX : (d n:ℝ)*((((ℓ n-1)%K n : ℕ) : ℝ)+1)*K n≤p n := by
    have : ((3*(d n*((ℓ n-1)%K n+1))*K n : ℕ) : ℝ)≤((2*p n : ℕ) : ℝ) := by exact_mod_cast hn2
    push_cast at this
    have hp0 : (0:ℝ)≤p n := Nat.cast_nonneg _
    nlinarith
  have hKτ : (K n:ℝ)^(-1:ℝ)≤(K n:ℝ)^(Parameters.tau-1) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK1) (by linarith [tot_tau_nonneg])
  rw [Real.rpow_neg_one] at hKτ
  have hdiv : (d n:ℝ)*((((ℓ n-1)%K n : ℕ) : ℝ)+1)≤(p n:ℝ)*(K n:ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hK0]
    exact hX
  exact hdiv.trans (mul_le_mul_of_nonneg_left hKτ (Nat.cast_nonneg _))

theorem mp_le (h : Big n) :
    (T n : ℝ) * totMp n ≤ 512 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
  obtain ⟨-, -, -, -, -, -, hδ⟩ := exp_facts
  have hB1 := tot_one_le_b h
  have h1 : (p n : ℝ) ^ totDelta ≤ 6 * (b n : ℝ) ^ (1 - kappa) :=
    gr_le_rpow_of_le hB1 (by norm_num) (gr_p_rpow_le n (by norm_num [totDelta])) hδ
  have h2 := gr_Tp_le h.1
  rw [tot_mp_eq h]
  calc (T n : ℝ) * ((p n : ℝ) * (p n : ℝ) ^ totDelta) = (T n * p n) * (p n : ℝ) ^ totDelta := by
        ring
    _ ≤ (48 * n) * (6 * (b n : ℝ) ^ (1 - kappa)) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = 288 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by ring
    _ ≤ 512 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)


/-- The resampling envelope with the logarithmic band width `α ≤ 4 B^{εc/2}` (`c = 2^-32`),
given `⌈log₂ p⌉ ≤ K` for the legacy chunk `K = ⌊d^c⌋`. -/
theorem resamp_le (h : Big n) (hK : 1 ≤ Mult.Sizes.K n)
    (hclog : Nat.clog 2 (p n) ≤ Mult.Sizes.K n) :
    totResamp n ≤ 8192 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
  obtain ⟨-, -, -, hres, -, -, -⟩ := exp_facts
  have hB1 := tot_one_le_b h
  have hB : (0 : ℝ) < b n := by linarith
  have hα : (alpha n : ℝ) ≤ 4 * (b n : ℝ) ^ (epsilon * Mult.Sizes.cParam * (1 / 2)) :=
    gr_alpha_le_K hK hclog
  have hd : (d n : ℝ) ≤ 1 * (b n : ℝ) ^ epsilon := by rw [one_mul]; exact gr_d_le_rpow n
  have hdα := gr_mul_le hB (Nat.cast_nonneg _) (by norm_num) hd hα
  have hp := gr_mul_le hB (by positivity) (by norm_num)
    (gr_p_rpow_le n (x := 1 / 2) (by norm_num))
    (gr_p_rpow_le n (x := totDelta) (by norm_num [totDelta]))
  have h3 := gr_mul_le hB (by positivity) (by norm_num) hdα hp
  have h4 := gr_le_rpow_of_le hB1 (by norm_num) h3 hres
  have hTp := gr_Tp_le h.1
  rw [totResamp, tot_mp_eq h]
  calc (d n : ℝ) * T n * (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n * ((p n : ℝ) * (p n : ℝ) ^ totDelta) =
      ((T n : ℝ) * p n) * (((d n : ℝ) * alpha n) *
        ((p n : ℝ) ^ (1 / 2 : ℝ) * (p n : ℝ) ^ totDelta)) := by ring
    _ ≤ (48 * n) * (1 * 4 * (6 * 6) * (b n : ℝ) ^ (1 - kappa)) :=
        mul_le_mul hTp h4 (by positivity) (by positivity)
    _ = 6912 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by ring
    _ ≤ 8192 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)


theorem conv_inner_nonneg (h : Big n) :
    0 ≤ (d n : ℝ) + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) +
      (ℓ n : ℝ) * (d n : ℝ) ^ lam' + grLogLog ((r n : ℝ) * p n) := by
  have h1 : 0 ≤ grLogLog ((r n : ℝ) * p n) := by
    have hr : (1 : ℝ) ≤ r n := by rw [gr_r_eq]; exact one_le_pow₀ (by norm_num)
    have hp : (1 : ℝ) ≤ p n := by
      have := h.thirteen_le_p; exact_mod_cast (show 1 ≤ p n by omega)
    have := gr_one_le_logLog (one_le_mul_of_one_le_of_one_le hr hp)
    linarith
  have h2 : (0 : ℝ) ≤ (d n : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h4 : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ lam' :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

/-- `T p (d + p K^{τ-1} + ℓ d^{λ'} + grLogLog (r p)) ≤ 4096 n B^{1-κ}`, given `K ≥ 1` and
`log₂ p` below the legacy chunk `⌊d^c⌋` (`c = 2^-32`). -/
theorem conv_le (h : Big n) (hK : 1 ≤ K n) (hlogp : Real.logb 2 (p n) ≤ Mult.Sizes.K n) :
    conv n ≤ 4096 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
  obtain ⟨-, he, -, -, hlam, hll, -⟩ := exp_facts
  have hB1 := tot_one_le_b h
  have hB : (0 : ℝ) < b n := by linarith
  have hD : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK
  have hτ0 := tot_tau_nonneg
  have hτ1 := tot_tau_le_one
  -- `d ≤ B^ε`
  have i1 : (d n : ℝ) ≤ (b n : ℝ) ^ (1 - kappa) :=
    (gr_d_le_rpow n).trans (Real.rpow_le_rpow_of_exponent_le hB1 he)
  -- `p K^{τ-1} = 6 B / K^{1-τ} ≤ 24 B^{1-κ}`
  have i2 : (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) ≤ 24 * (b n : ℝ) ^ (1 - kappa) := by
    have hKτ : 0 < (K n : ℝ) ^ (1 - Parameters.tau) := Real.rpow_pos_of_pos hK0 _
    have e : (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) =
        6 * ((b n : ℝ) / (K n : ℝ) ^ (1 - Parameters.tau)) := by
      rw [show Parameters.tau - 1 = -(1 - Parameters.tau) by ring, Real.rpow_neg hK0.le, gr_p_eq]
      ring
    have hk : (b n : ℝ) ^ kappa ≤ 4 * (K n : ℝ) ^ (1 - Parameters.tau) :=
      (Real.rpow_le_rpow_of_exponent_le hB1
        (show kappa≤epsilon*(1-Parameters.tau) by
          rw [epsilon_eq]
          norm_num [kappa,CompactInterim.kappa,Parameters.tau])).trans
        (compact_rpow_le_four_K_rpow hK (a:=1-Parameters.tau)
          (by linarith) (by linarith))
    have := gr_div_le hB hKτ hk
    rw [e]; linarith
  -- `ℓ d^{λ'} = d ℓ / d^{1-λ'} ≤ 2B / d^{1-λ'} ≤ 4 B^{1-ε(1-λ')}`
  have i3 : (ℓ n : ℝ) * (d n : ℝ) ^ lam' ≤ 4 * (b n : ℝ) ^ (1 - kappa) := by
    have hl0 : 0 ≤ 1 - lam' := by have := (show lam'<1 by norm_num [CompactInterim.lam']); linarith
    have hl1 : 1 - lam' ≤ 1 := by
      have : 0 ≤ lam' := by norm_num [lam',CompactInterim.lam']
      linarith
    have hDl : 0 < (d n : ℝ) ^ (1 - lam') := Real.rpow_pos_of_pos hD _
    have e : (ℓ n : ℝ) * (d n : ℝ) ^ lam' =
        ((d n : ℝ) * ℓ n) / (d n : ℝ) ^ (1 - lam') := by
      have e0 := Real.rpow_sub hD 1 (1 - lam')
      rw [sub_sub_cancel, Real.rpow_one] at e0
      rw [e0]
      ring
    have h1 : ((d n : ℝ) * ℓ n) / (d n : ℝ) ^ (1 - lam') ≤
        2 * ((b n : ℝ) / (d n : ℝ) ^ (1 - lam')) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (gr_dℓ_le h) hDl.le
    have h2 := gr_div_le hB hDl (gr_rpow_le_two_d_rpow h.one_le_d hl0 hl1)
    have h3 := gr_le_rpow_of_le hB1 (by norm_num) h2 hlam
    rw [e]; linarith
  -- `Λ = log₂ (r p) = ℓ + log₂ p ≤ 2ℓ`, so `Λ + 1 ≤ 9 B^{1-ε}` and
  -- `log₂ (Λ + 1) + 1 ≤ log₂ (4p) + 1 ≤ K + 3 ≤ 4 B^{εc}` for the legacy chunk
  have i4 : grLogLog ((r n : ℝ) * p n) ≤ 45 * (b n : ℝ) ^ (1 - kappa) := by
    have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
    have hp1' : (1 : ℝ) ≤ p n := by exact_mod_cast hp1
    have hΛ := gr_logb_rp hp1
    have hlp0 : 0 ≤ Real.logb 2 (p n) := gr_logb_nonneg hp1'
    have hKℓ : (Mult.Sizes.K n : ℝ) + 1 ≤ ℓ n := by exact_mod_cast h.K_succ_le_ℓ
    have hℓp : (ℓ n : ℝ) ≤ p n := by
      have h1 : 3 * d n * ℓ n ≤ p n := h.ℓ_bounds.2
      have h2 : ℓ n ≤ 3 * d n * ℓ n := by
        have := h.one_le_d
        nlinarith
      exact_mod_cast h2.trans h1
    unfold grLogLog
    set Λ := Real.logb 2 ((r n : ℝ) * p n) with hΛ_def
    have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
    have hΛℓ : Λ ≤ 2 * ℓ n := by rw [hΛ]; linarith
    have hBe : (1 : ℝ) ≤ (b n : ℝ) ^ (1 - epsilon) :=
      Real.one_le_rpow hB1 (by linarith [gr_epsilon_le_one])
    have f1 : Λ + 1 ≤ 9 * (b n : ℝ) ^ (1 - epsilon) := by
      have := gr_ℓ_le_rpow h
      linarith
    have h4p : Real.logb 2 (4 * p n) = 2 + Real.logb 2 (p n) := by
      rw [Real.logb_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.logb_pow, Real.logb_self_eq_one one_lt_two]
      norm_num
    have hlΛ : Real.logb 2 (Λ + 1) ≤ Real.logb 2 (4 * p n) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
    have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hK
    have f2 : Real.logb 2 (Λ + 1) + 1 ≤ 5 * (b n : ℝ) ^ (epsilon * Mult.Sizes.cParam) := by
      have := gr_K_le_rpow n
      have : (1 : ℝ) ≤ (b n : ℝ) ^ (epsilon * Mult.Sizes.cParam) :=
        Real.one_le_rpow hB1 (mul_nonneg (by rw [epsilon_eq]; norm_num) gr_cParam_pos.le)
      linarith
    have f12 := gr_mul_le hB (by linarith [gr_logb_nonneg (show (1 : ℝ) ≤ Λ + 1 by linarith)])
      (by norm_num) f1 f2
    have := gr_le_rpow_of_le hB1 (by norm_num) f12 hll
    linarith
  have hsum : (d n : ℝ) + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) +
      (ℓ n : ℝ) * (d n : ℝ) ^ lam' + grLogLog ((r n : ℝ) * p n) ≤
        74 * (b n : ℝ) ^ (1 - kappa) := by linarith
  have hTp := gr_Tp_le h.1
  unfold conv
  calc _ ≤ (48 * n) * (74 * (b n : ℝ) ^ (1 - kappa)) :=
        mul_le_mul hTp hsum (conv_inner_nonneg h) (by positivity)
    _ = 3552 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by ring
    _ ≤ 4096 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem conv_nonneg (h : Big n) : 0 ≤ conv n :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (conv_inner_nonneg h)


end
end IntegerMultBounds.MathlibTM2.Cost.CompactTotal
