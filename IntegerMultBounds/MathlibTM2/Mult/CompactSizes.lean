module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Parallel runtime sizes for the compact caller. Only the chunk root changes;
the established executable sizes and their public total bounds remain untouched. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactSizes
open Filter
noncomputable section

abbrev d := Sizes.d
abbrev p := Sizes.p
abbrev ℓ := Sizes.ℓ
abbrev r := Sizes.r
abbrev t := Sizes.t

/-- Fourth-root chunk, corresponding to the proposed compact exponent `1/4`. -/
def cExp : ℕ := 2^2
noncomputable def cParam : ℝ := (cExp : ℝ)⁻¹
def K (n : ℕ) : ℕ := Sizes.iroot cExp (d n)

theorem cExp_eq : cExp=4 := by norm_num [cExp]
theorem cExp_ne : cExp≠0 := by norm_num [cExp]
theorem cParam_eq : cParam=(2^2 : ℝ)⁻¹ := by norm_num [cParam,cExp]
theorem cParam_pos : 0<cParam := by norm_num [cParam,cExp]

theorem K_pow_le (n : ℕ) : K n^cExp≤d n := Sizes.iroot_pow_le cExp_ne _
theorem d_lt_K_succ_pow (n : ℕ) : d n<(K n+1)^cExp := Sizes.lt_succ_iroot_pow cExp_ne _
theorem le_K_iff {n k : ℕ} : k≤K n ↔ k^cExp≤d n := Sizes.le_iroot_iff cExp_ne
theorem K_le_d (n : ℕ) : K n≤d n := Sizes.iroot_le_self cExp_ne _
theorem one_le_K {n : ℕ} (hn : 2≤n) : 1≤K n :=
  Sizes.one_le_iroot cExp_ne (Sizes.one_le_d hn)
theorem K_eq_floor (n : ℕ) : K n=⌊(d n : ℝ)^cParam⌋₊ := Sizes.iroot_eq_floor cExp_ne _

/-- Increasing the exponent from `2^-32` to `2^-2` increases the chunk. -/
theorem old_K_le_K (n : ℕ) : Sizes.K n≤K n := by
  apply le_K_iff.mpr
  rcases Nat.eq_zero_or_pos (Sizes.K n) with h | h
  · rw [h,zero_pow cExp_ne]; exact Nat.zero_le _
  · exact (Nat.pow_le_pow_right h (by norm_num [cExp,Sizes.cExp])).trans (Sizes.K_pow_le n)

theorem tendsto_K : Tendsto K atTop atTop :=
  tendsto_atTop.2 fun M => (tendsto_atTop.1 Sizes.tendsto_K M).mono fun n h => h.trans (old_K_le_K n)

/-- Existing layout axis bounds remain valid for the larger chunk. -/
theorem K_succ_le_ℓ {n : ℕ} (h : Sizes.Big n) : K n+1≤ℓ n := by
  have hk : K n≤Sizes.d n := K_le_d n
  have hl := h.d_le_ℓ
  change K n+1≤Sizes.ℓ n
  omega

/-- Any fixed multiple of the precision logarithm is eventually paid. -/
theorem eventually_clog_p_le_K (C : ℕ) : ∀ᶠ n in atTop, C*Nat.clog 2 (p n)≤K n :=
  (Sizes.eventually_clog_p_le_K C).mono fun n h => h.trans (old_K_le_K n)

/-- More generally, a fixed affine logarithmic allowance is eventually paid. -/
theorem eventually_affine_clog_p_le_K (C B : ℕ) :
    ∀ᶠ n in atTop, C*Nat.clog 2 (p n)+B≤K n := by
  filter_upwards [eventually_ge_atTop 2,eventually_clog_p_le_K (C+B)] with n hn h
  have hp : 2≤p n := by
    have := Sizes.one_le_b hn
    unfold p Sizes.p
    omega
  have hl : 1≤Nat.clog 2 (p n) := Nat.clog_pos (by decide) hp
  nlinarith

/-- The persistent original-input guard used by the compact bootstrap. -/
def guard (n : ℕ) : ℕ := 4*Nat.clog 2 (p n)+6

theorem eventually_guard_le_K (C B : ℕ) : ∀ᶠ n in atTop, C*guard n+B≤K n := by
  filter_upwards [eventually_affine_clog_p_le_K (4*C) (6*C+B)] with n h
  unfold guard
  nlinarith

/-- In particular the full two-sided guard allowance fits a chunk. -/
theorem eventually_guard_room : ∀ᶠ n in atTop, 8*Nat.clog 2 (p n)+16≤K n :=
  eventually_affine_clog_p_le_K 8 16

/-- The new chunk still fits the actual initial `d-1` transform dimension. -/
theorem eventually_K_le_predecessor : ∀ᶠ n in atTop, K n≤d n-1 := by
  filter_upwards [tendsto_K.eventually (eventually_ge_atTop 2)] with n hK
  have hpow : K n^2≤K n^cExp := Nat.pow_le_pow_right (by omega) (by norm_num [cExp])
  have hd := hpow.trans (K_pow_le n)
  have hlt : K n<d n := by nlinarith
  omega

/-- Layout block width eventually dominates any fixed multiple of the chunk. -/
theorem eventually_mul_K_le_ℓ (C : ℕ) : ∀ᶠ n in atTop, C*K n≤ℓ n := by
  filter_upwards [Sizes.eventually_big, tendsto_atTop.1 Sizes.tendsto_d ((2*C)^4)] with n h hC
  have h1 := h.mul_sq_le hC
  have h2 := h.b_le_two_dℓ
  have h3 : C*K n≤C*d n := Nat.mul_le_mul_left _ (K_le_d n)
  have hd := h.one_le_d
  have h4 : d n*(2*(C*d n))≤d n*(2*ℓ n) := by
    calc d n*(2*(C*d n)) = 2*C*d n^2 := by ring
      _ ≤ 2*(d n*ℓ n) := h1.trans h2
      _ = d n*(2*ℓ n) := by ring
  have h5 : C*d n≤ℓ n := by
    have := Nat.le_of_mul_le_mul_left h4 hd
    omega
  exact h3.trans h5

end
end IntegerMultBounds.MathlibTM2.Mult.CompactSizes
