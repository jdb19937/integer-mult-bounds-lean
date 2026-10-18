module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import IntegerMultBounds.MathlibTM2.Balanced.Widths
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Parallel runtime sizes for the compact caller. Only the chunk changes; the established
executable sizes and their public total bounds remain untouched.

The chunk root is `Kroot = ⌊d^(7/8)⌋`. The chunk `K` is the uniform balanced width above it,
`min d (Balanced.unifWidth (ℓ - 1) Kroot)`: the `ℓ - 1` common slots of an axis split into
`⌊(ℓ - 1)/Kroot⌋` chunks of one width with a remainder below that count. For every `n`,
`Kroot ≤ K ≤ min d (2 Kroot)` (`Kroot_le_K`, `K_le_d`, `K_le_two_Kroot`); under `Big` the width
is exactly `(ℓ - 1) / ⌊(ℓ - 1)/Kroot⌋` (`K_eq_unif`) and the remainder is below
`(ℓ - 1)/Kroot` (`mod_K_succ_le`). -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactSizes
open Filter
noncomputable section

abbrev d := Sizes.d
abbrev p := Sizes.p
abbrev ℓ := Sizes.ℓ
abbrev r := Sizes.r
abbrev t := Sizes.t

/-- Root degree of the chunk root `Kroot = ⌊d^(7/8)⌋`, the eighth root of `d^7`. -/
def cExp : ℕ := 2^3
noncomputable def cParam : ℝ := 7/(cExp : ℝ)
/-- The chunk root `⌊d^(7/8)⌋`. -/
def Kroot (n : ℕ) : ℕ := Sizes.iroot cExp (d n^7)
/-- The chunk: the uniform balanced width of the `ℓ - 1` common slots above the root. -/
def K (n : ℕ) : ℕ := min (d n) (Balanced.unifWidth (ℓ n - 1) (Kroot n))

theorem cExp_eq : cExp=8 := by norm_num [cExp]
theorem cExp_ne : cExp≠0 := by norm_num [cExp]
theorem cParam_eq : cParam=7/(2^3 : ℝ) := by norm_num [cParam,cExp]
theorem cParam_pos : 0<cParam := by norm_num [cParam,cExp]

theorem Kroot_pow_le (n : ℕ) : Kroot n^cExp≤d n^7 := Sizes.iroot_pow_le cExp_ne _
theorem d_lt_Kroot_succ_pow (n : ℕ) : d n^7<(Kroot n+1)^cExp := Sizes.lt_succ_iroot_pow cExp_ne _
theorem le_Kroot_iff {n k : ℕ} : k≤Kroot n ↔ k^cExp≤d n^7 := Sizes.le_iroot_iff cExp_ne
theorem Kroot_le_d (n : ℕ) : Kroot n≤d n := by
  by_contra h
  have h1 : (d n+1)^cExp≤Kroot n^cExp := Nat.pow_le_pow_left (by omega) _
  have h3 : d n^7<(d n+1)^cExp := by
    rw [cExp_eq]
    calc d n^7<(d n+1)^7 := Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by norm_num)
      _ ≤ (d n+1)^8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by norm_num)
  exact absurd (h1.trans (Kroot_pow_le n)) (not_le.mpr h3)
theorem Kroot_eq_floor (n : ℕ) : Kroot n=⌊(d n : ℝ)^cParam⌋₊ := by
  rw [Kroot, Sizes.iroot_eq_floor cExp_ne, Nat.cast_pow,
    ←Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  congr 2

theorem Kroot_le_K (n : ℕ) : Kroot n≤K n :=
  le_min (Kroot_le_d n) (Balanced.le_unifWidth _ _)
theorem K_le_d (n : ℕ) : K n≤d n := min_le_left _ _
theorem K_le_two_Kroot (n : ℕ) : K n≤2*Kroot n :=
  (min_le_right _ _).trans (Balanced.unifWidth_le_two_mul _ _)
theorem one_le_Kroot {n : ℕ} (hn : 2≤n) : 1≤Kroot n :=
  Sizes.one_le_iroot cExp_ne (Nat.one_le_pow _ _ (Sizes.one_le_d hn))
theorem one_le_K {n : ℕ} (hn : 2≤n) : 1≤K n := (one_le_Kroot hn).trans (Kroot_le_K n)

/-- Increasing the exponent from `2^-32` to `7/8` increases the chunk. -/
theorem old_K_le_Kroot (n : ℕ) : Sizes.K n≤Kroot n := by
  apply le_Kroot_iff.mpr
  rcases Nat.eq_zero_or_pos (Sizes.K n) with h | h
  · rw [h,zero_pow cExp_ne]; exact Nat.zero_le _
  · exact ((Nat.pow_le_pow_right h (by norm_num [cExp,Sizes.cExp])).trans
      (Sizes.K_pow_le n)).trans (Nat.le_self_pow (by norm_num) _)

theorem old_K_le_K (n : ℕ) : Sizes.K n≤K n := (old_K_le_Kroot n).trans (Kroot_le_K n)

theorem tendsto_K : Tendsto K atTop atTop :=
  tendsto_atTop.2 fun M => (tendsto_atTop.1 Sizes.tendsto_K M).mono fun n h => h.trans (old_K_le_K n)

/-- Under `Big`, twice the root is below the dimension: `(2 Kroot)^8 ≤ 2^8 d^7 < d^8`. -/
theorem two_Kroot_lt_d {n : ℕ} (h : Sizes.Big n) : 2*Kroot n<d n := by
  have hd : 257≤d n := by have := h.2; change 257≤Sizes.d n; omega
  have hp := Kroot_pow_le n
  rw [cExp_eq] at hp
  by_contra hc
  have h8 : d n^8≤(2*Kroot n)^8 := Nat.pow_le_pow_left (by omega) 8
  have e : (2*Kroot n)^8=256*Kroot n^8 := by ring
  have h2 : 257*d n^7≤d n*d n^7 := Nat.mul_le_mul_right _ hd
  have e8 : d n^8=d n*d n^7 := by ring
  have hpos : 0<d n^7 := Nat.pow_pos (by omega)
  omega

/-- Under `Big`, twice the root is below the axis length: `(2 Kroot)^8 ≤ 256 d^7 < ℓ^8`
(`Sizes.Big.chunk_room`). -/
theorem two_Kroot_lt_ℓ {n : ℕ} (h : Sizes.Big n) : 2*Kroot n<ℓ n := by
  have hroom : 256*Sizes.d n^7<Sizes.ℓ n^8 := h.chunk_room
  have hp := Kroot_pow_le n
  rw [cExp_eq] at hp
  change 2*Kroot n<Sizes.ℓ n
  by_contra hc
  have h8 : Sizes.ℓ n^8≤(2*Kroot n)^8 := Nat.pow_le_pow_left (by omega) 8
  have e : (2*Kroot n)^8=256*Kroot n^8 := by ring
  have hd : Kroot n^8≤Sizes.d n^7 := hp
  omega

/-- Under `Big` the chunk is the uniform width `(ℓ - 1) / ⌊(ℓ - 1)/Kroot⌋`. -/
theorem K_eq_unif {n : ℕ} (h : Sizes.Big n) :
    K n=(ℓ n-1)/((ℓ n-1)/Kroot n) := by
  have h1 : 1≤Kroot n := one_le_Kroot h.1
  have h2 : Kroot n≤ℓ n-1 := by have := two_Kroot_lt_ℓ h; omega
  have hw := Balanced.unifWidth_le_two_mul (ℓ n-1) (Kroot n)
  have hd := (two_Kroot_lt_d h).le
  unfold K
  rw [min_eq_right (hw.trans hd), Balanced.unifWidth_eq (by omega) h2]

/-- **The remainder of the chunk.** Under `Big` the `ℓ - 1` common slots of an axis leave
fewer than `(ℓ - 1)/Kroot` slots below the chunks. -/
theorem mod_K_succ_le {n : ℕ} (h : Sizes.Big n) : (ℓ n-1)%K n+1≤(ℓ n-1)/Kroot n := by
  have h1 : 1≤Kroot n := one_le_Kroot h.1
  have h2 : Kroot n≤ℓ n-1 := by have := two_Kroot_lt_ℓ h; omega
  have hlt := Balanced.mod_unifWidth_lt (by omega : 0<Kroot n) h2
  have hK : K n=Balanced.unifWidth (ℓ n-1) (Kroot n) := by
    rw [K_eq_unif h, Balanced.unifWidth_eq (by omega) h2]
  rw [hK]
  omega

/-- Existing layout axis bounds remain valid for the larger chunk: `K ≤ 2 Kroot < ℓ`. -/
theorem K_succ_le_ℓ {n : ℕ} (h : Sizes.Big n) : K n+1≤ℓ n := by
  have := K_le_two_Kroot n
  have := two_Kroot_lt_ℓ h
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
  filter_upwards [Sizes.eventually_big] with n h
  have h1 : 2*Kroot n<Sizes.d n := two_Kroot_lt_d h
  have h2 := K_le_two_Kroot n
  have h3 := one_le_Kroot h.1
  change K n≤Sizes.d n-1
  omega

end
end IntegerMultBounds.MathlibTM2.Mult.CompactSizes
