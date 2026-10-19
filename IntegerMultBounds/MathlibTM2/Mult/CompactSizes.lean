module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import IntegerMultBounds.MathlibTM2.Balanced.Widths
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Parallel runtime sizes for the compact caller. Only the chunk changes; the established
executable sizes and their public total bounds remain untouched.

The chunk root is half the dimension, `Kroot = ⌈d/2⌉`. The chunk `K` is the uniform balanced
width above it, `min d (Balanced.unifWidth (ℓ - 1) Kroot)`: the `ℓ - 1` common slots of an axis
split into `⌊(ℓ - 1)/Kroot⌋` chunks of one width with a remainder below that count. For every
`n`, `Kroot ≤ K ≤ min d (2 Kroot)` and `d ≤ 2 Kroot` (`Kroot_le_K`, `K_le_d`, `K_le_two_Kroot`,
`d_le_two_Kroot`); under `Big` the width is exactly `(ℓ - 1) / ⌊(ℓ - 1)/Kroot⌋` (`K_eq_unif`),
the remainder is below `(ℓ - 1)/Kroot` (`mod_K_succ_le`) and `K ≤ d - 1` (`K_le_pred_d`). -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactSizes
open Filter
noncomputable section

abbrev d := Sizes.d
abbrev p := Sizes.p
abbrev ℓ := Sizes.ℓ
abbrev r := Sizes.r
abbrev t := Sizes.t

/-- The chunk root `⌈d/2⌉`. -/
def Kroot (n : ℕ) : ℕ := (d n+1)/2
/-- The chunk: the uniform balanced width of the `ℓ - 1` common slots above the root. -/
def K (n : ℕ) : ℕ := min (d n) (Balanced.unifWidth (ℓ n - 1) (Kroot n))

theorem Kroot_le_d (n : ℕ) : Kroot n≤d n := by unfold Kroot; omega
theorem d_le_two_Kroot (n : ℕ) : d n≤2*Kroot n := by unfold Kroot; omega

theorem Kroot_le_K (n : ℕ) : Kroot n≤K n :=
  le_min (Kroot_le_d n) (Balanced.le_unifWidth _ _)
theorem K_le_d (n : ℕ) : K n≤d n := min_le_left _ _
theorem K_le_two_Kroot (n : ℕ) : K n≤2*Kroot n :=
  (min_le_right _ _).trans (Balanced.unifWidth_le_two_mul _ _)
theorem one_le_Kroot {n : ℕ} (hn : 2≤n) : 1≤Kroot n := by
  have : 1≤d n := Sizes.one_le_d hn
  unfold Kroot
  omega
theorem one_le_K {n : ℕ} (hn : 2≤n) : 1≤K n := (one_le_Kroot hn).trans (Kroot_le_K n)

/-- The full-width chunk contains the old `2^-32` power chunk: `2 K ≤ K^2 + 1 ≤ d + 1`. -/
theorem old_K_le_Kroot (n : ℕ) : Sizes.K n≤Kroot n := by
  have hpow : Sizes.K n^2≤d n := by
    rcases Nat.eq_zero_or_pos (Sizes.K n) with h | h
    · rw [h]; exact Nat.zero_le _
    · exact (Nat.pow_le_pow_right h (by norm_num [Sizes.cExp])).trans (Sizes.K_pow_le n)
  have hsq : 2*Sizes.K n≤Sizes.K n^2+1 := by nlinarith [sq_nonneg ((Sizes.K n:ℤ)-1)]
  unfold Kroot
  omega

theorem old_K_le_K (n : ℕ) : Sizes.K n≤K n := (old_K_le_Kroot n).trans (Kroot_le_K n)

theorem tendsto_K : Tendsto K atTop atTop :=
  tendsto_atTop.2 fun M => (tendsto_atTop.1 Sizes.tendsto_K M).mono fun n h => h.trans (old_K_le_K n)

/-- Under `Big`, twice the root is below the axis length: `2 Kroot ≤ d + 1 ≤ 2 d < ℓ`. -/
theorem two_Kroot_lt_ℓ {n : ℕ} (h : Sizes.Big n) : 2*Kroot n<ℓ n := by
  have := h.two_d_lt_ℓ
  have := h.one_le_d
  change 2*((Sizes.d n+1)/2)<Sizes.ℓ n
  omega

/-- With `q = ⌊N/k⌋ ≥ 2` roots `k ≥ 2`, `w q ≤ N < (q + 1) k ≤ q (2k - 1)`, so the uniform width
`w = ⌊N/q⌋` is at most `2k - 2`. -/
private theorem div_div_le {N k : ℕ} (hk : 2≤k) (hN : 2*k≤N) : N/(N/k)≤2*k-2 := by
  have hq : 2≤N/k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  obtain ⟨q,hqdef⟩ : ∃ q, q=N/k := ⟨_,rfl⟩
  rw [← hqdef] at hq ⊢
  have hlt : N<(q+1)*k := by
    have := Nat.lt_div_mul_add (a := N) (b := k) (by omega)
    rw [← hqdef] at this
    rw [add_mul, one_mul]
    exact this
  obtain ⟨w,hwdef⟩ : ∃ w, w=N/q := ⟨_,rfl⟩
  rw [← hwdef]
  have hw : w*q≤N := by rw [hwdef]; exact Nat.div_mul_le_self _ _
  by_contra hc
  have h1 : (2*k-1)*q≤w*q := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2*k-1)*q=k*q+(k-1)*q := by
    rw [← add_mul]; congr 1; omega
  have h3 : (k-1)*2≤(k-1)*q := Nat.mul_le_mul_left _ hq
  have h4 : (q+1)*k=k*q+k := by ring
  omega

/-- Under `Big` the uniform width stays below the dimension: with `k = Kroot ≥ 2` and
`2k ≤ d + 1 < ℓ`, the width is at most `2k - 2 ≤ d - 1`. -/
theorem unifWidth_le_pred_d {n : ℕ} (h : Sizes.Big n) :
    Balanced.unifWidth (ℓ n-1) (Kroot n)≤d n-1 := by
  have hd : 3≤d n := by have := h.2; change 3≤Sizes.d n; omega
  have hℓ := two_Kroot_lt_ℓ h
  have hk2 : 2≤Kroot n := by unfold Kroot; omega
  have h2k : 2*Kroot n≤d n+1 := by unfold Kroot; omega
  have hw := div_div_le hk2 (show 2*Kroot n≤ℓ n-1 by omega)
  unfold Balanced.unifWidth
  exact max_le (by omega) (by omega)

/-- Under `Big` the chunk is the uniform width `(ℓ - 1) / ⌊(ℓ - 1)/Kroot⌋`. -/
theorem K_eq_unif {n : ℕ} (h : Sizes.Big n) :
    K n=(ℓ n-1)/((ℓ n-1)/Kroot n) := by
  have h1 : 1≤Kroot n := one_le_Kroot h.1
  have h2 : Kroot n≤ℓ n-1 := by have := two_Kroot_lt_ℓ h; omega
  have hw := unifWidth_le_pred_d h
  unfold K
  rw [min_eq_right (hw.trans (Nat.sub_le _ _)), Balanced.unifWidth_eq (by omega) h2]

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

/-- Under `Big` the chunk fits the actual initial `d - 1` transform dimension. -/
theorem K_le_pred_d {n : ℕ} (h : Sizes.Big n) : K n≤d n-1 :=
  (min_le_right _ _).trans (unifWidth_le_pred_d h)

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

/-- In particular the full two-sided guard allowance fits a chunk. -/
theorem eventually_guard_room : ∀ᶠ n in atTop, 8*Nat.clog 2 (p n)+16≤K n :=
  eventually_affine_clog_p_le_K 8 16

/-- The new chunk still fits the actual initial `d-1` transform dimension. -/
theorem eventually_K_le_predecessor : ∀ᶠ n in atTop, K n≤d n-1 :=
  Sizes.eventually_big.mono fun _ h => K_le_pred_d h

end
end IntegerMultBounds.MathlibTM2.Mult.CompactSizes
