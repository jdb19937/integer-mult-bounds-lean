module

public import IntegerMultBounds.MathlibTM2.Mult.Moduli
import IntegerMultBounds.ExactRecovery
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.NLogN.Multiplier

/-!
# Size parameters of the multiplication algorithm

Integer definitions of the parameters of the paper's `§8` "Input and transform sizes" as
functions of the operand length `n`, with the retuned constants `ε = 7/16`, `c = 2^{-32}`:

* `b = ⌈log₂ n⌉`, `p = 6b`;
* `d = ⌊b^ε⌋`, the largest `d` with `d^16 ≤ b^7`; `K = ⌊d^c⌋`, the largest `K` with
  `K^(2^32) ≤ d`;
* `T = 2^logT`, the power of two in `[4n/b, 8n/b)`; `ℓ = ⌈logT / d⌉`, `r = 2^ℓ`;
* axis lengths `t_i ∈ {r/2, r}`: the first `numHalf = dℓ - logT` are `r/2`, the rest (in
  particular the last) are `r`;
* `α`, the least integer with `α^4 ≥ 12 d² b`; `γ = d (2α² + 2)`; `η = 1/(4d)`;
  `q = ⌈n/b⌉`;
* source lengths `s_i` from `Moduli.src` with `N = oddProd d`, and `S = ∏ s_i`.

Every relation used downstream is proved for all large `n`, as a `Filter.Eventually` along
`atTop`. Most of them follow deterministically from the regime `Big n : 2 ≤ n ∧ 2^40 ≤ d n`
(`eventually_big`), whose consequences are the `Big.*` lemmas:

* `prod_t`, `t_last`, `t_eq`: `∏ t_i = T`, `t_d = r`, `t_i ∈ {r/2, r}`;
* `volume_bounds`: `24 n ≤ T p < 48 n`; `Big.logT_bounds`: `b ≤ 2 log₂ T`, `log₂ T < b`;
* `d_pow_le_p`, `p_lt_pow`, `d_rpow_bounds`: `p^ε/12 ≤ d ≤ p^ε`;
* `Big.ℓ_bounds`, `Big.ℓ_bounds_real`: `p/(12d) ≤ ℓ ≤ p/(3d)`; `Big.K_succ_le_ℓ`;
* `two_le_alpha`, `alpha_sq_lt`, `Big.alpha_sq_le_p`, `Big.eta_lt_theta`,
  `Big.quarter_p_le_theta`, `Big.band_width`, `Big.band_budget`;
* `Big.four_gamma_le_b`, `Big.gamma_le_real`: `γ ≤ b/4`;
* `Big.good`: the moduli (`Moduli.Good`), with `Big.S_lt_T`, `Big.T_lt_two_S`;
* `Big.two_q_le`, `Big.digits_length_le`: no wraparound, `2q - 2 < S`;
* `Big.margin_hyps`, `eventually_threshold`, `eventually_margins`: the hypotheses and the
  conclusion of `ExactRecovery.margins_of_sizes` at `k = b`, `L = log₂ T`;
* `eventually_pow_p_le_r`, `eventually_clog_p_le_K`, `eventually_logb_p_le_K`,
  `eventually_mul_K_le_ℓ`, `eventually_small`: the growth statements `p^C ≤ r`,
  `C log₂ p ≤ K`, `C K ≤ ℓ`, `2 d p² ≤ T log₂ T`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Sizes

open Filter Finset IntegerMultBounds.MathlibTM2.Mult.Moduli
open scoped Function

/-! ### Integer roots -/

/-- The integer `k`-th root: the largest `y` with `y^k ≤ x`. -/
def iroot (k x : ℕ) : ℕ := Nat.findGreatest (fun y => y ^ k ≤ x) x

section Iroot

variable {k x y : ℕ}

theorem iroot_pow_le (hk : k ≠ 0) (x : ℕ) : iroot k x ^ k ≤ x :=
  Nat.findGreatest_spec (P := fun y => y ^ k ≤ x) (Nat.zero_le x) (by simp [zero_pow hk])

theorem le_iroot_iff (hk : k ≠ 0) : y ≤ iroot k x ↔ y ^ k ≤ x := by
  constructor
  · intro h
    exact (Nat.pow_le_pow_left h k).trans (iroot_pow_le hk x)
  · intro h
    have hyx : y ≤ x := by
      rcases Nat.eq_zero_or_pos y with rfl | _
      · exact Nat.zero_le _
      · exact (Nat.le_self_pow hk y).trans h
    exact Nat.le_findGreatest (P := fun y => y ^ k ≤ x) hyx h

theorem lt_succ_iroot_pow (hk : k ≠ 0) (x : ℕ) : x < (iroot k x + 1) ^ k := by
  by_contra h
  have := (le_iroot_iff hk).2 (not_lt.1 h)
  omega

theorem one_le_iroot (hk : k ≠ 0) (hx : 1 ≤ x) : 1 ≤ iroot k x :=
  (le_iroot_iff hk).2 (by rw [one_pow]; exact hx)

theorem iroot_le_self (hk : k ≠ 0) (x : ℕ) : iroot k x ≤ x := by
  rcases Nat.eq_zero_or_pos (iroot k x) with h | h
  · rw [h]; exact Nat.zero_le _
  · exact (Nat.le_self_pow hk _).trans (iroot_pow_le hk x)

end Iroot

/-! ### Elementary inequalities -/

theorem two_mul_le_two_pow (m : ℕ) : 2 * m ≤ 2 ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := Nat.lt_two_pow_self (n := m - 1)
    have e : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem le_two_pow_two_mul {m : ℕ} (hm : 2 ≤ m) : 4 * m ≤ 2 ^ (2 * m) := by
  have h := Nat.lt_two_pow_self (n := m)
  have e : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [e]
  nlinarith

/-- `A m^k ≤ 2^m` for all large `m`. -/
theorem eventually_mul_pow_le_two_pow (A k : ℕ) : ∀ᶠ m : ℕ in atTop, A * m ^ k ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (one_lt_two : (1 : ℝ) < 2)
  have h2 := h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (A + 1) by positivity))
  filter_upwards [h2] with m hm
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have hA : (0 : ℝ) < A + 1 := by positivity
  rw [div_lt_div_iff₀ hpos hA, one_mul] at hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k := by positivity
  have : ((A * m ^ k : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast this

/-- `c x^k ≤ (c x)^k`. Stated for a variable exponent `k`, so that instances at
`k = 2^3` never ask the kernel to evaluate a power of a numeral. -/
theorem mul_pow_le_mul_pow {k : ℕ} (hk : k ≠ 0) (c x : ℕ) : c * x ^ k ≤ (c * x) ^ k := by
  rw [mul_pow]
  exact Nat.mul_le_mul_right _ (Nat.le_self_pow hk c)

/-! ### Fixed exponents -/

/-- Exact integer-root degree for the dyadic dimension. -/
def rootExp : ℕ := 16

/-- The power applied before taking the integer root. -/
def rootNumerator : ℕ := 7

/-- The available integer lower size cap, distinct from the root degree. -/
def powerCap : ℕ := 2

/-- A coarse upper growth power, not the reciprocal of `epsilon`. -/
def upperPower : ℕ := 8

/-- `2^32`, the root index of the legacy chunk. -/
def cExp : ℕ := 2 ^ 32

theorem rootExp_ne : rootExp ≠ 0 := by decide
theorem upperPower_ne : upperPower ≠ 0 := by decide
theorem cExp_ne : cExp ≠ 0 := by unfold cExp; positivity
theorem one_le_cExp : 1 ≤ cExp := by unfold cExp; norm_num

/-- The dyadic dimension exponent `7/16`. -/
noncomputable def epsilon : ℝ := (rootNumerator : ℝ) / rootExp

theorem epsilon_eq : epsilon = (7 : ℝ) / 16 := by norm_num [epsilon, rootNumerator, rootExp]

/-- `c = 2^{-32}` as a real number. -/
noncomputable def cParam : ℝ := ((cExp : ℕ) : ℝ)⁻¹

theorem cParam_eq : cParam = (2 ^ 32 : ℝ)⁻¹ := by
  norm_num [cParam, cExp]

/-- `iroot k x = ⌊x^(1/k)⌋`. -/
theorem iroot_eq_floor {k : ℕ} (hk : k ≠ 0) (x : ℕ) :
    iroot k x = ⌊(x : ℝ) ^ ((k : ℝ)⁻¹)⌋₊ := by
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hk)
  symm
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · have h : ((iroot k x : ℝ)) ^ k ≤ x := by exact_mod_cast iroot_pow_le hk x
    have h' := Real.rpow_le_rpow (by positivity) h hk'.le
    rwa [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hk] at h'
  · have h : (x : ℝ) < ((iroot k x : ℝ) + 1) ^ k := by exact_mod_cast lt_succ_iroot_pow hk x
    have h' := Real.rpow_lt_rpow (Nat.cast_nonneg _) h hk'
    rwa [Real.pow_rpow_inv_natCast (by positivity) hk] at h'

/-- `⌈X^(1/k)⌉ = m` when `(m - 1)^k < X ≤ m^k`. -/
theorem ceil_root_eq {k m X : ℕ} (hk : k ≠ 0) (hm : 1 ≤ m) (h1 : (m - 1) ^ k < X)
    (h2 : X ≤ m ^ k) : ⌈(X : ℝ) ^ ((k : ℝ)⁻¹)⌉₊ = m := by
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hk)
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · have h : (((m - 1 : ℕ) : ℝ)) ^ k < X := by exact_mod_cast h1
    have h' := Real.rpow_lt_rpow (by positivity) h hk'
    rwa [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hk] at h'
  · have h : (X : ℝ) ≤ (m : ℝ) ^ k := by exact_mod_cast h2
    have h' := Real.rpow_le_rpow (Nat.cast_nonneg _) h hk'.le
    rwa [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hk] at h'

/-! ### The parameters -/

/-- `b = ⌈log₂ n⌉`. -/
def b (n : ℕ) : ℕ := Nat.clog 2 n

/-- The working precision `p = 6b`. -/
def p (n : ℕ) : ℕ := 6 * b n

/-- The dimension `d = ⌊b^ε⌋`: the largest `d` with `d^16 ≤ b^7`. -/
def d (n : ℕ) : ℕ := iroot rootExp (b n ^ rootNumerator)

/-- `K = ⌊d^c⌋`: the largest `K` with `K^(2^32) ≤ d`. -/
def K (n : ℕ) : ℕ := iroot cExp (d n)

/-- `log₂ T`: the least `L` with `4n ≤ b 2^L`, i.e. `⌈log₂ ⌈4n/b⌉⌉`. -/
def logT (n : ℕ) : ℕ := Nat.clog 2 ((4 * n + b n - 1) / b n)

/-- `T`, the power of two in `[4n/b, 8n/b)`. -/
def T (n : ℕ) : ℕ := 2 ^ logT n

/-- `ℓ = ⌈logT / d⌉`. -/
def ℓ (n : ℕ) : ℕ := (logT n + d n - 1) / d n

/-- `r = 2^ℓ`. -/
def r (n : ℕ) : ℕ := 2 ^ ℓ n

/-- The number `dℓ - log₂ T` of axes of length `r/2`. -/
def numHalf (n : ℕ) : ℕ := d n * ℓ n - logT n

/-- The axis lengths: `r/2` on the first `numHalf` axes, `r` on the others. -/
def t (n : ℕ) (i : Fin (d n)) : ℕ := if (i : ℕ) < numHalf n then 2 ^ (ℓ n - 1) else 2 ^ ℓ n

/-- `u = ⌈log₂ p⌉ + 3`, the least power with `8p ≤ 2^u`. -/
def alphaU (n : ℕ) : ℕ := Nat.clog 2 (p n) + 3

theorem exists_alpha (n : ℕ) : ∃ α : ℕ, alphaU n ^ 2 ≤ α ^ 4 :=
  ⟨alphaU n, Nat.pow_le_pow_right (by unfold alphaU; omega) (by norm_num)⟩

/-- `α = ⌈√u⌉`: the least `α` with `u² ≤ α^4`, so `u ≤ α² < 4u`. The banded `B̃₀` needs only
the small-gap width `8p ≤ 2^(α²)`. -/
def alpha (n : ℕ) : ℕ := Nat.find (exists_alpha n)

/-- `γ = d (3α² + 2)`: the library's `d (2⌈α²⌉ + 2)` at integer `α`, plus `α²` per axis for the
scale `2^-α²` of the banded `B̃₀`. -/
def gamma (n : ℕ) : ℕ := d n * (3 * alpha n ^ 2 + 2)

/-- `η = 1/(4d)`. -/
noncomputable def eta (n : ℕ) : ℝ := 1 / (4 * d n)

/-- The number `q = ⌈n/b⌉` of radix-`2^b` digits. -/
def q (n : ℕ) : ℕ := (n + b n - 1) / b n

/-- `N = 1 · 3 ⋯ (4d - 1)`. -/
def N (n : ℕ) : ℕ := oddProd (d n)

/-- The source lengths `s_i` (`Moduli.src` with `N = oddProd d`, `R = r/2`). -/
def s (n : ℕ) : Fin (d n) → ℕ := src (d n) (N n) (numHalf n) (ℓ n - 1)

/-- `S = ∏ s_i`. -/
def S (n : ℕ) : ℕ := ∏ i, s n i

/-! ### `b` -/

section Basic

variable {n : ℕ}

theorem one_le_b (hn : 2 ≤ n) : 1 ≤ b n := Nat.clog_pos one_lt_two hn

theorem le_two_pow_b (n : ℕ) : n ≤ 2 ^ b n := Nat.le_pow_clog one_lt_two n

theorem two_pow_b_lt (hn : 2 ≤ n) : 2 ^ b n < 2 * n := by
  have h : 2 ^ (b n - 1) < n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) one_lt_two (x := n) hn
    rwa [Nat.pred_eq_sub_one] at this
  have h1 := one_le_b hn
  have e : 2 ^ b n = 2 * 2 ^ (b n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem b_lt_two_mul (hn : 2 ≤ n) : b n < 2 * n :=
  Nat.lt_two_pow_self.trans (two_pow_b_lt hn)

theorem le_b_of_two_pow_le {m : ℕ} (h : 2 ^ m ≤ n) : m ≤ b n := by
  have := Nat.clog_mono_right 2 h
  rwa [Nat.clog_pow 2 m one_lt_two] at this

theorem tendsto_b : Tendsto b atTop atTop :=
  tendsto_atTop.2 fun m => eventually_atTop.2 ⟨2 ^ m, fun _ h => le_b_of_two_pow_le h⟩

/-! ### `d` and `K` -/

theorem d_pow_le (n : ℕ) : d n ^ rootExp ≤ b n ^ rootNumerator :=
  iroot_pow_le rootExp_ne _

theorem b_pow_lt_d_succ_pow (n : ℕ) : b n ^ rootNumerator < (d n + 1) ^ rootExp :=
  lt_succ_iroot_pow rootExp_ne _

theorem b_lt_d_succ_pow (n : ℕ) : b n < (d n + 1) ^ upperPower := by
  by_contra h
  have hb : (d n+1)^8≤b n := Nat.le_of_not_gt h
  have hp := Nat.pow_le_pow_left hb 7
  have hroot := b_pow_lt_d_succ_pow n
  have hmono : (d n+1)^16≤(d n+1)^56 := Nat.pow_le_pow_right (by omega) (by decide)
  rw [←pow_mul] at hp
  norm_num only [Nat.mul] at hp
  change b n ^ 7 < (d n+1)^16 at hroot
  omega

theorem le_d_iff {D : ℕ} : D ≤ d n ↔ D ^ rootExp ≤ b n ^ rootNumerator :=
  le_iroot_iff rootExp_ne

theorem one_le_d (hn : 2 ≤ n) : 1 ≤ d n :=
  one_le_iroot rootExp_ne (one_le_pow₀ (one_le_b hn))

theorem d_sq_le (n : ℕ) : d n ^ powerCap ≤ b n := by
  have hroot := d_pow_le n
  rcases Nat.eq_zero_or_pos (b n) with hb | hb
  · have hd : d n = 0 := by simpa [hb, rootNumerator, rootExp] using hroot
    simp [hd, powerCap]
  · apply (Nat.pow_le_pow_iff_left (by decide : 8≠0)).mp
    change d n ^ 16 ≤ b n ^ 7 at hroot
    change (d n ^ 2)^8 ≤ b n ^ 8
    calc
      (d n^2)^8=d n^16 := by rw [←pow_mul]
      _ ≤ b n^7 := hroot
      _ ≤ b n^8 := Nat.pow_le_pow_right hb (by decide)

theorem d_le_b (n : ℕ) : d n ≤ b n :=
  (Nat.le_self_pow (by decide : powerCap≠0) _).trans (d_sq_le n)

theorem pow_le_b_of {k : ℕ} (hk : k ≤ powerCap) (hd : 1 ≤ d n) : d n ^ k ≤ b n :=
  (Nat.pow_le_pow_right hd hk).trans (d_sq_le n)

/-- `F d² ≤ b` whenever `F⁴ ≤ d`: `(F d²)^8 = F^8 d^16 ≤ d² b^7 ≤ b^8`. -/
theorem mul_sq_le_b {F : ℕ} (hF : F ^ 4 ≤ d n) : F * d n ^ 2 ≤ b n := by
  rcases Nat.eq_zero_or_pos (d n) with h | h
  · simp [h]
  have hroot : d n ^ 16 ≤ b n ^ 7 := d_pow_le n
  have hsq : d n ^ 2 ≤ b n := pow_le_b_of (k := 2) le_rfl h
  apply (Nat.pow_le_pow_iff_left (by decide : 8≠0)).mp
  calc (F * d n ^ 2) ^ 8 = (F ^ 4) ^ 2 * d n ^ 16 := by ring
    _ ≤ d n ^ 2 * b n ^ 7 := Nat.mul_le_mul (Nat.pow_le_pow_left hF 2) hroot
    _ ≤ b n * b n ^ 7 := Nat.mul_le_mul_right _ hsq
    _ = b n ^ 8 := by ring

theorem tendsto_d : Tendsto d atTop atTop :=
  tendsto_atTop.2 fun D => (tendsto_atTop.1 tendsto_b (D ^ rootExp)).mono fun n h =>
    le_d_iff.2 (h.trans (Nat.le_self_pow (by decide : rootNumerator≠0) _))

/-- The integer dimension is exactly the floor of the real dyadic power. -/
theorem d_eq_floor (n : ℕ) : d n = ⌊(b n : ℝ) ^ epsilon⌋₊ := by
  rw [d, iroot_eq_floor rootExp_ne]
  push_cast
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg (b n))]
  norm_num [epsilon, rootNumerator, rootExp]

theorem K_pow_le (n : ℕ) : K n ^ cExp ≤ d n := iroot_pow_le cExp_ne _

theorem d_lt_K_succ_pow (n : ℕ) : d n < (K n + 1) ^ cExp := lt_succ_iroot_pow cExp_ne _

theorem K_le_d (n : ℕ) : K n ≤ d n := iroot_le_self cExp_ne _

theorem tendsto_K : Tendsto K atTop atTop :=
  tendsto_atTop.2 fun M => (tendsto_atTop.1 tendsto_d (M ^ cExp)).mono fun _ h =>
    (le_iroot_iff cExp_ne).2 h

/-! ### `T` -/

theorem logT_le_iff (hn : 2 ≤ n) {L : ℕ} : logT n ≤ L ↔ 4 * n ≤ b n * 2 ^ L := by
  have hb := one_le_b hn
  unfold logT
  rw [Nat.clog_le_iff_le_pow one_lt_two, Nat.div_le_iff_le_mul_add_pred hb]
  omega

theorem four_mul_le_bT (hn : 2 ≤ n) : 4 * n ≤ b n * T n := (logT_le_iff hn).1 le_rfl

theorem bT_lt (hn : 2 ≤ n) : b n * T n < 8 * n := by
  rcases Nat.eq_zero_or_pos (logT n) with h | h
  · simp only [T, h, pow_zero, mul_one]
    have := b_lt_two_mul hn
    omega
  · have h1 : ¬ logT n ≤ logT n - 1 := by omega
    rw [logT_le_iff hn] at h1
    have e : T n = 2 * 2 ^ (logT n - 1) := by
      unfold T; rw [← pow_succ']; congr 1; omega
    rw [e]
    have : b n * (2 * 2 ^ (logT n - 1)) = 2 * (b n * 2 ^ (logT n - 1)) := by ring
    omega

theorem logT_le_b (hn : 2 ≤ n) (hb : 4 ≤ b n) : logT n ≤ b n := by
  rw [logT_le_iff hn]
  have := le_two_pow_b n
  nlinarith

/-- `T < 2^b` once `b ≥ 8`. -/
theorem logT_lt_b (hn : 2 ≤ n) (hb : 8 ≤ b n) : logT n < b n := by
  have h : logT n ≤ b n - 1 := by
    rw [logT_le_iff hn]
    have h1 := le_two_pow_b n
    have e : 2 ^ b n = 2 * 2 ^ (b n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at h1
    nlinarith
  omega

/-- `b/2 ≤ log₂ T`, for every `n ≥ 2`. -/
theorem b_le_two_mul_logT (hn : 2 ≤ n) : b n ≤ 2 * logT n := by
  by_contra hc
  push Not at hc
  set L := logT n
  set m := b n + 1 - L
  have h1 : 2 ^ (b n + 1) < 4 * n := by
    have := two_pow_b_lt hn
    rw [pow_succ]
    omega
  have h2 := four_mul_le_bT hn
  have e : 2 ^ (b n + 1) = 2 ^ m * T n := by
    unfold T; rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ m * T n < b n * T n := by omega
  have h4 : 2 ^ m < b n := lt_of_mul_lt_mul_right h3 (Nat.zero_le _)
  have h5 := two_mul_le_two_pow m
  omega

theorem one_le_logT_of (hn : 2 ≤ n) (hb : 2 ≤ b n) : 1 ≤ logT n := by
  have := b_le_two_mul_logT hn
  omega

/-! ### `ℓ`, `r`, the axis lengths -/

theorem logT_le_dℓ (hd : 1 ≤ d n) : logT n ≤ d n * ℓ n := by
  have h := Nat.lt_mul_div_succ (logT n + d n - 1) (b := d n) hd
  unfold ℓ
  have : d n * ((logT n + d n - 1) / d n + 1) = d n * ((logT n + d n - 1) / d n) + d n := by
    ring
  omega

/-- `d⁹ ≤ 128 ℓ⁷` for every `n ≥ 2`: `d^16 ≤ b^7 ≤ (2 log₂ T)^7 ≤ (2 d ℓ)^7`. -/
theorem d_pow_nine_le (hn : 2 ≤ n) : d n ^ 9 ≤ 128 * ℓ n ^ 7 := by
  have hd := one_le_d hn
  have h1 := b_le_two_mul_logT hn
  have h2 := logT_le_dℓ hd
  have hroot : d n ^ 16 ≤ b n ^ 7 := d_pow_le n
  have h3 : b n ^ 7 ≤ (2 * (d n * ℓ n)) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have h4 : d n ^ 7 * d n ^ 9 ≤ d n ^ 7 * (128 * ℓ n ^ 7) := by
    calc d n ^ 7 * d n ^ 9 = d n ^ 16 := by ring
      _ ≤ (2 * (d n * ℓ n)) ^ 7 := hroot.trans h3
      _ = d n ^ 7 * (128 * ℓ n ^ 7) := by ring
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

/-- `d ≤ 2ℓ` for every `n ≥ 2`. -/
theorem d_le_two_ℓ (hn : 2 ≤ n) : d n ≤ 2 * ℓ n := by
  have h := d_pow_nine_le hn
  have hd := one_le_d hn
  by_contra hc
  have h1 : (2 * ℓ n) ^ 7 ≤ d n ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have e1 : (2 * ℓ n) ^ 7 = 128 * ℓ n ^ 7 := by ring
  have e2 : d n ^ 9 = d n ^ 2 * d n ^ 7 := by ring
  have h2 : 0 < d n ^ 7 := by positivity
  rcases Nat.lt_or_ge (d n) 2 with h3 | h3
  · have hd1 : d n = 1 := by omega
    have hl : ℓ n = 0 := by omega
    rw [hd1, hl] at h
    norm_num at h
  · have h4 : 4 ≤ d n ^ 2 := by nlinarith
    have h5 : 4 * d n ^ 7 ≤ d n ^ 2 * d n ^ 7 := Nat.mul_le_mul_right _ h4
    omega

theorem dℓ_lt (hd : 1 ≤ d n) : d n * ℓ n < logT n + d n := by
  have h := Nat.mul_div_le (logT n + d n - 1) (d n)
  unfold ℓ
  omega

theorem numHalf_lt (hd : 1 ≤ d n) : numHalf n < d n := by
  have := dℓ_lt hd
  unfold numHalf
  omega

theorem one_le_ℓ_of_numHalf (h : 0 < numHalf n) : 1 ≤ ℓ n := by
  unfold numHalf at h
  rcases Nat.eq_zero_or_pos (ℓ n) with h' | h'
  · rw [h', mul_zero] at h; omega
  · exact h'

/-- `t_i ∈ {r/2, r}`. -/
theorem t_eq (i : Fin (d n)) : t n i = if (i : ℕ) < numHalf n then r n / 2 else r n := by
  unfold t r
  split_ifs with h
  · have := one_le_ℓ_of_numHalf (lt_of_le_of_lt (Nat.zero_le _) h)
    have e : 2 ^ ℓ n = 2 ^ (ℓ n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [e, Nat.mul_div_cancel _ two_pos]
  · rfl

/-- The last axis has length `r`. -/
theorem t_last (hd : 1 ≤ d n) : t n ⟨d n - 1, by omega⟩ = r n := by
  have := numHalf_lt hd
  unfold t r
  split_ifs with h
  · simp only at h; omega
  · rfl

/-- `∏ t_i = T`. -/
theorem prod_t (hd : 1 ≤ d n) : ∏ i, t n i = T n := by
  have ha := numHalf_lt hd
  have h1 := logT_le_dℓ hd
  have h2 := dℓ_lt hd
  have hF := Fin.prod_univ_eq_prod_range
    (fun i => if i < numHalf n then 2 ^ (ℓ n - 1) else 2 ^ ℓ n) (d n)
  have hA : ∏ i ∈ range (numHalf n), (if i < numHalf n then 2 ^ (ℓ n - 1) else 2 ^ ℓ n) =
      (2 ^ (ℓ n - 1)) ^ numHalf n := by
    rw [prod_congr rfl (g := fun _ => 2 ^ (ℓ n - 1)) (fun i hi => by simp [mem_range.1 hi]),
      prod_const, card_range]
  have hB : ∏ i ∈ Ico (numHalf n) (d n), (if i < numHalf n then 2 ^ (ℓ n - 1) else 2 ^ ℓ n) =
      (2 ^ ℓ n) ^ (d n - numHalf n) := by
    rw [prod_congr rfl (g := fun _ => 2 ^ ℓ n)
      (fun i hi => by simp [not_lt.2 (mem_Ico.1 hi).1]), prod_const, Nat.card_Ico]
  unfold t
  rw [hF, ← prod_range_mul_prod_Ico _ ha.le, hA, hB, ← pow_mul, ← pow_mul, ← pow_add]
  unfold T
  congr 1
  rcases Nat.eq_zero_or_pos (numHalf n) with h0 | h0
  · rw [h0]
    unfold numHalf at h0
    simp only [mul_zero, zero_add, Nat.sub_zero]
    rw [mul_comm]; omega
  · have hl := one_le_ℓ_of_numHalf h0
    obtain ⟨m, hm⟩ : ∃ m, ℓ n = m + 1 := ⟨ℓ n - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    rw [hm] at h1 h2
    unfold numHalf at h0 ⊢
    rw [hm]
    have e1 : d n * (m + 1) = m * d n + d n := by ring
    have e2 : m * (d n * (m + 1) - logT n) + (m + 1) * (d n - (d n * (m + 1) - logT n)) =
        m * d n + (d n - (d n * (m + 1) - logT n)) := by
      have hle : d n * (m + 1) - logT n ≤ d n := by omega
      obtain ⟨u, hu⟩ : ∃ u, d n = (d n * (m + 1) - logT n) + u := ⟨_, (Nat.add_sub_of_le hle).symm⟩
      rw [show d n - (d n * (m + 1) - logT n) = u by omega]
      generalize d n * (m + 1) - logT n = v at hu ⊢
      rw [hu]
      ring
    rw [e2]
    omega

end Basic

/-! ### Bounds valid for every `n ≥ 2` -/

section Small

variable {n : ℕ}

/-- `T p = Θ(n)`: `24 n ≤ T p < 48 n`. -/
theorem volume_bounds (hn : 2 ≤ n) : 24 * n ≤ T n * p n ∧ T n * p n < 48 * n := by
  have h1 := four_mul_le_bT hn
  have h2 := bT_lt hn
  have e : T n * p n = 6 * (b n * T n) := by unfold p; ring
  omega

/-- The exact root cap also holds with the larger precision parameter. -/
theorem d_pow_le_p (n : ℕ) : d n ^ rootExp ≤ p n ^ rootNumerator :=
  (d_pow_le n).trans (Nat.pow_le_pow_left (by unfold p; omega) _)

theorem p_lt_pow (hn : 2 ≤ n) : p n < (12 * d n) ^ upperPower := by
  have hd := one_le_d hn
  have h2 : (d n + 1) ^ upperPower ≤ (2 * d n) ^ upperPower := Nat.pow_le_pow_left (by omega) _
  calc p n = 6 * b n := rfl
    _ < 6 * (d n + 1) ^ upperPower := by have := b_lt_d_succ_pow n; omega
    _ ≤ 6 * (2 * d n) ^ upperPower := Nat.mul_le_mul_left _ h2
    _ ≤ (6 * (2 * d n)) ^ upperPower := mul_pow_le_mul_pow upperPower_ne 6 _
    _ = (12 * d n) ^ upperPower := by rw [show 6 * (2 * d n) = 12 * d n by ring]

/-- The real dimension sandwich retains its constants at `ε = 9/64`. -/
theorem d_rpow_bounds (hn : 2 ≤ n) :
    (p n : ℝ) ^ epsilon / 12 ≤ d n ∧ (d n : ℝ) ≤ (p n : ℝ) ^ epsilon := by
  have hfloor : (d n : ℝ) ≤ (b n : ℝ)^epsilon ∧
      (b n : ℝ)^epsilon < (d n : ℝ)+1 :=
    (Nat.floor_eq_iff (by positivity)).mp (d_eq_floor n).symm
  have hd : (1:ℝ) ≤ d n := by exact_mod_cast one_le_d hn
  have hhalf : (b n : ℝ)^epsilon/2 ≤ d n := by linarith [hfloor.2]
  have he : (0:ℝ)≤epsilon := by rw [epsilon_eq]; norm_num
  have h6 : (6:ℝ)^epsilon≤6 := Real.rpow_le_self_of_one_le (by norm_num)
    (by rw [epsilon_eq]; norm_num)
  have hp : (p n : ℝ)=6*(b n : ℝ) := by simp [p]
  rw [hp]
  constructor
  · have hscale : (6*(b n:ℝ))^epsilon≤6*(b n:ℝ)^epsilon := by
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_right h6 (by positivity)
    linarith
  · exact hfloor.1.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by nlinarith) he)

theorem alpha_spec (n : ℕ) : alphaU n ^ 2 ≤ alpha n ^ 4 := Nat.find_spec (exists_alpha n)

theorem alpha_min (n : ℕ) {m : ℕ} (hm : m < alpha n) : m ^ 4 < alphaU n ^ 2 :=
  not_le.1 (Nat.find_min (exists_alpha n) hm)

/-- `u ≤ α²`. -/
theorem alphaU_le_alpha_sq (n : ℕ) : alphaU n ≤ alpha n ^ 2 := by
  have h := alpha_spec n
  by_contra hc
  have h1 : (alpha n ^ 2) ^ 2 < alphaU n ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  rw [← pow_mul] at h1
  norm_num at h1
  omega

theorem two_le_alpha' (n : ℕ) : 2 ≤ alpha n := by
  have h := alphaU_le_alpha_sq n
  have hu : 3 ≤ alphaU n := by unfold alphaU; omega
  by_contra hc
  have : alpha n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem two_le_alpha (_hn : 2 ≤ n) : 2 ≤ alpha n := two_le_alpha' n

/-- `α² < 4u`. -/
theorem alpha_sq_lt (n : ℕ) : alpha n ^ 2 < 4 * alphaU n := by
  have h2 := two_le_alpha' n
  have h1 := alpha_min n (m := alpha n - 1) (by omega)
  have h3 : (alpha n - 1) ^ 2 < alphaU n := by
    have : ((alpha n - 1) ^ 2) ^ 2 < alphaU n ^ 2 := by rw [← pow_mul]; exact h1
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 this
  have h4 : alpha n ^ 2 ≤ (2 * (alpha n - 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rw [mul_pow] at h4
  omega

/-- `α⁴ < 16 u²`. -/
theorem alpha_pow_four_lt (n : ℕ) : alpha n ^ 4 < 16 * alphaU n ^ 2 := by
  have h := alpha_sq_lt n
  have : (alpha n ^ 2) ^ 2 < (4 * alphaU n) ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  rw [← pow_mul, mul_pow] at this
  simpa using this

/-- `u ≤ b + 6`. -/
theorem alphaU_le_b (n : ℕ) : alphaU n ≤ b n + 6 := by
  have h1 : p n ≤ 2 ^ (b n + 3) := by
    have := Nat.lt_two_pow_self (n := b n)
    unfold p; rw [pow_add]; omega
  have := Nat.clog_le_of_le_pow h1
  unfold alphaU; omega

/-- `γ = d (2 ⌈α²⌉ + 2 + α²)` with real `α`, the library's normalization plus the band scale. -/
theorem gamma_eq_ceil (n : ℕ) :
    gamma n = d n * (2 * ⌈((alpha n : ℝ)) ^ 2⌉₊ + 2 + alpha n * alpha n) := by
  rw [← Nat.cast_pow, Nat.ceil_natCast]
  unfold gamma; ring

/-- `K = ⌊d^c⌋`. -/
theorem K_eq_floor (n : ℕ) : K n = ⌊(d n : ℝ) ^ cParam⌋₊ := iroot_eq_floor cExp_ne _

/-- `T` is the power of two in `[4n/b, 8n/b)`. -/
theorem T_bounds_real (hn : 2 ≤ n) :
    4 * (n : ℝ) / b n ≤ T n ∧ (T n : ℝ) < 8 * n / b n := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast one_le_b hn
  have h1 : (4 * n : ℝ) ≤ b n * T n := by exact_mod_cast four_mul_le_bT hn
  have h2 : (b n * T n : ℝ) < 8 * n := by exact_mod_cast bT_lt hn
  constructor
  · rw [div_le_iff₀ hb]; linarith
  · rw [lt_div_iff₀ hb]; linarith

/-- `log₂ p ≤ 3 + 2^35 ⌈log₂ (K + 1)⌉`. -/
theorem clog_p_le (n : ℕ) : Nat.clog 2 (p n) ≤ 3 + cExp * upperPower * Nat.clog 2 (K n + 1) := by
  apply Nat.clog_le_of_le_pow
  have h1 := b_lt_d_succ_pow n
  have h2 : d n + 1 ≤ (K n + 1) ^ cExp := d_lt_K_succ_pow n
  have h3 : (d n + 1) ^ upperPower ≤ ((K n + 1) ^ cExp) ^ upperPower := Nat.pow_le_pow_left h2 _
  have h4 : K n + 1 ≤ 2 ^ Nat.clog 2 (K n + 1) := Nat.le_pow_clog one_lt_two _
  have h5 : ((K n + 1) ^ cExp) ^ upperPower ≤ ((2 ^ Nat.clog 2 (K n + 1)) ^ cExp) ^ upperPower :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_left h4 _) _
  have e : 2 ^ (3 + cExp * upperPower * Nat.clog 2 (K n + 1)) =
      8 * ((2 ^ Nat.clog 2 (K n + 1)) ^ cExp) ^ upperPower := by
    rw [← pow_mul, ← pow_mul, pow_add]; ring_nf
  rw [e]
  unfold p
  omega

end Small

/-! ### The large regime -/

/-- The regime of the deterministic size relations: `n ≥ 2` and `d ≥ 2^40`. With `d^16 ≤ b^7`
this pays every fixed `F d² ≤ b` with `F⁴ ≤ d` (`mul_sq_le_b`). -/
def Big (n : ℕ) : Prop := 2 ≤ n ∧ 1099511627776 ≤ d n

theorem eventually_big : ∀ᶠ n in atTop, Big n :=
  (eventually_ge_atTop 2).and (tendsto_atTop.1 tendsto_d 1099511627776)

section Big

variable {n : ℕ}

theorem Big.one_le_d (h : Big n) : 1 ≤ d n := by have := h.2; omega

theorem Big.two_le_d (h : Big n) : 2 ≤ d n := by have := h.2; omega

theorem Big.pow_le_b (h : Big n) {k : ℕ} (hk : k ≤ 2) : d n ^ k ≤ b n :=
  pow_le_b_of hk h.one_le_d

/-- `F d² ≤ b` for `F⁴ ≤ d`. -/
theorem Big.mul_sq_le (_h : Big n) {F : ℕ} (hF : F ^ 4 ≤ d n) : F * d n ^ 2 ≤ b n :=
  mul_sq_le_b hF

theorem Big.sixteen_le_b (h : Big n) : 16 ≤ b n := by
  have := h.pow_le_b (k := 1) (by norm_num)
  have := h.2
  rw [pow_one] at *
  omega

theorem Big.logT_bounds (h : Big n) : b n ≤ 2 * logT n ∧ logT n < b n :=
  ⟨b_le_two_mul_logT h.1, logT_lt_b h.1 (by have := h.sixteen_le_b; omega)⟩

theorem Big.one_le_logT (h : Big n) : 1 ≤ logT n :=
  one_le_logT_of h.1 (by have := h.sixteen_le_b; omega)

/-- `b ≤ 2 d ℓ`. -/
theorem Big.b_le_two_dℓ (h : Big n) : b n ≤ 2 * (d n * ℓ n) := by
  have := h.logT_bounds.1
  have := logT_le_dℓ h.one_le_d
  omega

/-- `2d ≤ ℓ`: `4 d² ≤ b ≤ 2 d ℓ`. -/
theorem Big.two_d_le_ℓ (h : Big n) : 2 * d n ≤ ℓ n := by
  have h1 := h.b_le_two_dℓ
  have h2 := h.mul_sq_le (F := 4) (by have := h.2; norm_num; omega)
  have hd := h.one_le_d
  have h3 : d n * (2 * (2 * d n)) ≤ d n * (2 * ℓ n) := by
    calc d n * (2 * (2 * d n)) = 4 * d n ^ 2 := by ring
      _ ≤ 2 * (d n * ℓ n) := h2.trans h1
      _ = d n * (2 * ℓ n) := by ring
  have := Nat.le_of_mul_le_mul_left h3 hd
  omega

theorem Big.d_le_ℓ (h : Big n) : d n + 1 ≤ ℓ n := by
  have := h.two_d_le_ℓ
  have := h.one_le_d
  omega

theorem Big.two_le_ℓ (h : Big n) : 2 ≤ ℓ n := by have := h.d_le_ℓ; have := h.2; omega

/-- `p/(12d) ≤ ℓ ≤ p/(3d)`, integer form. -/
theorem Big.ℓ_bounds (h : Big n) : p n ≤ 12 * d n * ℓ n ∧ 3 * d n * ℓ n ≤ p n := by
  have h1 := h.logT_bounds
  have h2 := logT_le_dℓ h.one_le_d
  have h3 := dℓ_lt h.one_le_d
  have h4 := d_le_b n
  have e1 : 12 * d n * ℓ n = 12 * (d n * ℓ n) := by ring
  have e2 : 3 * d n * ℓ n = 3 * (d n * ℓ n) := by ring
  unfold p
  omega

/-- `p/(12d) ≤ ℓ ≤ p/(3d)`. -/
theorem Big.ℓ_bounds_real (h : Big n) :
    (p n : ℝ) / (12 * d n) ≤ ℓ n ∧ (ℓ n : ℝ) ≤ p n / (3 * d n) := by
  obtain ⟨h1, h2⟩ := h.ℓ_bounds
  have hd : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have h1' : (p n : ℝ) ≤ 12 * d n * ℓ n := by exact_mod_cast h1
  have h2' : (3 * d n * ℓ n : ℝ) ≤ p n := by exact_mod_cast h2
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-- `K + 1 ≤ ℓ`. -/
theorem Big.K_succ_le_ℓ (h : Big n) : K n + 1 ≤ ℓ n := by
  have := K_le_d n
  have := h.d_le_ℓ
  omega

/-- `(6(x+3))⁴ ≤ 2^x` from `x = 40` on. -/
private theorem six_mul_pow_four_le {x : ℕ} (hx : 40 ≤ x) : (6 * (x + 3)) ^ 4 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    set A := 6 * (x + 1 + 3)
    set B := 6 * (x + 3)
    have h1 : (8 * A) ^ 4 ≤ (9 * B) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 : (8 * A) ^ 4 = 8 ^ 4 * A ^ 4 := mul_pow 8 A 4
    have h2' : (9 * B) ^ 4 = 9 ^ 4 * B ^ 4 := mul_pow 9 B 4
    have h3 : 8 ^ 4 * A ^ 4 ≤ 8 ^ 4 * (2 * B ^ 4) := by
      have : 9 ^ 4 * B ^ 4 ≤ 8 ^ 4 * (2 * B ^ 4) := by
        rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by norm_num)
      omega
    have h4 := Nat.le_of_mul_le_mul_left h3 (by norm_num)
    calc A ^ 4 ≤ 2 * B ^ 4 := h4
      _ ≤ 2 * 2 ^ x := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (x + 1) := by rw [pow_succ]; ring

/-- The modulus condition `8 d² N + 4d ≤ r/2` of `Moduli.src_good`: with `4d ≤ 2^E`,
`16 d² N ≤ (4d)^(2d+2) ≤ 2^(E(2d+2))`, and `6 E d² ≤ b ≤ 2 d ℓ` from `(6E)⁴ ≤ d`. -/
theorem Big.moduli_room (h : Big n) : 8 * d n ^ 2 * N n + 4 * d n ≤ 2 ^ (ℓ n - 1) := by
  set D := d n with hDdef
  have hD : 1099511627776 ≤ D := h.2
  have hN1 : 1 ≤ N n := oddProd_pos D
  have hN : N n ≤ (4 * D) ^ (2 * D) := oddProd_le D
  have hDN : D ≤ D ^ 2 * N n := by
    calc D ≤ D ^ 2 := Nat.le_self_pow (by norm_num) D
      _ ≤ D ^ 2 * N n := Nat.le_mul_of_pos_right _ hN1
  have h1 : 8 * D ^ 2 * N n + 4 * D ≤ 16 * (D ^ 2 * N n) := by
    have e : 8 * D ^ 2 * N n = 8 * (D ^ 2 * N n) := by ring
    omega
  have h2 : 16 * (D ^ 2 * N n) ≤ (4 * D) ^ (2 * D + 2) := by
    calc 16 * (D ^ 2 * N n) = (4 * D) ^ 2 * N n := by ring
      _ ≤ (4 * D) ^ 2 * (4 * D) ^ (2 * D) := Nat.mul_le_mul_left _ hN
      _ = (4 * D) ^ (2 * D + 2) := by rw [← pow_add, add_comm]
  set x := Nat.log 2 D with hx
  have hx1 : 2 ^ x ≤ D := Nat.pow_log_le_self 2 (by omega)
  have hx2 : D < 2 ^ (x + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have hx40 : 40 ≤ x := by
    rw [hx]
    exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hE : 4 * D ≤ 2 ^ (x + 3) := by
    have e : 2 ^ (x + 3) = 4 * 2 ^ (x + 1) := by rw [pow_add, pow_add]; ring
    omega
  have hroom : 6 * (x + 3) * D ^ 2 ≤ b n :=
    h.mul_sq_le ((six_mul_pow_four_le hx40).trans hx1)
  have hb := h.b_le_two_dℓ
  have hℓ : 3 * (x + 3) * D ≤ ℓ n := by
    have hd : 0 < D := by omega
    have h5 : D * (2 * (3 * (x + 3) * D)) ≤ D * (2 * ℓ n) := by
      calc D * (2 * (3 * (x + 3) * D)) = 6 * (x + 3) * D ^ 2 := by ring
        _ ≤ 2 * (D * ℓ n) := hroom.trans hb
        _ = D * (2 * ℓ n) := by ring
    have := Nat.le_of_mul_le_mul_left h5 hd
    omega
  have hexp : (x + 3) * (2 * D + 2) ≤ ℓ n - 1 := by
    have e : 3 * (x + 3) * D = (x + 3) * (2 * D + 2) + (x + 3) * (D - 2) := by
      rw [show 3 * (x + 3) * D = (x + 3) * (3 * D) by ring, ← Nat.mul_add]
      congr 1; omega
    have : 1 ≤ (x + 3) * (D - 2) := Nat.mul_pos (by omega) (by omega)
    omega
  calc 8 * D ^ 2 * N n + 4 * D ≤ (4 * D) ^ (2 * D + 2) := h1.trans h2
    _ ≤ (2 ^ (x + 3)) ^ (2 * D + 2) := Nat.pow_le_pow_left hE _
    _ = 2 ^ ((x + 3) * (2 * D + 2)) := by rw [← pow_mul]
    _ ≤ 2 ^ (ℓ n - 1) := Nat.pow_le_pow_right (by norm_num) hexp

theorem t_eq_box (hl : 1 ≤ ℓ n) : t n = Moduli.box (d n) (numHalf n) (ℓ n - 1) := by
  funext i
  unfold t Moduli.box axisLen
  split_ifs
  · rfl
  · congr 1; omega

/-- **The moduli at the chosen sizes**: odd, `s_i < t_i`, coprime to `t_i`, pairwise
coprime, `(1 - 2η) t_i < s_i ≤ (1 - η) t_i`, `T/2 < S < T`. -/
theorem Big.good (h : Big n) : Good (s n) (t n) := by
  rw [t_eq_box (by have := h.two_le_ℓ; omega)]
  exact src_good_oddProd h.two_le_d h.moduli_room

theorem Big.bounds_real (h : Big n) (i : Fin (d n)) :
    (1 - 2 * eta n) * t n i < s n i ∧ (s n i : ℝ) ≤ (1 - eta n) * t n i :=
  (h.good.bounds i).real h.one_le_d

theorem Big.S_lt_T (h : Big n) : S n < T n := by
  have := h.good.prod_lt
  rwa [prod_t h.one_le_d] at this

theorem Big.T_lt_two_S (h : Big n) : T n < 2 * S n := by
  have := h.good.prod_gt
  rwa [prod_t h.one_le_d] at this

theorem Big.half_T_lt_S (h : Big n) : (T n : ℝ) / 2 < S n := by
  have : (T n : ℝ) < 2 * S n := by exact_mod_cast h.T_lt_two_S
  linarith

theorem Big.two_dvd_t (h : Big n) (i : Fin (d n)) : 2 ∣ t n i := by
  have := h.two_le_ℓ
  unfold t
  split_ifs
  · exact dvd_pow_self 2 (by omega)
  · exact dvd_pow_self 2 (by omega)

theorem Big.thirteen_le_p (h : Big n) : 13 ≤ p n := by
  have := h.sixteen_le_b; unfold p; omega

private theorem eight_mul_add_le_two_pow (x : ℕ) (hx : 7 ≤ x) : 8 * x + 6 ≤ 2 ^ (x - 1) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    have e : x + 1 - 1 = (x - 1) + 1 := by omega
    rw [e, pow_succ]
    have : 8 ≤ 2 ^ (x - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `u ≤ d`: the width exponent is at most the dimension. -/
theorem Big.alphaU_le_d (h : Big n) : alphaU n ≤ d n := by
  have hD := h.2
  set x := Nat.clog 2 (d n + 1) with hx
  have hx1 : d n + 1 ≤ 2 ^ x := Nat.le_pow_clog one_lt_two _
  have hx7 : 7 ≤ x := by
    by_contra hc
    have : 2 ^ x ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hx2 : 2 ^ (x - 1) < d n + 1 := by
    exact Nat.pow_pred_clog_lt_self one_lt_two (by omega)
  have hb := b_lt_d_succ_pow n
  have hb8 : 6 * b n ≤ 2 ^ (8 * x + 3) := by
    have h8 : (d n + 1) ^ upperPower ≤ (2 ^ x) ^ 8 := Nat.pow_le_pow_left hx1 8
    rw [← pow_mul] at h8
    have e : 2 ^ (8 * x + 3) = 8 * 2 ^ (x * 8) := by rw [pow_add, mul_comm x 8]; ring
    omega
  have hc := Nat.clog_le_of_le_pow hb8
  have := eight_mul_add_le_two_pow x hx7
  unfold alphaU p; omega

/-- `α² ≤ p`. -/
theorem Big.alpha_sq_le_p (h : Big n) : alpha n ^ 2 ≤ p n := by
  have h1 := alpha_sq_lt n
  have h2 := h.alphaU_le_d
  have h3 := d_le_b n
  unfold p; omega

/-- `η < θ_i`. -/
theorem Big.eta_lt_theta (h : Big n) (i : Fin (d n)) : eta n < (t n i : ℝ) / s n i - 1 := by
  have hg := h.good
  have hs : (0 : ℝ) < s n i := by exact_mod_cast (hg.odd i).pos
  have hd : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have hu : (4 * d n * s n i + t n i : ℝ) ≤ 4 * d n * t n i := by
    exact_mod_cast (hg.bounds i).upper
  have hlt : (s n i : ℝ) < t n i := by exact_mod_cast hg.lt i
  have e : (t n i : ℝ) / s n i - 1 = (t n i - s n i) / s n i := by field_simp
  rw [e, eta, div_lt_div_iff₀ (by positivity) hs]
  nlinarith

/-- `1/(4p) ≤ θ_i`: the small-gap condition of the banded `B̃₀`. -/
theorem Big.quarter_p_le_theta (h : Big n) (i : Fin (d n)) :
    1 / (4 * (p n : ℝ)) ≤ (t n i : ℝ) / s n i - 1 := by
  have h1 := h.eta_lt_theta i
  have hd : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hdp : (d n : ℝ) ≤ p n := by
    have := d_le_b n
    exact_mod_cast (show d n ≤ p n by unfold p; omega)
  have h2 : 1 / (4 * (p n : ℝ)) ≤ eta n := by
    unfold eta
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- `16 d α² ≤ b`. -/
theorem Big.sixteen_d_alpha_sq_le_b (h : Big n) : 16 * d n * alpha n ^ 2 ≤ b n := by
  have h1 := alpha_sq_lt n
  have h2 := h.alphaU_le_d
  have h7 := h.mul_sq_le (F := 64) (by have := h.2; norm_num; omega)
  have hD := h.2
  have h3 : 64 * d n ^ 2 ≤ b n := h7
  have h4 : 16 * d n * alpha n ^ 2 ≤ 16 * d n * (4 * d n) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : 16 * d n * (4 * d n) = 64 * d n ^ 2 := by ring
  omega

/-- `γ ≤ b/4`, integer form `4γ ≤ b`. -/
theorem Big.four_gamma_le_b (h : Big n) : 4 * gamma n ≤ b n := by
  have h4 := h.sixteen_d_alpha_sq_le_b
  have hA := two_le_alpha h.1
  have hA4 : 4 ≤ alpha n ^ 2 := by nlinarith
  have h6 : 4 * d n ≤ d n * alpha n ^ 2 := by
    calc 4 * d n = d n * 4 := by ring
      _ ≤ d n * alpha n ^ 2 := Nat.mul_le_mul_left _ hA4
  show 4 * (d n * (3 * alpha n ^ 2 + 2)) ≤ b n
  have e : 4 * (d n * (3 * alpha n ^ 2 + 2)) = 12 * (d n * alpha n ^ 2) + 8 * d n := by ring
  have e2 : 16 * d n * alpha n ^ 2 = 16 * (d n * alpha n ^ 2) := by ring
  omega

/-- The small-gap width condition of the banded `B̃₀`: `8p ≤ 2^(α²)`. -/
theorem Big.band_width (_h : Big n) : 8 * p n ≤ 2 ^ (alpha n ^ 2) := by
  have h1 : p n ≤ 2 ^ Nat.clog 2 (p n) := Nat.le_pow_clog one_lt_two _
  have h2 : 2 ^ alphaU n ≤ 2 ^ (alpha n ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (alphaU_le_alpha_sq n)
  have e : 2 ^ alphaU n = 8 * 2 ^ Nat.clog 2 (p n) := by unfold alphaU; rw [pow_add]; ring
  omega

/-- The small-gap budget of the banded `B̃₀`: `α² d ≤ p`. -/
theorem Big.band_budget (h : Big n) : ((alpha n : ℝ)) ^ 2 * (d n : ℝ) ≤ p n := by
  have h4 := h.sixteen_d_alpha_sq_le_b
  have : alpha n ^ 2 * d n ≤ p n := by unfold p; nlinarith
  exact_mod_cast this

theorem Big.gamma_le_real (h : Big n) : (gamma n : ℝ) ≤ b n / 4 := by
  have : (4 * gamma n : ℝ) ≤ b n := by exact_mod_cast h.four_gamma_le_b
  linarith

/-- No wraparound: `2q - 2 < S`, as `2q ≤ S + 1`. -/
theorem Big.two_q_le (h : Big n) : 2 * q n ≤ S n + 1 := by
  have hb := one_le_b h.1
  have h1 : b n * q n ≤ n + b n - 1 := Nat.mul_div_le _ _
  have h2 := four_mul_le_bT h.1
  have h3 := h.T_lt_two_S
  by_contra hc
  push Not at hc
  have h4 : T n + 5 ≤ 4 * q n := by omega
  have h5 : b n * (T n + 5) ≤ b n * (4 * q n) := Nat.mul_le_mul_left _ h4
  have e1 : b n * (T n + 5) = b n * T n + 5 * b n := by ring
  have e2 : b n * (4 * q n) = 4 * (b n * q n) := by ring
  omega

theorem Big.two_q_sub_two_lt (h : Big n) : 2 * q n - 2 < S n := by
  have := h.two_q_le
  have : 0 < S n := by
    have := h.T_lt_two_S
    omega
  omega

/-- The digit-count hypothesis `hS` of `ExactRecovery.exact_product` at `k = b`. -/
theorem Big.digits_length_le (h : Big n) {x y : List Bool} (hx : x.length = n)
    (hy : y.length = n) :
    (IntegerMultBounds.NLogN.digitsOf (b n) x).length +
      (IntegerMultBounds.NLogN.digitsOf (b n) y).length ≤ S n + 1 := by
  have hb := one_le_b h.1
  have h1 := IntegerMultBounds.NLogN.digitsOf_length_le_div hb x
  have h2 := IntegerMultBounds.NLogN.digitsOf_length_le_div hb y
  rw [hx] at h1
  rw [hy] at h2
  have := h.two_q_le
  unfold q at this
  omega

/-- The size hypotheses of `ExactRecovery.margins_of_sizes` with `k = b`, `L = log₂ T`. -/
theorem Big.margin_hyps (h : Big n) :
    S n ≤ T n ∧ 2 ≤ T n ∧ T n < 2 ^ b n ∧ 1 ≤ logT n ∧ logT n < b n ∧
      (gamma n : ℝ) ≤ b n / 4 ∧ p n = 6 * b n := by
  have hL := h.one_le_logT
  have hLb := h.logT_bounds.2
  refine ⟨h.S_lt_T.le, ?_, ?_, hL, hLb, h.gamma_le_real, rfl⟩
  · unfold T
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ logT n := Nat.pow_le_pow_right (by norm_num) hL
  · exact Nat.pow_lt_pow_right (by norm_num) hLb

end Big

/-! ### Eventual statements -/

theorem tendsto_ℓ : Tendsto ℓ atTop atTop :=
  tendsto_atTop.2 fun M => (eventually_big.and (tendsto_atTop.1 tendsto_d M)).mono
    fun _ h => by have := h.1.d_le_ℓ; have := h.2; omega

/-- `b ≤ 4ℓ²`, hence `p ≤ 24 ℓ²`. -/
theorem Big.p_le_ℓ_sq {n : ℕ} (h : Big n) : p n ≤ 24 * ℓ n ^ 2 := by
  have h1 := h.b_le_two_dℓ
  have h2 := h.pow_le_b (k := 2) (by norm_num)
  have hd : 0 < d n ^ 2 := by have := h.one_le_d; positivity
  have h3 : d n ^ 2 * b n ≤ d n ^ 2 * (4 * ℓ n ^ 2) := by
    calc d n ^ 2 * b n ≤ b n * b n := Nat.mul_le_mul_right _ h2
      _ ≤ (2 * (d n * ℓ n)) * (2 * (d n * ℓ n)) := Nat.mul_le_mul h1 h1
      _ = d n ^ 2 * (4 * ℓ n ^ 2) := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 hd
  unfold p
  omega

/-- `r` exceeds every fixed power of `p`. -/
theorem eventually_pow_p_le_r (C : ℕ) : ∀ᶠ n in atTop, p n ^ C ≤ r n := by
  filter_upwards [eventually_big,
    tendsto_ℓ.eventually (eventually_mul_pow_le_two_pow (24 ^ C) (2 * C))] with n h hl
  calc p n ^ C ≤ (24 * ℓ n ^ 2) ^ C := Nat.pow_le_pow_left h.p_le_ℓ_sq C
    _ = 24 ^ C * ℓ n ^ (2 * C) := by rw [mul_pow, ← pow_mul]
    _ ≤ r n := hl

theorem tendsto_clog_succ : Tendsto (fun k : ℕ => Nat.clog 2 (k + 1)) atTop atTop :=
  tendsto_atTop.2 fun m => eventually_atTop.2 ⟨2 ^ m, fun k hk => by
    have := Nat.clog_mono_right 2 (show 2 ^ m ≤ k + 1 by omega)
    rwa [Nat.clog_pow 2 m one_lt_two] at this⟩

/-- `C (3 + M ⌈log₂ (k+1)⌉) ≤ k` for all large `k`. -/
theorem eventually_log_le (C M : ℕ) :
    ∀ᶠ k : ℕ in atTop, C * (3 + M * Nat.clog 2 (k + 1)) ≤ k := by
  filter_upwards [eventually_ge_atTop 1, tendsto_clog_succ.eventually
    ((eventually_mul_pow_le_two_pow (2 * (C * (3 + M))) 1).and (eventually_ge_atTop 1))]
    with k hk ⟨hc, hc1⟩
  set c := Nat.clog 2 (k + 1)
  rw [pow_one] at hc
  have h1 : 2 ^ (c - 1) < k + 1 := by
    have := Nat.pow_pred_clog_lt_self (b := 2) one_lt_two (x := k + 1) (by omega)
    rwa [Nat.pred_eq_sub_one] at this
  have e : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
  have h2 : C * (3 + M * c) ≤ C * (3 + M) * c := by
    rw [mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have h3 : 2 * (C * (3 + M)) * c = 2 * (C * (3 + M) * c) := by ring
  omega

/-- `K / log p → ∞`: for every `C`, eventually `C ⌈log₂ p⌉ ≤ K`. -/
theorem eventually_clog_p_le_K (C : ℕ) : ∀ᶠ n in atTop, C * Nat.clog 2 (p n) ≤ K n := by
  filter_upwards [tendsto_K.eventually (eventually_log_le C (cExp * upperPower))] with n hn
  exact (Nat.mul_le_mul_left _ (clog_p_le n)).trans hn

/-- `K / log p → ∞` with the real logarithm: for every real `C`, eventually
`C log₂ p ≤ K`. -/
theorem eventually_logb_p_le_K (C : ℝ) : ∀ᶠ n in atTop, C * Real.logb 2 (p n) ≤ K n := by
  filter_upwards [eventually_clog_p_le_K ⌈C⌉₊, eventually_big] with n hn h
  have hp : (1 : ℝ) ≤ p n := by exact_mod_cast (h.thirteen_le_p.trans' (by norm_num))
  have hlog0 : 0 ≤ Real.logb 2 (p n) := Real.logb_nonneg one_lt_two hp
  have hlog : Real.logb 2 (p n) ≤ Nat.clog 2 (p n) := by
    have h1 : ((p n : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (p n) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog one_lt_two (p n)
    have h2 := Real.logb_le_logb_of_le one_lt_two (by linarith) h1
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two,
      mul_one] at h2
  have hC : C ≤ ⌈C⌉₊ := Nat.le_ceil C
  have hK : ((⌈C⌉₊ * Nat.clog 2 (p n) : ℕ) : ℝ) ≤ K n := by exact_mod_cast hn
  push_cast at hK
  calc C * Real.logb 2 (p n) ≤ ⌈C⌉₊ * Real.logb 2 (p n) := by
        exact mul_le_mul_of_nonneg_right hC hlog0
    _ ≤ ⌈C⌉₊ * Nat.clog 2 (p n) := by
        exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ K n := hK

/-- `ℓ / K → ∞`: for every `C`, eventually `C K ≤ ℓ`. -/
theorem eventually_mul_K_le_ℓ (C : ℕ) : ∀ᶠ n in atTop, C * K n ≤ ℓ n := by
  filter_upwards [eventually_big, tendsto_atTop.1 tendsto_d ((2 * C) ^ 4)] with n h hC
  have h1 := h.mul_sq_le hC
  have h2 := h.b_le_two_dℓ
  have h3 : C * K n ≤ C * d n := Nat.mul_le_mul_left _ (K_le_d n)
  have hd := h.one_le_d
  have h4 : d n * (2 * (C * d n)) ≤ d n * (2 * ℓ n) := by
    calc d n * (2 * (C * d n)) = 2 * C * d n ^ 2 := by ring
      _ ≤ 2 * (d n * ℓ n) := h1.trans h2
      _ = d n * (2 * ℓ n) := by ring
  have := Nat.le_of_mul_le_mul_left h4 hd
  omega

/-- `2 d p² ≤ T log₂ T` (the hypothesis `hsmall` of the source-transform assembly). -/
theorem eventually_small : ∀ᶠ n in atTop, 2 * d n * p n ^ 2 ≤ T n * logT n := by
  filter_upwards [eventually_big, tendsto_b.eventually (eventually_mul_pow_le_two_pow 72 4)]
    with n h hb
  have h1 := four_mul_le_bT h.1
  have h2 := two_pow_b_lt h.1
  have hL := h.one_le_logT
  have hdb := d_le_b n
  have hB := h.sixteen_le_b
  -- `b · 72 b³ ≤ 2^b < 2n ≤ b T`, so `72 b³ < T`
  have h3 : b n * (72 * b n ^ 3) < b n * T n := by
    have : b n * (72 * b n ^ 3) = 72 * b n ^ 4 := by ring
    omega
  have h4 : 72 * b n ^ 3 < T n := Nat.lt_of_mul_lt_mul_left h3
  have h5 : 2 * d n * p n ^ 2 ≤ 72 * b n ^ 3 := by
    unfold p
    have : d n * b n ^ 2 ≤ b n * b n ^ 2 := Nat.mul_le_mul_right _ hdb
    nlinarith
  have h6 : T n ≤ T n * logT n := Nat.le_mul_of_pos_right _ hL
  omega

/-- The threshold of `ExactRecovery.eventually_threshold` at `k = b`. -/
theorem eventually_threshold :
    ∀ᶠ n in atTop, 896 * (b n : ℝ) * (2 : ℝ) ^ ((b n : ℝ) / 4) < 2 ^ b n :=
  tendsto_b.eventually IntegerMultBounds.ExactRecovery.eventually_threshold

/-- The precision margins of exact recovery, `E_s = 9 · 2^γ T log₂ T`:
`E_s ≤ 2^p / 100` and `2^(2b+4) S² (3 E_s + 2) < 2^p / 2`. -/
theorem eventually_margins :
    ∀ᶠ n in atTop,
      9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100 ∧
        (2 : ℝ) ^ (2 * b n + 4) * S n ^ 2 * (3 * (9 * (2 : ℝ) ^ gamma n * T n * logT n) + 2) <
          2 ^ p n / 2 := by
  filter_upwards [eventually_big, eventually_threshold] with n h hthr
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h.margin_hyps
  exact IntegerMultBounds.ExactRecovery.margins_of_sizes h1 h2 h3 h4 h5 h6 hthr

end IntegerMultBounds.MathlibTM2.Mult.Sizes
