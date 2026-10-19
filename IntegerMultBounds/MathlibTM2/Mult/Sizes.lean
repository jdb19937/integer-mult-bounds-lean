module

public import IntegerMultBounds.MathlibTM2.Mult.Moduli
public import IntegerMultBounds.Primes.Moduli
import IntegerMultBounds.Primes.Window
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
functions of the operand length `n`, with the retuned constants `ε = 31/64`, `c = 2^{-32}`:

* `b = ⌈log₂ n⌉`, `p = 6b`;
* `d = ⌊b^ε⌋`, the largest `d` with `d^64 ≤ b^31`; `K = ⌊d^c⌋`, the largest `K` with
  `K^(2^32) ≤ d`;
* `T = 2^logT`, the power of two in `[4n/b, 8n/b)`; `ℓ = ⌈logT / d⌉`, `r = 2^ℓ`;
* axis lengths `t_i ∈ {r/2, r}`: the first `numHalf = dℓ - logT` are `r/2`, the rest (in
  particular the last) are `r`;
* `α`, the least integer with `α^4 ≥ 12 d² b`; `γ = d (2α² + 2)`; `η = 1/(4d)`;
  `q = ⌈n/b⌉`;
* source lengths `s_i`, the prime moduli `Primes.primeSrc`: the first `numHalf` primes of the
  window `((1 - 2η) r/2, (1 - η) r/2]` and the first `d - numHalf` primes of the window
  `((1 - 2η) r, (1 - η) r]` (`srcLen`), and `S = ∏ s_i`.

The windows hold enough primes for all large `n` (`PrimeSupply`, `eventually_primeSupply`, from
the strong prime number theorem). With the chunk room `256 d^7 < ℓ^8` and the Gaussian width room
`64 d (⌈log₂ p⌉ + 3) ≤ b` it forms the regime facts `BigFacts`, eventual statements whose
thresholds are existential; `bigDim` names a dimension from which on they hold. None of them
needs `d² ≤ b`: they use `d^64 ≤ b^31` and `b^33 ≤ (2ℓ)^64` (`b_pow_le_ℓ`).

Every relation used downstream is proved for all large `n`, as a `Filter.Eventually` along
`atTop`. Most of them follow deterministically from the regime
`Big n : 2 ≤ n ∧ 2^192 + bigDim ≤ d n` (`eventually_big`), whose consequences are the `Big.*`
lemmas:

* `prod_t`, `t_last`, `t_eq`: `∏ t_i = T`, `t_d = r`, `t_i ∈ {r/2, r}`;
* `volume_bounds`: `24 n ≤ T p < 48 n`; `Big.logT_bounds`: `b ≤ 2 log₂ T`, `log₂ T < b`;
* `d_pow_le_p`, `p_lt_pow`, `d_rpow_bounds`: `p^ε/12 ≤ d ≤ p^ε`;
* `Big.ℓ_bounds`, `Big.ℓ_bounds_real`: `p/(12d) ≤ ℓ ≤ p/(3d)`; `Big.K_succ_le_ℓ`;
* `two_le_alpha`, `alpha_sq_lt`, `Big.alpha_sq_le_p`, `Big.eta_lt_theta`,
  `Big.quarter_p_le_theta`, `Big.band_width`, `Big.band_budget`;
* `Big.four_gamma_le_b`, `Big.gamma_le_real`: `γ ≤ b/4`;
* `Big.primeSupply`, `Big.good`: the moduli (`Moduli.Good`), with `Big.S_lt_T`, `Big.T_lt_two_S`;
* `Big.two_q_le`, `Big.digits_length_le`: no wraparound, `2q - 2 < S`;
* `Big.margin_hyps`, `eventually_threshold`, `eventually_margins`: the hypotheses and the
  conclusion of `ExactRecovery.margins_of_sizes` at `k = b`, `L = log₂ T`;
* `eventually_pow_p_le_r`, `eventually_clog_p_le_K`, `eventually_logb_p_le_K`,
  `eventually_small`: the growth statements `p^C ≤ r`,
  `C log₂ p ≤ K`, `C K ≤ ℓ`, `2 d p² ≤ T log₂ T`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Sizes

open Filter Finset IntegerMultBounds.MathlibTM2.Mult.Moduli
open IntegerMultBounds.Primes (primeSrc windowPrime winLo winHi)
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
def rootExp : ℕ := 64

/-- The power applied before taking the integer root. -/
def rootNumerator : ℕ := 31

/-- A coarse upper growth power, not the reciprocal of `epsilon`. -/
def upperPower : ℕ := 8

/-- `2^32`, the root index of the legacy chunk. -/
def cExp : ℕ := 2 ^ 32

theorem rootExp_ne : rootExp ≠ 0 := by decide
theorem upperPower_ne : upperPower ≠ 0 := by decide
theorem cExp_ne : cExp ≠ 0 := by unfold cExp; positivity
/-- The dyadic dimension exponent `31/64`. -/
noncomputable def epsilon : ℝ := (rootNumerator : ℝ) / rootExp

theorem epsilon_eq : epsilon = (31 : ℝ) / 64 := by norm_num [epsilon, rootNumerator, rootExp]

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

/-! ### The parameters -/

/-- `b = ⌈log₂ n⌉`. -/
def b (n : ℕ) : ℕ := Nat.clog 2 n

/-- The working precision `p = 6b`. -/
def p (n : ℕ) : ℕ := 6 * b n

/-- The dimension `d = ⌊b^ε⌋`: the largest `d` with `d^64 ≤ b^31`. -/
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

/-- The prime supply at `n`: `d ≥ 2`, `ℓ ≥ 4`, and both windows, below `R = 2^(ℓ-1)` and
below `2R`, hold at least `d` primes. -/
def PrimeSupply (n : ℕ) : Prop :=
  2 ≤ d n ∧ 4 ≤ ℓ n ∧
    d n ≤ ((Ioc (winLo (d n) (2 ^ (ℓ n - 1))) (winHi (d n) (2 ^ (ℓ n - 1)))).filter
      Nat.Prime).card ∧
    d n ≤ ((Ioc (winLo (d n) (2 * 2 ^ (ℓ n - 1))) (winHi (d n) (2 * 2 ^ (ℓ n - 1)))).filter
      Nat.Prime).card

instance (n : ℕ) : Decidable (PrimeSupply n) := by
  unfold PrimeSupply
  infer_instance

/-- The source length `s_i` on ℕ indices: the prime moduli `Primes.primeSrc` with `R = r/2`
under the prime supply, and the primes above `2` otherwise. -/
def srcLen (n i : ℕ) : ℕ :=
  if PrimeSupply n then primeSrc (d n) (numHalf n) (2 ^ (ℓ n - 1)) i else windowPrime 2 i

/-- The source lengths `s_i`. -/
def s (n : ℕ) : Fin (d n) → ℕ := fun i => srcLen n i

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
  have hp := Nat.pow_le_pow_left hb 31
  have hroot := b_pow_lt_d_succ_pow n
  have hmono : (d n+1)^64≤(d n+1)^248 := Nat.pow_le_pow_right (by omega) (by decide)
  rw [←pow_mul] at hp
  norm_num only [Nat.mul] at hp
  change b n ^ 31 < (d n+1)^64 at hroot
  omega

theorem le_d_iff {D : ℕ} : D ≤ d n ↔ D ^ rootExp ≤ b n ^ rootNumerator :=
  le_iroot_iff rootExp_ne

theorem one_le_d (hn : 2 ≤ n) : 1 ≤ d n :=
  one_le_iroot rootExp_ne (one_le_pow₀ (one_le_b hn))

/-- `d ≤ b`, from `d^64 ≤ b^31`. -/
theorem d_le_b (n : ℕ) : d n ≤ b n := by
  have hroot : d n ^ 64 ≤ b n ^ 31 := d_pow_le n
  by_contra hc
  have h1 : b n ^ 64 < d n ^ 64 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : b n ^ 31 ≤ b n ^ 64 := by
    rcases Nat.eq_zero_or_pos (b n) with hb | hb
    · simp [hb]
    · exact Nat.pow_le_pow_right hb (by norm_num)
  omega

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

/-- `d^33 ≤ (2ℓ)^31` for every `n ≥ 2`: `d^64 ≤ b^31 ≤ (2 log₂ T)^31 ≤ (2 d ℓ)^31`. -/
theorem d_pow_le_ℓ (hn : 2 ≤ n) : d n ^ 33 ≤ (2 * ℓ n) ^ 31 := by
  have hd := one_le_d hn
  have h1 := b_le_two_mul_logT hn
  have h2 := logT_le_dℓ hd
  have hroot : d n ^ 64 ≤ b n ^ 31 := d_pow_le n
  have h3 : b n ^ 31 ≤ (2 * (d n * ℓ n)) ^ 31 := Nat.pow_le_pow_left (by omega) 31
  have h4 : d n ^ 31 * d n ^ 33 ≤ d n ^ 31 * (2 * ℓ n) ^ 31 := by
    calc d n ^ 31 * d n ^ 33 = d n ^ 64 := by ring
      _ ≤ (2 * (d n * ℓ n)) ^ 31 := hroot.trans h3
      _ = d n ^ 31 * (2 * ℓ n) ^ 31 := by ring
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

/-- `b^33 ≤ (2ℓ)^64` for every `n ≥ 2`: `b^64 ≤ (2dℓ)^64 = d^64 (2ℓ)^64 ≤ b^31 (2ℓ)^64`. The axis
length grows like `b^(1-ε)` for every dimension exponent `ε`. -/
theorem b_pow_le_ℓ (hn : 2 ≤ n) : b n ^ 33 ≤ (2 * ℓ n) ^ 64 := by
  have hd := one_le_d hn
  have h1 := b_le_two_mul_logT hn
  have h2 := logT_le_dℓ hd
  have hroot : d n ^ 64 ≤ b n ^ 31 := d_pow_le n
  have hb1 := one_le_b hn
  have h3 : b n ^ 64 ≤ (2 * (d n * ℓ n)) ^ 64 := Nat.pow_le_pow_left (by omega) 64
  have h4 : b n ^ 31 * b n ^ 33 ≤ b n ^ 31 * (2 * ℓ n) ^ 64 := by
    calc b n ^ 31 * b n ^ 33 = b n ^ 64 := by ring
      _ ≤ (2 * (d n * ℓ n)) ^ 64 := h3
      _ = d n ^ 64 * (2 * ℓ n) ^ 64 := by ring
      _ ≤ b n ^ 31 * (2 * ℓ n) ^ 64 := Nat.mul_le_mul_right _ hroot
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

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

/-! ### The prime supply -/

section Supply

variable {n : ℕ}

theorem d_mono : Monotone d := fun _ _ hxy =>
  (le_iroot_iff rootExp_ne).2 ((iroot_pow_le rootExp_ne _).trans
    (Nat.pow_le_pow_left (Nat.clog_mono_right 2 hxy) _))

theorem tendsto_ℓ : Tendsto ℓ atTop atTop := by
  refine tendsto_atTop.2 fun M => ((eventually_ge_atTop 2).and
    (tendsto_atTop.1 tendsto_b ((2 * M) ^ 2 + 1))).mono fun n h => ?_
  have h1 := b_pow_le_ℓ h.1
  by_contra hc
  have hc' : ℓ n < M := not_le.mp hc
  have h2 : (2 * ℓ n) ^ 64 < (2 * M) ^ 64 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h3 : (2 * M) ^ 64 ≤ b n ^ 33 := by
    calc (2 * M) ^ 64 = ((2 * M) ^ 2) ^ 32 := by ring
      _ ≤ b n ^ 32 := Nat.pow_le_pow_left (by omega) 32
      _ ≤ b n ^ 33 := Nat.pow_le_pow_right (by have := h.2; omega) (by norm_num)
  omega

/-- **The prime supply.** For all large `n` both windows hold at least `d` primes:
`d^33 ≤ (2ℓ)^31 ≤ (ℓ - 1)^62`, so `d ≤ (ℓ - 1)^2`, and `primes_in_window_two_pow 2` applies
below `2^(ℓ-1)` and below `2^ℓ`. -/
theorem eventually_primeSupply : ∀ᶠ n in atTop, PrimeSupply n := by
  have hℓ1 : Tendsto (fun n => ℓ n - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp tendsto_ℓ
  filter_upwards [eventually_ge_atTop 2, tendsto_atTop.1 tendsto_d 8,
    hℓ1.eventually (Primes.window_card_two_pow 2),
    tendsto_ℓ.eventually (Primes.window_card_two_pow 2),
    tendsto_ℓ.eventually (eventually_ge_atTop 4)] with n hn hd8 h₁ h₂ hl4
  have hd1 : 1 ≤ d n := by omega
  have hsq : 2 * ℓ n ≤ (ℓ n - 1) ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, ℓ n = m + 4 := ⟨ℓ n - 4, by omega⟩
    rw [hm, show m + 4 - 1 = m + 3 by omega]
    nlinarith
  have hdl : d n ≤ (ℓ n - 1) ^ 2 := by
    have h33 := d_pow_le_ℓ hn
    have h1 : (2 * ℓ n) ^ 31 ≤ ((ℓ n - 1) ^ 2) ^ 33 :=
      (Nat.pow_le_pow_left hsq 31).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp (h33.trans h1)
  have hsq' : (ℓ n - 1) ^ 2 ≤ ℓ n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  have e2 : 2 * 2 ^ (ℓ n - 1) = 2 ^ ℓ n := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨by omega, hl4, ?_, ?_⟩
  · rw [Primes.winLo_two_pow hd1, Primes.winHi_two_pow hd1]
    exact h₁ (d n) hd1 (by omega)
  · rw [e2, Primes.winLo_two_pow hd1, Primes.winHi_two_pow hd1]
    exact h₂ (d n) hd1 (by omega)

/-- `r` exceeds every fixed power of `p`: `p^33 = 6^33 b^33 ≤ 6^33 (2ℓ)^64`. -/
theorem eventually_pow_p_le_r (C : ℕ) : ∀ᶠ n in atTop, p n ^ C ≤ r n := by
  filter_upwards [eventually_ge_atTop 2,
    tendsto_ℓ.eventually (eventually_mul_pow_le_two_pow ((6 ^ 33 * 2 ^ 64) ^ C) (64 * C))]
    with n hn hl
  have hb := b_pow_le_ℓ hn
  have hp33 : p n ^ 33 ≤ 6 ^ 33 * 2 ^ 64 * ℓ n ^ 64 := by
    calc p n ^ 33 = 6 ^ 33 * b n ^ 33 := by unfold p; rw [mul_pow]
      _ ≤ 6 ^ 33 * (2 * ℓ n) ^ 64 := Nat.mul_le_mul_left _ hb
      _ = 6 ^ 33 * 2 ^ 64 * ℓ n ^ 64 := by rw [mul_pow, mul_assoc]
  have h1 : (p n ^ C) ^ 33 ≤ (6 ^ 33 * 2 ^ 64) ^ C * ℓ n ^ (64 * C) := by
    calc (p n ^ C) ^ 33 = (p n ^ 33) ^ C := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (6 ^ 33 * 2 ^ 64 * ℓ n ^ 64) ^ C := Nat.pow_le_pow_left hp33 C
      _ = (6 ^ 33 * 2 ^ 64) ^ C * ℓ n ^ (64 * C) := by rw [mul_pow, ← pow_mul]
  have h2 : 2 ^ ℓ n ≤ (2 ^ ℓ n) ^ 33 := Nat.le_self_pow (by norm_num) _
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp ((h1.trans hl).trans h2)

/-- The chunk room `2^8 d^7 < ℓ^8`: the compact chunk `⌊d^(7/8)⌋` (`CompactSizes.Kroot`) stays
below `ℓ/2` eventually, since `(7/8) ε < 1 - ε`. From `d^64 ≤ b^31` and `b^33 ≤ (2ℓ)^64`:
`(2^8 d^7)^64 ≤ 2^512 b^217 < 2^(-512) b^264 ≤ ℓ^512` once `b^47 > 2^1024`. -/
theorem eventually_chunk_room : ∀ᶠ n in atTop, 2 ^ 8 * d n ^ 7 < ℓ n ^ 8 := by
  filter_upwards [eventually_ge_atTop 2, tendsto_atTop.1 tendsto_b (2 ^ 22)] with n hn hb
  have hroot : d n ^ 64 ≤ b n ^ 31 := d_pow_le n
  have hℓ := b_pow_le_ℓ hn
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 := ⟨_, rfl⟩
  rw [← ht] at hℓ hb ⊢
  have ht1 : 1 < t := by omega
  have hb1 : 0 < b n := lt_of_lt_of_le (Nat.pow_pos (by omega)) hb
  have h1 : (t ^ 8 * d n ^ 7) ^ 64 ≤ t ^ 512 * b n ^ 217 := by
    calc (t ^ 8 * d n ^ 7) ^ 64 = t ^ 512 * (d n ^ 64) ^ 7 := by ring
      _ ≤ t ^ 512 * (b n ^ 31) ^ 7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hroot 7)
      _ = t ^ 512 * b n ^ 217 := by ring
  have h2 : b n ^ 264 ≤ t ^ 512 * ℓ n ^ 512 := by
    calc b n ^ 264 = (b n ^ 33) ^ 8 := by ring
      _ ≤ ((t * ℓ n) ^ 64) ^ 8 := Nat.pow_le_pow_left hℓ 8
      _ = t ^ 512 * ℓ n ^ 512 := by ring
  have h3 : t ^ 1024 < b n ^ 47 := by
    have h10 : 1 < t ^ 10 := Nat.one_lt_pow (by norm_num) ht1
    have hpos : 0 < t ^ 1024 := pow_pos (Nat.lt_trans Nat.zero_lt_one ht1) 1024
    calc t ^ 1024 < t ^ 1024 * t ^ 10 := lt_mul_of_one_lt_right hpos h10
      _ = (t ^ 22) ^ 47 := by ring
      _ ≤ b n ^ 47 := Nat.pow_le_pow_left hb 47
  have hpos : 0 < b n ^ 217 := Nat.pow_pos hb1
  have h4 : t ^ 512 * (t ^ 512 * b n ^ 217) < t ^ 512 * ℓ n ^ 512 := by
    calc t ^ 512 * (t ^ 512 * b n ^ 217) = t ^ 1024 * b n ^ 217 := by ring
      _ < b n ^ 47 * b n ^ 217 := Nat.mul_lt_mul_of_pos_right h3 hpos
      _ = b n ^ 264 := by ring
      _ ≤ t ^ 512 * ℓ n ^ 512 := h2
  have h5 : (t ^ 8 * d n ^ 7) ^ 64 < (ℓ n ^ 8) ^ 64 := by
    have := Nat.lt_of_mul_lt_mul_left h4
    calc (t ^ 8 * d n ^ 7) ^ 64 ≤ t ^ 512 * b n ^ 217 := h1
      _ < ℓ n ^ 512 := this
      _ = (ℓ n ^ 8) ^ 64 := by ring
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h5

/-- The Gaussian width room `64 d (⌈log₂ p⌉ + 3) ≤ b`: `d ≤ b^(31/64)` against a logarithm. -/
theorem eventually_gauss_room : ∀ᶠ n in atTop, 64 * d n * (Nat.clog 2 (p n) + 3) ≤ b n := by
  have hm : Tendsto (fun n => Nat.clog 2 (b n)) atTop atTop :=
    tendsto_atTop.2 fun M => (tendsto_atTop.1 tendsto_b (2 ^ M)).mono fun n h => by
      have := Nat.clog_mono_right 2 h
      rwa [Nat.clog_pow 2 M one_lt_two] at this
  filter_upwards [eventually_ge_atTop 2, tendsto_atTop.1 tendsto_b 2,
    hm.eventually (eventually_mul_pow_le_two_pow (2 ^ 481) 64),
    hm.eventually (eventually_ge_atTop 16)] with n hn hb2 hpow hm16
  obtain ⟨m, hmdef⟩ : ∃ m, m = Nat.clog 2 (b n) := ⟨_, rfl⟩
  rw [← hmdef] at hpow hm16
  have hroot : d n ^ 64 ≤ b n ^ 31 := d_pow_le n
  have hbm : 2 ^ (m - 1) < b n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) one_lt_two (x := b n) hb2
    rwa [Nat.pred_eq_sub_one, ← hmdef] at this
  have hp : Nat.clog 2 (p n) + 3 ≤ m + 6 := by
    have h8 : p n ≤ 2 ^ 3 * b n := by unfold p; norm_num; omega
    have h := Nat.clog_mono_right 2 h8
    have hle : Nat.clog 2 (2 ^ 3 * b n) ≤ 3 + m := by
      apply Nat.clog_le_of_le_pow
      rw [pow_add, hmdef]
      exact Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two _)
    omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 := ⟨_, rfl⟩
  rw [← ht] at hpow hbm
  have ht1 : 1 ≤ t := by omega
  have hL : (m + 6) ^ 64 ≤ t ^ 64 * m ^ 64 := by
    calc (m + 6) ^ 64 ≤ (t * m) ^ 64 := Nat.pow_le_pow_left (by rw [ht]; omega) 64
      _ = t ^ 64 * m ^ 64 := by ring
  have hb33 : t ^ (33 * (m - 1)) ≤ b n ^ 33 := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left hbm.le 33
  have hm64 : m ^ 64 ≤ t ^ m :=
    (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))).trans hpow
  have hkey : t ^ 384 * (m + 6) ^ 64 ≤ b n ^ 33 := by
    calc t ^ 384 * (m + 6) ^ 64 ≤ t ^ 384 * (t ^ 64 * m ^ 64) := Nat.mul_le_mul_left _ hL
      _ = t ^ 448 * m ^ 64 := by ring
      _ ≤ t ^ 448 * t ^ m := Nat.mul_le_mul_left _ hm64
      _ = t ^ (448 + m) := by rw [pow_add]
      _ ≤ t ^ (33 * (m - 1)) := Nat.pow_le_pow_right ht1 (by omega)
      _ ≤ b n ^ 33 := hb33
  have h64 : (t ^ 6 * d n * (m + 6)) ^ 64 ≤ b n ^ 64 := by
    calc (t ^ 6 * d n * (m + 6)) ^ 64 = t ^ 384 * d n ^ 64 * (m + 6) ^ 64 := by ring
      _ ≤ t ^ 384 * b n ^ 31 * (m + 6) ^ 64 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hroot)
      _ = b n ^ 31 * (t ^ 384 * (m + 6) ^ 64) := by ring
      _ ≤ b n ^ 31 * b n ^ 33 := Nat.mul_le_mul_left _ hkey
      _ = b n ^ 64 := by ring
  have h := (Nat.pow_le_pow_iff_left (by norm_num)).mp h64
  have e64 : t ^ 6 = 64 := by rw [ht]; norm_num
  rw [e64] at h
  calc 64 * d n * (Nat.clog 2 (p n) + 3) ≤ 64 * d n * (m + 6) := Nat.mul_le_mul_left _ hp
    _ ≤ b n := h

/-- The facts of the large regime that hold eventually for the present exponents: the prime
supply, the chunk room `2^8 d^7 < ℓ^8`, the Gaussian width room
`64 d (⌈log₂ p⌉ + 3) ≤ b`, `d ≤ 2^(ℓ-1)` and `8p ≤ r`. Each holds eventually for every dimension exponent
`ε < 1` with the chunk exponent `c` of `CompactSizes` in `εc < 1 - ε`. -/
def BigFacts (n : ℕ) : Prop :=
  PrimeSupply n ∧ 2 ^ 8 * d n ^ 7 < ℓ n ^ 8 ∧ 64 * d n * (Nat.clog 2 (p n) + 3) ≤ b n ∧
    d n ≤ 2 ^ (ℓ n - 1) ∧ 8 * p n ≤ r n

theorem eventually_bigFacts : ∀ᶠ n in atTop, BigFacts n := by
  filter_upwards [eventually_primeSupply, eventually_chunk_room, eventually_gauss_room,
    tendsto_ℓ.eventually (eventually_mul_pow_le_two_pow 2 8), eventually_ge_atTop 2,
    eventually_pow_p_le_r 3] with n h₁ h₂ h₃ h₄ hn h₅
  have e8 : (2:ℕ) ^ 8 = 256 := by norm_num
  have h₂' := h₂
  rw [e8] at h₂'
  refine ⟨h₁, h₂, h₃, ?_, ?_⟩
  swap
  · have hb := one_le_b hn
    have hp : 6 ≤ p n := by unfold p; omega
    have hpp : 8 ≤ p n * p n := by nlinarith
    have h8 : 8 * p n ≤ p n * p n * p n := Nat.mul_le_mul_right _ hpp
    have e : p n ^ 3 = p n * p n * p n := by ring
    omega
  have hd := one_le_d hn
  have hl := h₁.2.1
  have h7 : d n ≤ d n ^ 7 := Nat.le_self_pow (by norm_num) _
  have e : 2 ^ ℓ n = 2 * 2 ^ (ℓ n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- A dimension from which on the regime facts hold. -/
noncomputable def bigDim : ℕ := d (Classical.choose (eventually_atTop.1 eventually_bigFacts)) + 1

theorem bigFacts_of_bigDim_le (h : bigDim ≤ d n) : BigFacts n := by
  apply Classical.choose_spec (eventually_atTop.1 eventually_bigFacts)
  by_contra hlt
  have := d_mono (Nat.le_of_lt (not_le.mp hlt))
  unfold bigDim at h
  omega

theorem srcLen_prime (n i : ℕ) : (srcLen n i).Prime := by
  unfold srcLen
  split_ifs
  · exact Primes.primeSrc_prime _ _ _ _
  · exact Primes.windowPrime_prime _ _

theorem three_le_srcLen (n i : ℕ) : 3 ≤ srcLen n i := by
  unfold srcLen
  split_ifs with h
  · have h8 : 8 ≤ 2 ^ (ℓ n - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (ℓ n - 1) := Nat.pow_le_pow_right (by norm_num) (by have := h.2.1; omega)
    exact Primes.three_le_primeSrc (by have := h.1; omega) h8 i
  · exact Primes.lo_lt_windowPrime 2 i

theorem t_eq_box (hl : 1 ≤ ℓ n) : t n = Moduli.box (d n) (numHalf n) (ℓ n - 1) := by
  funext i
  unfold t Moduli.box axisLen
  split_ifs
  · rfl
  · congr 1; omega

/-- Under the prime supply the source lengths are the prime moduli, `Good` for the axes. -/
theorem good_of_primeSupply (h : PrimeSupply n) : Good (s n) (t n) := by
  obtain ⟨hd, hl, h₁, h₂⟩ := h
  have hs : s n = fun i : Fin (d n) => primeSrc (d n) (numHalf n) (2 ^ (ℓ n - 1)) i := by
    funext i
    simp only [s, srcLen, show PrimeSupply n from ⟨hd, hl, h₁, h₂⟩, ↓reduceIte]
  have hnh := numHalf_lt (n := n) (by omega)
  rw [hs, t_eq_box (by omega)]
  exact Primes.primeSrc_good hd hnh.le (by omega) (by omega) (by omega)

/-- The source lengths are pairwise coprime for every `n`. -/
theorem s_pairwise_coprime (n : ℕ) : Pairwise (Nat.Coprime on (s n)) := by
  by_cases h : PrimeSupply n
  · exact (good_of_primeSupply h).pairwise
  · intro i j hij
    have hs : ∀ k : Fin (d n), s n k = windowPrime 2 k := fun k => by simp [s, srcLen, h]
    simp only [Function.onFun, hs]
    exact (Nat.coprime_primes (Primes.windowPrime_prime _ _) (Primes.windowPrime_prime _ _)).2
      ((Primes.windowPrime_strictMono 2).injective.ne (fun e => hij (Fin.ext e)))

end Supply

/-! ### The large regime -/

/-- The regime of the deterministic size relations: `n ≥ 2` and `d ≥ 2^192 + bigDim`, so that
the regime facts hold (`Big.bigFacts`): the prime supply, the chunk room and the Gaussian width
room. -/
def Big (n : ℕ) : Prop :=
  2 ≤ n ∧ 6277101735386680763835789423207666416102355444464034512896 + bigDim ≤ d n

theorem eventually_big : ∀ᶠ n in atTop, Big n :=
  (eventually_ge_atTop 2).and (tendsto_atTop.1 tendsto_d
    (6277101735386680763835789423207666416102355444464034512896 + bigDim))

section Big

variable {n : ℕ}

theorem Big.one_le_d (h : Big n) : 1 ≤ d n := by have := h.2; omega

theorem Big.bigFacts (h : Big n) : BigFacts n := bigFacts_of_bigDim_le (by have := h.2; omega)

theorem Big.sixteen_le_b (h : Big n) : 16 ≤ b n := by
  have := d_le_b n
  have := h.2
  omega

theorem Big.logT_bounds (h : Big n) : b n ≤ 2 * logT n ∧ logT n < b n :=
  ⟨b_le_two_mul_logT h.1, logT_lt_b h.1 (by have := h.sixteen_le_b; omega)⟩

theorem Big.one_le_logT (h : Big n) : 1 ≤ logT n :=
  one_le_logT_of h.1 (by have := h.sixteen_le_b; omega)

theorem Big.primeSupply (h : Big n) : PrimeSupply n := h.bigFacts.1

theorem Big.four_le_ℓ (h : Big n) : 4 ≤ ℓ n := h.primeSupply.2.1

theorem Big.two_le_ℓ (h : Big n) : 2 ≤ ℓ n := by have := h.four_le_ℓ; omega

/-- The chunk room `256 d^7 < ℓ^8`. -/
theorem Big.chunk_room (h : Big n) : 256 * d n ^ 7 < ℓ n ^ 8 := by
  have h1 := h.bigFacts.2.1
  rwa [show (2:ℕ) ^ 8 = 256 by norm_num] at h1

theorem Big.d_le_two_pow_pred_ℓ (h : Big n) : d n ≤ 2 ^ (ℓ n - 1) := h.bigFacts.2.2.2.1

theorem Big.eight_p_le_r (h : Big n) : 8 * p n ≤ r n := h.bigFacts.2.2.2.2

/-- `F d ≤ b` whenever `F^64 ≤ b^33`: `(F d)^64 ≤ b^33 b^31`. -/
theorem mul_d_le_b {F : ℕ} (hF : F ^ 64 ≤ b n ^ 33) : F * d n ≤ b n := by
  have hroot : d n ^ 64 ≤ b n ^ 31 := d_pow_le n
  apply (Nat.pow_le_pow_iff_left (by norm_num : 64 ≠ 0)).mp
  calc (F * d n) ^ 64 = F ^ 64 * d n ^ 64 := by ring
    _ ≤ b n ^ 33 * b n ^ 31 := Nat.mul_le_mul hF hroot
    _ = b n ^ 64 := by ring

theorem Big.eight_d_le_b (h : Big n) : 8 * d n ≤ b n := by
  apply mul_d_le_b
  have hb : 2 ^ 192 ≤ b n := by have := d_le_b n; have := h.2; omega
  calc (8 : ℕ) ^ 64 = 2 ^ 192 := by norm_num
    _ ≤ b n := hb
    _ ≤ b n ^ 33 := Nat.le_self_pow (by norm_num) _

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

/-- `K + 1 ≤ ℓ`: `K^8 ≤ K^(2^32) ≤ d ≤ d^7 < ℓ^8`. -/
theorem Big.K_succ_le_ℓ (h : Big n) : K n + 1 ≤ ℓ n := by
  have hroom := h.chunk_room
  have hK := K_pow_le n
  have hd := h.one_le_d
  by_contra hc
  have h1 : ℓ n ^ 8 ≤ K n ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have h2 : K n ^ 8 ≤ K n ^ cExp := by
    rcases Nat.eq_zero_or_pos (K n) with h0 | h0
    · rw [h0, zero_pow (by norm_num)]; exact Nat.zero_le _
    · exact Nat.pow_le_pow_right h0 (by norm_num [cExp])
  have h3 : d n ≤ d n ^ 7 := Nat.le_self_pow (by norm_num) _
  omega

/-- Under `Big` the source lengths are the prime moduli. -/
theorem Big.srcLen_eq (h : Big n) (i : ℕ) :
    srcLen n i = primeSrc (d n) (numHalf n) (2 ^ (ℓ n - 1)) i := by
  simp only [srcLen, h.primeSupply, ↓reduceIte]

/-- **The moduli at the chosen sizes**: odd, `s_i < t_i`, coprime to `t_i`, pairwise
coprime, `(1 - 2η) t_i < s_i ≤ (1 - η) t_i`, `T/2 < S < T`. -/
theorem Big.good (h : Big n) : Good (s n) (t n) :=
  good_of_primeSupply h.primeSupply

theorem Big.S_lt_T (h : Big n) : S n < T n := by
  have := h.good.prod_lt
  rwa [prod_t h.one_le_d] at this

theorem Big.T_lt_two_S (h : Big n) : T n < 2 * S n := by
  have := h.good.prod_gt
  rwa [prod_t h.one_le_d] at this

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
  have h3 := h.bigFacts.2.2.1
  have h4 : 16 * d n * alpha n ^ 2 ≤ 16 * d n * (4 * alphaU n) :=
    Nat.mul_le_mul_left _ h1.le
  have e : 16 * d n * (4 * alphaU n) = 64 * d n * (Nat.clog 2 (p n) + 3) := by
    unfold alphaU; ring
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
