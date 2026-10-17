module

public import IntegerMultBounds.MathlibTM2.Mult.Pipeline
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Integer numerators of the phase tables

The chirp axis entries `Chirp.axisPhase` and the twist entries `Pipeline.twistPlus`,
`Pipeline.twistMinus` are noncomputable complex numbers built from real fixed-point operations;
their values are dyadic rationals with explicit integer numerators. This file gives those
numerators as functions of natural numbers, in the form a binary machine computes them.

## Taylor sums

For an angle `x = X / 2^Q` (`X : ℤ`) the fixed-point Taylor terms `taylorTerm q x m` are
`u_m = U_m / 2^q` with `U_0 = 2^q`, `U_{m+1} = (U_m X).tdiv (2^Q (m+1))`. Truncation toward zero
is odd, so `U_m = sgn(X)^m M_m` with the natural magnitudes `tblMag |X| q Q m`:
`M_0 = 2^q`, `M_{m+1} = ⌊M_m |X| / (2^Q (m+1))⌋` (`tbl_taylorTerm`). The real part of
`taylorExpI q x n = ∑_{m<n} i^m u_m` collects the terms with `m ≡ 0, 2 (mod 4)` and the imaginary
part those with `m ≡ 1, 3`: with `tblSum |X| q Q r n = ∑_{m<n, m ≡ r} M_m`,
`taylorExpI q x n = (tblCre + i tblCim) / 2^q`, `tblCre = S₀ − S₂`,
`tblCim = sgn(X) (S₁ − S₃)` (`tbl_taylorExpI`).

## Roundings

* `tbl_rho0_div`: `rho0 (a / b) = a.tdiv b` for `b > 0`.
* `tbl_roundC`: `roundC k` of `(a + i b) / 2^(k+d+1)` has numerators `⌊(a + 2^d) / 2^(d+1)⌋`
  and `⌊(b + 2^d) / 2^(d+1)⌋` at `k` bits.
* `tbl_diskPhase`: `diskPhase p` of `(a + i b) / 2^q` has numerators
  `((2^(p+2) − 1) a).tdiv 2^(q+2)` and `((2^(p+2) − 1) b).tdiv 2^(q+2)` at `p` bits.

## Table entries

* `tbl_axisPhase`: `axisPhase p g N s j = (tblAxRe + i tblAxIm) / 2^(p+g)`, from the angle
  numerator `X = −angleNum p g N s j` at `Q = 5 (p + g + 4)` bits, `q = p + g + 2 + gT` bits and
  `n = p + g + 14` terms, `gT = taylorGuard p g`.
* `tbl_twistPlus`, `tbl_twistMinus`: `twistPlus p r k = (tblTwRe + i tblTwIm) / 2^p` and its
  conjugate, from `X = twistAngleNum p r k ≥ 0` (`tbl_twistAngleNum_nonneg`) at
  `Q = 5 (p + 4)`, `q = p + 2 + taylorGuard p 0`, `n = p + 14`.

## Sizes

* `tbl_mag_le`: `M_m ≤ 2^q x^m / m!` for `x = |X| / 2^Q`; `tbl_mag_lt`, `tbl_sum_le`: for
  `|X| ≤ 4 · 2^Q`, `M_m < 2^(q+6)` and `S_r(n) ≤ n 2^(q+6)` (`e^4 < 64`).
* `tbl_angle_le`, `tbl_twistAngleNum_le`: both angle numerators are at most `4 · 2^Q` in
  magnitude.
* `tbl_wmag_eq`: the magnitudes `WeightNat.mag Y q` of the weight tables are `tblMag Y q q`;
  `tbl_wmag_lt`, `tbl_evenSum_le`, `tbl_oddSum_le`, `tbl_allSum_le`: for `Y ≤ p 2^q`, `p ≥ 1`,
  each magnitude is below `2^(q+2p)` (`e^p < 4^p`) and each `N`-term sum at most `N 2^(q+2p)`.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN Complex
open IntegerMultBounds.MathlibTM2.Mult.ComplexConv IntegerMultBounds.MathlibTM2.Mult.Chirp IntegerMultBounds.MathlibTM2.Mult.Pipeline

namespace IntegerMultBounds.MathlibTM2.Fast.TableNum

/-! ### Definitions -/

/-- Taylor magnitudes: `M_0 = 2^q`, `M_{m+1} = ⌊M_m Y / (2^Q (m+1))⌋`. -/
def tblMag (Y q Q : ℕ) : ℕ → ℕ
  | 0 => 2 ^ q
  | m + 1 => tblMag Y q Q m * Y / (2 ^ Q * (m + 1))

/-- `∑_{m < n, m % 4 = r} M_m`. -/
def tblSum (Y q Q r : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => tblSum Y q Q r m + if m % 4 = r then tblMag Y q Q m else 0

/-- A sign as an integer: `-1` for `true`, `1` for `false`. -/
def tblSgn (neg : Bool) : ℤ := if neg then -1 else 1

/-- The real numerator of the Taylor sum: `S₀ − S₂`. -/
def tblCre (Y q Q n : ℕ) : ℤ := (tblSum Y q Q 0 n : ℤ) - tblSum Y q Q 2 n

/-- The imaginary numerator of the Taylor sum: `sgn (S₁ − S₃)`. -/
def tblCim (neg : Bool) (Y q Q n : ℕ) : ℤ := tblSgn neg * ((tblSum Y q Q 1 n : ℤ) - tblSum Y q Q 3 n)

/-! ### Truncation and signs -/

/-- Rounding toward zero of an integer over a positive natural is the truncated division. -/
theorem tbl_rho0_div (a : ℤ) (b : ℕ) (hb : 0 < b) : rho0 ((a : ℝ) / (b : ℝ)) = a.tdiv b := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  unfold rho0
  split_ifs with h
  · have hn : 0 ≤ a := by
      by_contra hc
      push Not at hc
      have : (a : ℝ) / b < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hc) hbr
      linarith
    rw [Int.floor_div_natCast, Int.floor_intCast, Int.tdiv_eq_ediv_of_nonneg hn]
  · have hn : a < 0 := by
      by_contra hc
      push Not at hc
      exact h (div_nonneg (by exact_mod_cast hc) hbr.le)
    rw [← neg_neg ((a : ℝ) / b), Int.ceil_neg, ← neg_div, ← Int.cast_neg, Int.floor_div_natCast,
      Int.floor_intCast, ← Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -a), Int.neg_tdiv, neg_neg]

/-- `tbl_rho0_div` for a power of two. -/
theorem tbl_rho0_div_pow (a : ℤ) (k : ℕ) : rho0 ((a : ℝ) / 2 ^ k) = a.tdiv (2 ^ k) := by
  have h := tbl_rho0_div a (2 ^ k) (by positivity)
  push_cast at h
  exact h

/-- Powers of a sign are signs. -/
theorem tbl_sgn_pow (neg : Bool) (k : ℕ) : tblSgn neg ^ k = 1 ∨ tblSgn neg ^ k = -1 := by
  cases neg
  · simp [tblSgn]
  · simp only [tblSgn, ite_true]
    rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [h]

/-- Truncated division commutes with a unit factor. -/
theorem tbl_tdiv_unit {u : ℤ} (hu : u = 1 ∨ u = -1) (a b : ℤ) : (u * a).tdiv b = u * a.tdiv b := by
  rcases hu with rfl | rfl <;> simp [Int.neg_tdiv]

/-- An integer is its sign times its magnitude. -/
theorem tbl_sgn_natAbs (X : ℤ) : X = tblSgn (decide (X < 0)) * (X.natAbs : ℤ) := by
  rw [Int.natCast_natAbs]
  by_cases h : X < 0
  · simp [tblSgn, h, abs_of_neg h]
  · simp [tblSgn, h, abs_of_nonneg (not_lt.mp h)]

/-! ### Taylor sums -/

/-- The fixed-point Taylor terms of `e^{ix}`, `x = X / 2^Q`: `u_m = sgn(X)^m M_m / 2^q`. -/
theorem tbl_taylorTerm (X : ℤ) (q Q m : ℕ) :
    taylorTerm q ((X : ℝ) / 2 ^ Q) m =
      ((tblSgn (decide (X < 0)) ^ m * (tblMag X.natAbs q Q m : ℤ) : ℤ) : ℝ) / 2 ^ q := by
  induction m with
  | zero => simp [taylorTerm, tblMag]
  | succ m ih =>
    rw [taylorTerm, ih]
    set σ := tblSgn (decide (X < 0))
    set M := tblMag X.natAbs q Q m
    have hq : (0 : ℝ) < 2 ^ q := by positivity
    unfold truncR
    have e : (2 : ℝ) ^ q * (((σ ^ m * (M : ℤ) : ℤ) : ℝ) / 2 ^ q * ((X : ℝ) / 2 ^ Q) / ((m : ℝ) + 1)) =
        ((σ ^ m * (M : ℤ) * X : ℤ) : ℝ) / ((2 ^ Q * (m + 1) : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [e, tbl_rho0_div _ _ (by positivity)]
    have hX : σ ^ m * (M : ℤ) * X = σ ^ (m + 1) * ((M * X.natAbs : ℕ) : ℤ) := by
      conv_lhs => rw [tbl_sgn_natAbs X]
      push_cast; ring
    have ht : ((M * X.natAbs : ℕ) : ℤ).tdiv ((2 ^ Q * (m + 1) : ℕ) : ℤ) =
        (tblMag X.natAbs q Q (m + 1) : ℤ) := by
      rw [Int.tdiv_eq_ediv_of_nonneg (by positivity), ← Int.natCast_ediv]
      rfl
    rw [hX, tbl_tdiv_unit (tbl_sgn_pow _ _), ht]


/-- `i^n` depends on `n mod 4`. -/
theorem tbl_I_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  rw [show I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num]
  simp

/-- Powers of a sign depend on the exponent mod `4`. -/
theorem tbl_sgn_pow_mod (neg : Bool) (n : ℕ) : tblSgn neg ^ n = tblSgn neg ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  rw [show tblSgn neg ^ 4 = 1 by cases neg <;> simp [tblSgn]]
  simp

/-- Real and imaginary parts of `i^r u`, `r < 4`, for real `u`. -/
theorem tbl_I_pow_re_im (u : ℝ) (r : ℕ) (hr : r < 4) :
    (I ^ r * (u : ℂ)).re = (if r = 0 then u else if r = 2 then -u else 0) ∧
      (I ^ r * (u : ℂ)).im = (if r = 1 then u else if r = 3 then -u else 0) := by
  interval_cases r <;> simp [pow_succ, Complex.mul_re, Complex.mul_im]

/-- The Taylor sum `taylorExpI q (X / 2^Q) n` is `(tblCre + i tblCim) / 2^q`. -/
theorem tbl_taylorExpI (X : ℤ) (q Q n : ℕ) :
    taylorExpI q ((X : ℝ) / 2 ^ Q) n =
      ⟨(tblCre X.natAbs q Q n : ℝ) / 2 ^ q, (tblCim (decide (X < 0)) X.natAbs q Q n : ℝ) / 2 ^ q⟩ := by
  induction n with
  | zero => apply Complex.ext <;> simp [taylorExpI, tblCre, tblCim, tblSum]
  | succ n ih =>
    have hs : taylorExpI q ((X : ℝ) / 2 ^ Q) (n + 1) =
        taylorExpI q ((X : ℝ) / 2 ^ Q) n + I ^ n * (taylorTerm q ((X : ℝ) / 2 ^ Q) n : ℂ) := by
      unfold taylorExpI; rw [Finset.sum_range_succ]
    rw [hs, ih, tbl_taylorTerm, tbl_I_pow_mod, tbl_sgn_pow_mod]
    set σ := tblSgn (decide (X < 0)) with hσdef
    have hσ2 : σ ^ 2 = 1 := by simp only [σ]; cases decide (X < 0) <;> simp [tblSgn]
    have hσ3 : σ ^ 3 = σ := by rw [pow_succ, hσ2, one_mul]
    obtain ⟨hre, him⟩ := tbl_I_pow_re_im
      (((σ ^ (n % 4) * (tblMag X.natAbs q Q n : ℤ) : ℤ) : ℝ) / 2 ^ q) (n % 4) (Nat.mod_lt _ (by norm_num))
    apply Complex.ext
    · rw [Complex.add_re, hre]
      simp only [tblCre, tblSum]
      rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
        simp only [h, hσ2, hσ3, pow_zero, pow_one] <;> norm_num <;> ring
    · rw [Complex.add_im, him]
      simp only [tblCim, tblSum]
      rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
        simp only [h, hσ2, hσ3, pow_zero, pow_one] <;> norm_num <;> ring

/-! ### Roundings -/

/-- Rounding to nearest of `a / 2^(d+1)` is `⌊(a + 2^d) / 2^(d+1)⌋`. -/
theorem tbl_round_div (a : ℤ) (d : ℕ) : round ((a : ℝ) / 2 ^ (d + 1)) = (a + 2 ^ d) / 2 ^ (d + 1) := by
  rw [round_eq]
  have e : (a : ℝ) / 2 ^ (d + 1) + 1 / 2 = ((a + 2 ^ d : ℤ) : ℝ) / ((2 ^ (d + 1) : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e, Int.floor_div_natCast, Int.floor_intCast]
  push_cast; rfl

/-- `roundC k` of a grid value at `k + d + 1` bits, as numerators at `k` bits. -/
theorem tbl_roundC (k d : ℕ) (a b : ℤ) :
    roundC k ⟨(a : ℝ) / 2 ^ (k + d + 1), (b : ℝ) / 2 ^ (k + d + 1)⟩ =
      ⟨(((a + 2 ^ d) / 2 ^ (d + 1) : ℤ) : ℝ) / 2 ^ k, (((b + 2 ^ d) / 2 ^ (d + 1) : ℤ) : ℝ) / 2 ^ k⟩ := by
  have e : ∀ c : ℤ, (2 : ℝ) ^ k * ((c : ℝ) / 2 ^ (k + d + 1)) = (c : ℝ) / 2 ^ (d + 1) := by
    intro c; rw [show k + d + 1 = k + (d + 1) by ring, pow_add]; field_simp
  unfold roundC
  simp only [e, tbl_round_div]

/-- `diskPhase p` of a grid value at `q` bits, as numerators at `p` bits. -/
theorem tbl_diskPhase (p q : ℕ) (a b : ℤ) :
    diskPhase p ⟨(a : ℝ) / 2 ^ q, (b : ℝ) / 2 ^ q⟩ =
      ⟨((((2 ^ (p + 2) - 1) * a).tdiv (2 ^ (q + 2)) : ℤ) : ℝ) / 2 ^ p,
        ((((2 ^ (p + 2) - 1) * b).tdiv (2 ^ (q + 2)) : ℤ) : ℝ) / 2 ^ p⟩ := by
  have e : ∀ c : ℤ, (2 : ℝ) ^ p * ((1 - 1 / 2 ^ (p + 2)) * ((c : ℝ) / 2 ^ q)) =
      (((2 ^ (p + 2) - 1) * c : ℤ) : ℝ) / 2 ^ (q + 2) := by
    intro c; push_cast; rw [pow_add, pow_add]; field_simp
  unfold diskPhase rhoC
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [e, tbl_rho0_div_pow]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [e, tbl_rho0_div_pow]

/-! ### Chirp axis entries -/

/-- The real numerator of `axisPhase p g N s j` at `p + g` bits. -/
def tblAxRe (p g N s : ℕ) (j : ZMod N) : ℤ :=
  (tblCre (-angleNum p g N s j).natAbs (p + g + 2 + taylorGuard p g) (5 * anglePrec p g)
      (taylorTerms p g) + 2 ^ (1 + taylorGuard p g)) / 2 ^ (2 + taylorGuard p g)

/-- The imaginary numerator of `axisPhase p g N s j` at `p + g` bits. -/
def tblAxIm (p g N s : ℕ) (j : ZMod N) : ℤ :=
  (tblCim (decide (-angleNum p g N s j < 0)) (-angleNum p g N s j).natAbs
      (p + g + 2 + taylorGuard p g) (5 * anglePrec p g) (taylorTerms p g) +
      2 ^ (1 + taylorGuard p g)) / 2 ^ (2 + taylorGuard p g)

/-- The axis angle on the `2^{-5P}` grid, `P = anglePrec p g`. -/
theorem tbl_axisAngle (p g N s : ℕ) (j : ZMod N) :
    axisAngle p g N s j = ((-angleNum p g N s j : ℤ) : ℝ) / 2 ^ (5 * anglePrec p g) := by
  unfold axisAngle; push_cast; ring

/-- The chirp axis entry as a dyadic number with numerators `tblAxRe`, `tblAxIm`. -/
theorem tbl_axisPhase (p g N s : ℕ) (j : ZMod N) :
    axisPhase p g N s j =
      ⟨(tblAxRe p g N s j : ℝ) / 2 ^ (p + g), (tblAxIm p g N s j : ℝ) / 2 ^ (p + g)⟩ := by
  unfold axisPhase axisTaylor
  rw [tbl_axisAngle, tbl_taylorExpI,
    show p + g + 2 + taylorGuard p g = (p + g) + (1 + taylorGuard p g) + 1 by ring, tbl_roundC,
    show 1 + taylorGuard p g + 1 = 2 + taylorGuard p g by ring,
    show p + g + (1 + taylorGuard p g) + 1 = p + g + 2 + taylorGuard p g by ring]
  rfl

/-! ### Twist entries -/

/-- The twist angle numerator is nonnegative (`piQ (p + 4) ≥ 0`). -/
theorem tbl_twistAngleNum_nonneg (p r k : ℕ) : 0 ≤ twistAngleNum p r k := by
  unfold twistAngleNum
  exact Int.ediv_nonneg (mul_nonneg (IntegerMultBounds.Resampling.WeightTable.piQ_nonneg (p + 4) (by omega))
    (Int.natCast_nonneg k)) (Int.natCast_nonneg r)

/-- The real numerator of `twistPlus p r k` at `p` bits. -/
def tblTwRe (p r k : ℕ) : ℤ :=
  ((2 ^ (p + 2) - 1) * tblCre (twistAngleNum p r k).natAbs (p + 2 + taylorGuard p 0) (5 * (p + 4))
      (taylorTerms p 0)).tdiv (2 ^ (p + 2 + taylorGuard p 0 + 2))

/-- The imaginary numerator of `twistPlus p r k` at `p` bits. -/
def tblTwIm (p r k : ℕ) : ℤ :=
  ((2 ^ (p + 2) - 1) * tblCim (decide (twistAngleNum p r k < 0)) (twistAngleNum p r k).natAbs
      (p + 2 + taylorGuard p 0) (5 * (p + 4)) (taylorTerms p 0)).tdiv
    (2 ^ (p + 2 + taylorGuard p 0 + 2))

/-- The twist entry `θ̃⁺_k` as a dyadic number with numerators `tblTwRe`, `tblTwIm`. -/
theorem tbl_twistPlus (p r : ℕ) (k : Fin r) :
    twistPlus p r k = ⟨(tblTwRe p r k : ℝ) / 2 ^ p, (tblTwIm p r k : ℝ) / 2 ^ p⟩ := by
  unfold twistPlus twistPhase twistAngle
  rw [tbl_taylorExpI, tbl_diskPhase]
  rfl

/-- The twist entry `θ̃⁻_k = conj θ̃⁺_k`. -/
theorem tbl_twistMinus (p r : ℕ) (k : Fin r) :
    twistMinus p r k = ⟨(tblTwRe p r k : ℝ) / 2 ^ p, ((-tblTwIm p r k : ℤ) : ℝ) / 2 ^ p⟩ := by
  unfold twistMinus
  rw [tbl_twistPlus]
  apply Complex.ext
  · simp
  · simp only [Complex.conj_im]; push_cast; ring

/-! ### Sizes -/

/-- `M_m ≤ 2^q x^m / m!` for `x = Y / 2^Q`. -/
theorem tbl_mag_le (Y q Q m : ℕ) :
    (tblMag Y q Q m : ℝ) ≤ 2 ^ q * ((Y : ℝ) / 2 ^ Q) ^ m / m.factorial := by
  induction m with
  | zero => simp [tblMag]
  | succ m ih =>
    have hQ : (0 : ℝ) < 2 ^ Q := by positivity
    have hm : (0 : ℝ) < m + 1 := by positivity
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    set x : ℝ := (Y : ℝ) / 2 ^ Q with hx
    calc (tblMag Y q Q (m + 1) : ℝ)
        ≤ ((tblMag Y q Q m * Y : ℕ) : ℝ) / ((2 ^ Q * (m + 1) : ℕ) : ℝ) := Nat.cast_div_le
      _ = (tblMag Y q Q m : ℝ) * x / (m + 1) := by rw [hx]; push_cast; field_simp
      _ ≤ 2 ^ q * x ^ m / m.factorial * x / (m + 1) := by gcongr
      _ = 2 ^ q * x ^ (m + 1) / (m + 1).factorial := by
          rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp

/-- `e^4 < 64`. -/
theorem tbl_exp_four_lt : Real.exp 4 < 64 := by
  have h := Real.exp_one_lt_d9
  have h0 := (Real.exp_pos 1).le
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 64 := by norm_num

/-- For `Y ≤ 4 · 2^Q`, every magnitude is below `2^(q+6)`. -/
theorem tbl_mag_lt (Y q Q m : ℕ) (hY : Y ≤ 4 * 2 ^ Q) : tblMag Y q Q m < 2 ^ (q + 6) := by
  have hQ : (0 : ℝ) < 2 ^ Q := by positivity
  have hx0 : (0 : ℝ) ≤ (Y : ℝ) / 2 ^ Q := by positivity
  have hx4 : (Y : ℝ) / 2 ^ Q ≤ 4 := by
    rw [div_le_iff₀ hQ]; exact_mod_cast hY
  have h1 := tbl_mag_le Y q Q m
  have h2 : ((Y : ℝ) / 2 ^ Q) ^ m / m.factorial ≤ Real.exp 4 :=
    (Real.pow_div_factorial_le_exp _ hx0 m).trans (Real.exp_le_exp.mpr hx4)
  have h3 : (tblMag Y q Q m : ℝ) < 2 ^ (q + 6) := by
    calc (tblMag Y q Q m : ℝ) ≤ 2 ^ q * (((Y : ℝ) / 2 ^ Q) ^ m / m.factorial) := by
          rw [← mul_div_assoc]; exact h1
      _ ≤ 2 ^ q * Real.exp 4 := by gcongr
      _ < 2 ^ q * 64 := by gcongr; exact tbl_exp_four_lt
      _ = 2 ^ (q + 6) := by rw [pow_add]; norm_num
  exact_mod_cast h3

/-- For `Y ≤ 4 · 2^Q`, every partial sum of `n` terms is at most `n 2^(q+6)`. -/
theorem tbl_sum_le (Y q Q r n : ℕ) (hY : Y ≤ 4 * 2 ^ Q) : tblSum Y q Q r n ≤ n * 2 ^ (q + 6) := by
  induction n with
  | zero => simp [tblSum]
  | succ n ih =>
    have h := tbl_mag_lt Y q Q n hY
    simp only [tblSum]
    split_ifs <;> nlinarith

open IntegerMultBounds.Resampling.WeightNat in
/-- The weight-table magnitudes are the Taylor magnitudes with `Q = q`. -/
theorem tbl_wmag_eq (Y q m : ℕ) : mag Y q m = tblMag Y q q m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [mag, tblMag, ih]

open IntegerMultBounds.Resampling.WeightNat in
/-- For `Y ≤ p 2^q` and `p ≥ 1`, every weight-table magnitude is below `2^(q+2p)`. -/
theorem tbl_wmag_lt (p Y q m : ℕ) (hp : 1 ≤ p) (hY : Y ≤ p * 2 ^ q) : mag Y q m < 2 ^ (q + 2 * p) := by
  rw [tbl_wmag_eq]
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have hx0 : (0 : ℝ) ≤ (Y : ℝ) / 2 ^ q := by positivity
  have hxp : (Y : ℝ) / 2 ^ q ≤ p := by
    rw [div_le_iff₀ hq]; exact_mod_cast hY
  have h1 := tbl_mag_le Y q q m
  have h2 : ((Y : ℝ) / 2 ^ q) ^ m / m.factorial ≤ Real.exp p :=
    (Real.pow_div_factorial_le_exp _ hx0 m).trans (Real.exp_le_exp.mpr hxp)
  have he : Real.exp p < 4 ^ p := by
    rw [← Real.exp_one_pow]
    have : Real.exp 1 < 4 := Real.exp_one_lt_three.trans (by norm_num)
    exact pow_lt_pow_left₀ this (Real.exp_pos 1).le (by omega)
  have h3 : (tblMag Y q q m : ℝ) < 2 ^ (q + 2 * p) := by
    calc (tblMag Y q q m : ℝ) ≤ 2 ^ q * (((Y : ℝ) / 2 ^ q) ^ m / m.factorial) := by
          rw [← mul_div_assoc]; exact h1
      _ ≤ 2 ^ q * Real.exp p := by gcongr
      _ < 2 ^ q * 4 ^ p := by gcongr
      _ = 2 ^ (q + 2 * p) := by
          rw [pow_add, pow_mul]; norm_num
  exact_mod_cast h3

open IntegerMultBounds.Resampling.WeightNat in
/-- The even partial sum of the weight routine: at most `N 2^(q+2p)`. -/
theorem tbl_evenSum_le (p Y q N : ℕ) (hp : 1 ≤ p) (hY : Y ≤ p * 2 ^ q) :
    evenSum Y q N ≤ N * 2 ^ (q + 2 * p) := by
  induction N with
  | zero => simp [evenSum]
  | succ N ih =>
    have h := tbl_wmag_lt p Y q N hp hY
    simp only [evenSum]
    split_ifs <;> nlinarith

open IntegerMultBounds.Resampling.WeightNat in
/-- The odd partial sum of the weight routine: at most `N 2^(q+2p)`. -/
theorem tbl_oddSum_le (p Y q N : ℕ) (hp : 1 ≤ p) (hY : Y ≤ p * 2 ^ q) :
    oddSum Y q N ≤ N * 2 ^ (q + 2 * p) := by
  induction N with
  | zero => simp [oddSum]
  | succ N ih =>
    have h := tbl_wmag_lt p Y q N hp hY
    simp only [oddSum]
    split_ifs <;> nlinarith

open IntegerMultBounds.Resampling.WeightNat in
/-- The full partial sum of the weight routine: at most `N 2^(q+2p)`. -/
theorem tbl_allSum_le (p Y q N : ℕ) (hp : 1 ≤ p) (hY : Y ≤ p * 2 ^ q) :
    allSum Y q N ≤ N * 2 ^ (q + 2 * p) := by
  induction N with
  | zero => simp [allSum]
  | succ N ih =>
    have h := tbl_wmag_lt p Y q N hp hY
    simp only [allSum]
    nlinarith

/-- The chirp angle numerator is at most `4 · 2^(5P)` in magnitude. -/
theorem tbl_angle_le (p g N s : ℕ) [NeZero N] (j : ZMod N) :
    (angleNum p g N s j).natAbs ≤ 4 * 2 ^ (5 * anglePrec p g) := by
  have h := abs_axisAngle_le p g N s j
  have hP : (0 : ℝ) < 2 ^ (5 * anglePrec p g) := by positivity
  unfold axisAngle at h
  rw [abs_neg, abs_div, abs_of_pos hP, div_le_iff₀ hP] at h
  have h2 : ((angleNum p g N s j).natAbs : ℝ) ≤ 4 * 2 ^ (5 * anglePrec p g) := by
    rw [Nat.cast_natAbs]; push_cast; exact h
  exact_mod_cast h2

/-- The twist angle numerator is at most `4 · 2^(5(p+4))` in magnitude for `k ≤ r`. -/
theorem tbl_twistAngleNum_le (p r k : ℕ) (hr : 0 < r) (hk : k ≤ r) :
    (twistAngleNum p r k).natAbs ≤ 4 * 2 ^ (5 * (p + 4)) := by
  have h := twistAngle_err p r k hr hk
  have hP : (0 : ℝ) < 2 ^ (5 * (p + 4)) := by positivity
  have h16 : (16 : ℝ) ≤ 2 ^ (p + 4) :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (p + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hd : |twistAngle p r k - Real.pi * k / r| ≤ 1 / 16 := by
    have := abs_nonneg (twistAngle p r k - Real.pi * k / r)
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hx0 : |Real.pi * k / r| ≤ Real.pi := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hrr]
    have : (k : ℝ) ≤ r := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  have hpi := Real.pi_lt_d2
  have ha : |twistAngle p r k| ≤ 4 := by
    have := abs_sub_abs_le_abs_sub (twistAngle p r k) (Real.pi * k / r)
    linarith
  unfold twistAngle at ha
  rw [abs_div, abs_of_pos hP, div_le_iff₀ hP] at ha
  have h2 : ((twistAngleNum p r k).natAbs : ℝ) ≤ 4 * 2 ^ (5 * (p + 4)) := by
    rw [Nat.cast_natAbs]; push_cast; exact ha
  exact_mod_cast h2

end IntegerMultBounds.MathlibTM2.Fast.TableNum
