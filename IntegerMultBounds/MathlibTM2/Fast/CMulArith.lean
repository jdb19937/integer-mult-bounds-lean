module

import IntegerMultBounds.MathlibTM2.Layer.GaussLin
public import IntegerMultBounds.MathlibTM2.Host.Index
import IntegerMultBounds.NLogN.FixedOps
public import IntegerMultBounds.NLogN.Approx
public import IntegerMultBounds.MathlibTM2.Layer.Carry
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Arithmetic of the complex fixed-point product

A grid value `u = N / 2^p` (`N : GaussianInt`) is stored through its numerator `N`; `numer p u`
recovers the numerator (`numer_grid`), and `rhoC p u = numer p u / 2^p` for every `u`
(`rhoC_eq_numer`). The rounded product of two grid values is the grid value of the truncated
numerator product: `rhoC p ((N₁ / 2^p) (N₂ / 2^p)) = tdivN p (N₁ N₂) / 2^p` (`rhoC_mul_grid`), where
`tdivN p` divides both parts by `2^p` with truncation toward zero.

The machine computes `tdivN p (N₁ N₂)` in sign-magnitude form:

* `select_testBit`, `select_natAbs`: the top bit of the two's complement residue
  `(x : ZMod (2^K)).val` is the sign of `x`, and choosing between the residues of `x` and `-x` by
  that bit gives `|x|`, whenever `|x| < 2^(K-1)`;
* `bsgn_natAbs`, `bsgn_xor`, `bsgn_not`: signs as integers;
* `tdiv_eq_bsgn`: `x.tdiv 2^p = bsgn (x < 0) · (|x| / 2^p)`;
* `binSyms_add`, `drop_binSyms`: splitting a binary numeral;
* `carryRun_nat`: the signed-carry adder on bits of natural numbers computes an integer linear
  combination modulo `2^K`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN IntegerMultBounds.Machine

/-! ### Signs -/

/-- A sign as an integer: `-1` for `true` (negative), `1` for `false`. -/
def bsgn (s : Bool) : ℤ := if s then -1 else 1

@[simp] lemma bsgn_true : bsgn true = -1 := rfl
@[simp] lemma bsgn_false : bsgn false = 1 := rfl

lemma bsgn_xor (s t : Bool) : bsgn (s ^^ t) = bsgn s * bsgn t := by
  cases s <;> cases t <;> simp [bsgn]

lemma bsgn_not (s : Bool) : bsgn (!s) = -bsgn s := by
  cases s <;> simp [bsgn]

lemma bsgn_natAbs (x : ℤ) : bsgn (decide (x < 0)) * (x.natAbs : ℤ) = x := by
  by_cases h : x < 0
  · simp only [h, decide_true, bsgn_true]; omega
  · simp only [h, decide_false, bsgn_false]; omega

/-! ### Truncated division -/

/-- Division of both parts by `2^p`, truncating toward zero. -/
def tdivN (p : ℕ) (z : GaussianInt) : GaussianInt := ⟨z.re.tdiv (2 ^ p), z.im.tdiv (2 ^ p)⟩

@[simp] lemma tdivN_re (p : ℕ) (z : GaussianInt) : (tdivN p z).re = z.re.tdiv (2 ^ p) := rfl
@[simp] lemma tdivN_im (p : ℕ) (z : GaussianInt) : (tdivN p z).im = z.im.tdiv (2 ^ p) := rfl

/-- Truncated division in sign-magnitude form. -/
lemma tdiv_eq_bsgn (x : ℤ) (p : ℕ) :
    x.tdiv (2 ^ p) = bsgn (decide (x < 0)) * ((x.natAbs / 2 ^ p : ℕ) : ℤ) := by
  have hc : ((2 : ℕ) : ℤ) ^ p = ((2 ^ p : ℕ) : ℤ) := by push_cast; ring
  by_cases h : x < 0
  · have hx : x = -((x.natAbs : ℕ) : ℤ) := by omega
    simp only [h, decide_true, bsgn_true]
    conv_lhs => rw [hx]
    rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by positivity)]
    push_cast
    ring
  · have hx : x = ((x.natAbs : ℕ) : ℤ) := by omega
    simp only [h, decide_false, bsgn_false, one_mul]
    conv_lhs => rw [hx]
    rw [Int.tdiv_eq_ediv_of_nonneg (by positivity)]
    push_cast
    rfl

/-- Truncated division of an integer by `2^s` is the truncation toward zero of the real
quotient. -/
lemma tdiv_rho0 (x : ℤ) (s : ℕ) : x.tdiv (2 ^ s) = rho0 ((x : ℝ) / 2 ^ s) := by
  have h : ((x : ℝ) / 2 ^ s) = (((x : ℚ) / ((2 ^ s : ℕ) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  unfold rho0
  rw [h, Rat.floor_cast, Rat.ceil_cast]
  split_ifs with hx
  · have : 0 ≤ x := by
      rw [← h] at hx
      have := (div_nonneg_iff.1 hx)
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact_mod_cast h1
      · linarith
    rw [Int.tdiv_eq_ediv_of_nonneg this, Rat.floor_intCast_div_natCast]
    push_cast; rfl
  · have : x < 0 := by
      rw [← h] at hx
      by_contra hc
      exact hx (div_nonneg (by exact_mod_cast not_lt.1 hc) hpos.le)
    rw [Rat.ceil_intCast_div_natCast, ← neg_neg x, Int.neg_tdiv, neg_neg,
      Int.tdiv_eq_ediv_of_nonneg (by omega)]
    push_cast; rfl

/-! ### Numerators of grid values -/

/-- The numerator of a grid value at `p` fractional bits: `2^p u` with both parts truncated
toward zero. For `u = N / 2^p` it is `N` (`numer_grid`). -/
noncomputable def numer (p : ℕ) (u : ℂ) : GaussianInt := ⟨rho0 (2 ^ p * u.re), rho0 (2 ^ p * u.im)⟩

lemma toComplex_div_re (N : GaussianInt) (c : ℝ) :
    (GaussianInt.toComplex N / (c : ℂ)).re = (N.re : ℝ) / c := by
  rw [Complex.div_ofReal_re, ← GaussianInt.intCast_re]

lemma toComplex_div_im (N : GaussianInt) (c : ℝ) :
    (GaussianInt.toComplex N / (c : ℂ)).im = (N.im : ℝ) / c := by
  rw [Complex.div_ofReal_im, ← GaussianInt.intCast_im]

lemma two_pow_complex (p : ℕ) : (2 : ℂ) ^ p = ((2 ^ p : ℝ) : ℂ) := by push_cast; rfl

/-- The rounding `rhoC p` is the grid value of `numer p`. -/
theorem rhoC_eq_numer (p : ℕ) (u : ℂ) : rhoC p u = GaussianInt.toComplex (numer p u) / 2 ^ p := by
  rw [two_pow_complex]
  apply Complex.ext
  · rw [rhoC_re, toComplex_div_re]; rfl
  · rw [rhoC_im, toComplex_div_im]; rfl

/-- The numerator of the grid value `N / 2^p` is `N`. -/
theorem numer_grid (p : ℕ) (N : GaussianInt) : numer p (GaussianInt.toComplex N / 2 ^ p) = N := by
  have hpos : (2 : ℝ) ^ p ≠ 0 := by positivity
  rw [two_pow_complex]
  simp only [numer, toComplex_div_re, toComplex_div_im]
  rw [mul_div_cancel₀ _ hpos, mul_div_cancel₀ _ hpos, rho0_intCast, rho0_intCast]

/-- The rounded product of two grid values is the grid value of the truncated numerator
product. -/
theorem rhoC_mul_grid (p : ℕ) (N₁ N₂ : GaussianInt) :
    rhoC p (GaussianInt.toComplex N₁ / 2 ^ p * (GaussianInt.toComplex N₂ / 2 ^ p)) =
      GaussianInt.toComplex (tdivN p (N₁ * N₂)) / 2 ^ p := by
  have hpos : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hprod : GaussianInt.toComplex N₁ / 2 ^ p * (GaussianInt.toComplex N₂ / 2 ^ p) =
      GaussianInt.toComplex (N₁ * N₂) / ((2 ^ p * 2 ^ p : ℝ) : ℂ) := by
    rw [map_mul]; push_cast; ring
  rw [hprod, two_pow_complex]
  apply Complex.ext
  · rw [rhoC_re, toComplex_div_re, toComplex_div_re, tdivN_re, tdiv_rho0]
    congr 2
    field_simp
  · rw [rhoC_im, toComplex_div_im, toComplex_div_im, tdivN_im, tdiv_rho0]
    congr 2
    field_simp

/-! ### Two's complement and sign-magnitude -/

lemma val_intCast_eq (K : ℕ) (x : ℤ) : (((x : ZMod (2 ^ K)).val : ℕ) : ℤ) = x % 2 ^ K := by
  rw [ZMod.val_intCast]; push_cast; rfl

/-- The top bit of the residue of `x` modulo `2^K` is the sign of `x`. -/
lemma select_testBit {K : ℕ} (hK : 1 ≤ K) {x : ℤ} (hx : |x| < 2 ^ (K - 1)) :
    (x : ZMod (2 ^ K)).val.testBit (K - 1) = decide (x < 0) := by
  have hK2 : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hK2n : (2 : ℕ) ^ K = 2 * 2 ^ (K - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hv := val_intCast_eq K x
  rw [abs_lt] at hx
  set u := (x : ZMod (2 ^ K)).val with hu
  have hpos : (0 : ℤ) < 2 ^ (K - 1) := by positivity
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x < 0
  · have hm : x % 2 ^ K = x + 2 ^ K := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hm] at hv
    have h1 : 2 ^ (K - 1) ≤ u := by
      have : ((2 ^ (K - 1) : ℕ) : ℤ) ≤ (u : ℤ) := by push_cast; omega
      exact_mod_cast this
    have h2 : u < 2 * 2 ^ (K - 1) := by
      have : (u : ℤ) < ((2 * 2 ^ (K - 1) : ℕ) : ℤ) := by push_cast; omega
      exact_mod_cast this
    have : u / 2 ^ (K - 1) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [this, h]
  · have hm : x % 2 ^ K = x := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm] at hv
    have h2 : u < 2 ^ (K - 1) := by
      have : (u : ℤ) < ((2 ^ (K - 1) : ℕ) : ℤ) := by push_cast; omega
      exact_mod_cast this
    have : u / 2 ^ (K - 1) = 0 := Nat.div_eq_of_lt h2
    simp [this, h]

/-- Choosing between the residues of `x` and `-x` by the sign gives `|x|`. -/
lemma select_natAbs {K : ℕ} {x : ℤ} (hx : |x| < 2 ^ (K - 1)) :
    (if decide (x < 0) then ((-x : ℤ) : ZMod (2 ^ K)).val else (x : ZMod (2 ^ K)).val) =
      x.natAbs := by
  have hle : (2 : ℤ) ^ (K - 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [abs_lt] at hx
  by_cases h : x < 0
  · simp only [h, decide_true, ite_true]
    have hv := val_intCast_eq K (-x)
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hv
    omega
  · simp only [h, decide_false]
    have hv := val_intCast_eq K x
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hv
    simp only [Bool.false_eq_true, ite_false]
    omega

/-! ### Binary numerals -/

/-- A numeral of `a + b` bits is its low `a` bits followed by `b` bits of the quotient. -/
lemma binSyms_add {A : ℕ} (a b x : ℕ) :
    (binSyms (a + b) x : List (Fin (A + 4))) = binSyms a x ++ binSyms b (x / 2 ^ a) := by
  simp only [binSyms]
  rw [List.ofFn_add]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [Nat.testBit_div_two_pow, Nat.add_comm]

/-- Dropping the low `p` bits of a numeral. -/
lemma drop_binSyms {A : ℕ} {N p : ℕ} (hp : p ≤ N) (x : ℕ) :
    (binSyms N x : List (Fin (A + 4))).drop p = binSyms (N - p) (x / 2 ^ p) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [binSyms_add, List.drop_left' (by simp), Nat.add_sub_cancel_left]

lemma getD_ofFn_bool {K : ℕ} (f : Fin K → Bool) (t : Fin K) : (List.ofFn f).getD t false = f t := by
  simp [List.getD_eq_getElem?_getD]

/-- The signed-carry adder on the bits of natural numbers: the integer combination modulo
`2^K`. -/
lemma carryRun_nat (K k : ℕ) (a : Fin k → ℤ) (X : Fin k → ℕ) :
    (carryRun 0 (List.ofFn fun t : Fin K => ∑ i, a i * (((X i).testBit t).toNat : ℤ))).1 =
      List.ofFn fun t : Fin K => ((∑ i, a i * (X i : ℤ) : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  have h := carryRun_bits K k a (fun i => ((X i : ℕ) : ZMod (2 ^ K)))
  have e1 : ∀ i (t : Fin K), ((X i : ZMod (2 ^ K))).val.testBit t = (X i).testBit t := by
    intro i t
    rw [ZMod.val_natCast, Nat.testBit_mod_two_pow]
    simp [t.2]
  simp only [e1] at h
  rw [h]
  congr 1
  funext t
  congr 3
  push_cast
  rfl

end IntegerMultBounds.MathlibTM2.Fast
