module
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat
public import IntegerMultBounds.MathlibTM2.Binary
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
public import IntegerMultBounds.MathlibTM2.Mult.CRT


/-!
# Arithmetic of the parameter machine

Facts used by the parameter programs (`Fast/ParamSub.lean`, `Fast/ParamProg.lean`), which compute
every size of `Mult/Sizes.lean` from the operand length `n ≥ 2`.

* **Capped squaring.** `pmSq c z = min (z²) c`; for `v ≤ c`, `k` capped squarings give
  `min (v^(2^k)) c` (`pmSq_iter`), so `(v^(2^k) ≤ x)` is decided by `k` squarings of numbers
  at most `(x + 1)²` (`pmSq_iter_lt_iff`), never forming `v^(2^k)`.
* **Loop exits** of the searches: `⌈log₂ x⌉` (`pm_pow_lt_of_lt_clog`), integer roots
  (`Sizes.le_iroot_iff`), `⌊√x⌋` (`Nat.le_sqrt`), the least `a` with `t ≤ a^4`.
* **Sizes** for every `n ≥ 2`, with `B = b n`: `1 ≤ log₂ T ≤ B + 2`, `1 ≤ ℓ ≤ log₂ T`,
  `S < 2^(3B + 6)` (`pm_S_lt`, for `Big n`, from `S < T`), `α^4 < 2^(3B + 8)`,
  `p α² < 2^(4B + 11)`. Every value a parameter program forms is below `2^(4B + 16)`.
* **The elementary moduli** `Moduli.modulus N x₀ a i` of the programs `pmModC`, `pmProdSC`,
  `pmEmitSC`: the bounds `pmModBound`, `pm_modBound_le`, `pm_modulus_le_bound`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli Finset

/-! ### Capped squaring -/

/-- One capped squaring `z ↦ min (z²) c`. -/
def pmSq (c z : ℕ) : ℕ := min (z * z) c

theorem pmSq_iter {c v : ℕ} (hv : v ≤ c) : ∀ k, (pmSq c)^[k] v = min (v ^ 2 ^ k) c
  | 0 => by simp [hv]
  | k + 1 => by
    rw [Function.iterate_succ_apply', pmSq_iter hv k]
    unfold pmSq
    have e : v ^ 2 ^ (k + 1) = v ^ 2 ^ k * v ^ 2 ^ k := by rw [pow_succ, pow_mul, sq]
    rw [e]
    rcases le_or_gt (v ^ 2 ^ k) c with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h.le, min_eq_right (Nat.le_mul_self c), min_eq_right]
      nlinarith

theorem pmSq_iter_le {c v : ℕ} (hv : v ≤ c) (k : ℕ) : (pmSq c)^[k] v ≤ c := by
  rw [pmSq_iter hv]; exact min_le_right _ _

theorem pmSq_iter_lt_iff {x v : ℕ} (hv : v ≤ x + 1) (k : ℕ) :
    (pmSq (x + 1))^[k] v < x + 1 ↔ v ^ 2 ^ k ≤ x := by
  rw [pmSq_iter hv]; omega

/-! ### Loop exits -/

theorem pm_pow_lt_of_lt_clog {x j : ℕ} (h : j < Nat.clog 2 x) : 2 ^ j < x := by
  by_contra hc
  have := (Nat.clog_le_iff_le_pow one_lt_two).2 (not_lt.1 hc)
  omega

theorem pm_pow_le_of_iroot {k x j : ℕ} (hk : k ≠ 0) (h : j < iroot k x) : (j + 1) ^ k ≤ x :=
  (le_iroot_iff hk).1 h

/-! ### The least fourth-power bound -/

/-- `a` is the least natural number with `t ≤ a^4`. -/
def PmQuart (t a : ℕ) : Prop := t ≤ a ^ 4 ∧ ∀ j < a, j ^ 4 < t

theorem pmQuart_alpha (n : ℕ) : PmQuart (alphaU n ^ 2) (alpha n) :=
  ⟨alpha_spec n, fun _ hj => alpha_min n hj⟩

/-! ### Sizes for every `n ≥ 2` -/

section Sizes

variable {n : ℕ}

theorem pm_two_pow_le {a c : ℕ} (h : a ≤ c) : 2 ^ a ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) h

theorem pm_logT_le (hn : 2 ≤ n) : logT n ≤ b n + 2 := by
  rw [logT_le_iff hn]
  have h1 := le_two_pow_b n
  have h2 := one_le_b hn
  rw [pow_add]
  nlinarith

theorem pm_one_le_logT (hn : 2 ≤ n) : 1 ≤ logT n := by
  by_contra h
  have h0 : logT n ≤ 0 := by omega
  rw [logT_le_iff hn] at h0
  have := b_lt_two_mul hn
  simp at h0
  omega

theorem pm_one_le_ℓ (hn : 2 ≤ n) : 1 ≤ ℓ n := by
  have hd := one_le_d hn
  have hL := pm_one_le_logT hn
  unfold ℓ
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

theorem pm_ℓ_le_logT (hn : 2 ≤ n) : ℓ n ≤ logT n := by
  have hd := one_le_d hn
  have hL := pm_one_le_logT hn
  unfold ℓ
  apply Nat.div_le_of_le_mul
  have : logT n + d n ≤ d n * logT n + 1 := by nlinarith
  omega

theorem pm_ℓ_le (hn : 2 ≤ n) : ℓ n ≤ b n + 2 := (pm_ℓ_le_logT hn).trans (pm_logT_le hn)

/-- `N x₀ ≤ R + 2N` for the start `x₀ = start d N R`. -/
theorem pm_N_start_le {d N R : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) : N * start d N R ≤ R + 2 * N := by
  have h := (start_bounds (R := R) hd hN).2
  have : 2 * d * (N * start d N R) ≤ 2 * d * (R + 2 * N) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- The bound on the intermediate values of one modulus. -/
def pmModBound (N x₀ i : ℕ) : ℕ := N * (2 * x₀ + 2 * i + 1) + 2

theorem pm_modBound_le {d N R i : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (hi : i < d) :
    pmModBound N (start d N R) i ≤ 2 * R + N * (2 * d + 5) + 2 := by
  have h := pm_N_start_le (R := R) hd hN
  unfold pmModBound
  have : N * i ≤ N * d := Nat.mul_le_mul_left _ hi.le
  nlinarith

theorem pm_modulus_le_bound (N x₀ a i : ℕ) : modulus N x₀ a i ≤ pmModBound N x₀ i := by
  unfold modulus modA modB pmModBound
  split_ifs with h
  · nlinarith
  · have : i - a ≤ i := Nat.sub_le _ _
    nlinarith

theorem pm_S_prod (n : ℕ) : S n = ∏ i ∈ range (d n), srcLen n i :=
  Fin.prod_univ_eq_prod_range (fun i => srcLen n i) (d n)

theorem pm_S_lt (hB : Big n) : S n < 2 ^ (3 * b n + 6) := by
  have h1 := hB.S_lt_T
  have h2 : T n ≤ 2 ^ (3 * b n + 6) := pm_two_pow_le (by have := pm_logT_le hB.1; omega)
  omega

theorem pm_alpha_four_lt (hn : 2 ≤ n) : alpha n ^ 4 < 2 ^ (3 * b n + 8) := by
  have h1 := alpha_pow_four_lt n
  have hu := alphaU_le_b n
  have hb : b n + 6 ≤ 2 ^ (b n + 3) := by
    have := Nat.lt_two_pow_self (n := b n)
    rw [pow_add]; omega
  have h2 : alphaU n ^ 2 ≤ (2 ^ (b n + 3)) ^ 2 := Nat.pow_le_pow_left (hu.trans hb) 2
  have e : 16 * (2 ^ (b n + 3)) ^ 2 = 2 ^ (2 * b n + 10) := by
    rw [← pow_mul, show 2 * b n + 10 = 4 + (b n + 3) * 2 by ring, pow_add]; norm_num
  have h3 : 2 ^ (2 * b n + 10) ≤ 2 ^ (3 * b n + 8) ∨ b n ≤ 1 := by
    rcases Nat.lt_or_ge (b n) 2 with hb2 | hb2
    · exact Or.inr (by omega)
    · exact Or.inl (Nat.pow_le_pow_right (by norm_num) (by omega))
  rcases h3 with h3 | h3
  · omega
  · -- `b ≤ 1`: `u ≤ 7`, `α⁴ < 16 · 49`
    have : alphaU n ^ 2 ≤ 7 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have := one_le_b hn
    have : 2 ^ 11 ≤ 2 ^ (3 * b n + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem pm_alpha_sq_le (n : ℕ) : alpha n ^ 2 ≤ alpha n ^ 4 := by
  rcases Nat.eq_zero_or_pos (alpha n) with h | h
  · simp [h]
  · exact Nat.pow_le_pow_right h (by norm_num)

theorem pm_p_alpha_sq_lt (hn : 2 ≤ n) : p n * alpha n ^ 2 < 2 ^ (4 * b n + 11) := by
  have h1 := pm_alpha_four_lt hn
  have h2 := pm_alpha_sq_le n
  have hb := Nat.lt_two_pow_self (n := b n)
  have h3 : p n * alpha n ^ 2 ≤ 6 * b n * alpha n ^ 4 := by
    unfold p; exact Nat.mul_le_mul_left _ h2
  have h4 : 6 * b n * alpha n ^ 4 < 6 * 2 ^ b n * 2 ^ (3 * b n + 8) := by
    have : 0 < alpha n ^ 4 := by have := two_le_alpha hn; positivity
    have : 6 * b n * alpha n ^ 4 < 6 * 2 ^ b n * alpha n ^ 4 := by
      apply Nat.mul_lt_mul_of_pos_right _ this; omega
    calc 6 * b n * alpha n ^ 4 < 6 * 2 ^ b n * alpha n ^ 4 := this
      _ ≤ 6 * 2 ^ b n * 2 ^ (3 * b n + 8) := Nat.mul_le_mul_left _ h1.le
  have e : 6 * 2 ^ b n * 2 ^ (3 * b n + 8) ≤ 2 ^ (4 * b n + 11) := by
    have : 2 ^ (4 * b n + 11) = 8 * (2 ^ b n * 2 ^ (3 * b n + 8)) := by
      rw [← pow_add, show 4 * b n + 11 = 3 + (b n + (3 * b n + 8)) by ring, pow_add]; norm_num
    have e' : 6 * 2 ^ b n * 2 ^ (3 * b n + 8) = 6 * (2 ^ b n * 2 ^ (3 * b n + 8)) := by ring
    omega
  omega

/-- `(⌊√x⌋ + 1)² ≤ 3 x + 1`. -/
theorem pm_sqrt_succ_sq_le (x : ℕ) : (Nat.sqrt x + 1) * (Nat.sqrt x + 1) ≤ 3 * x + 1 := by
  have h1 := Nat.sqrt_le' x
  have h2 := Nat.sqrt_le_self x
  nlinarith

end Sizes

end IntegerMultBounds.MathlibTM2.Fast.TableVM
