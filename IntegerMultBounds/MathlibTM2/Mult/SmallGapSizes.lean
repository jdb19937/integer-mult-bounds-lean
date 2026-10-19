module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Small-gap parameters at the existing sizes. With `u = ⌈log₂(8p)⌉` and the
dimension `d` as cell parameter, the existing source/axis lengths satisfy every
hypothesis of the small-gap inverse theory: `8p ≤ 2^u`, `1/(4p) ≤ θ_i`,
`1/4 ≤ d θ_i` and `u d ≤ p`. This supports replacing the Neumann inverse by a
banded factorization with `α² = u` without changing the axis sizes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- The small-gap Gaussian parameter `α² = u`. -/
def uSG (n : ℕ) : ℕ := Nat.clog 2 (8*p n)

theorem two_pow_uSG (n : ℕ) : 8*p n ≤ 2^uSG n := Nat.le_pow_clog one_lt_two _

variable {n : ℕ}

/-- `u d ≤ p`: `u ≤ ⌈log₂ p⌉ + 3` and the Gaussian width room `64 d (⌈log₂ p⌉ + 3) ≤ b`. -/
theorem Big.uSG_mul_d_le (h : Big n) : uSG n*d n≤p n := by
  have hroom := h.bigFacts.2.1
  have hu : uSG n≤Nat.clog 2 (p n)+3 := by
    unfold uSG
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have := Nat.le_pow_clog one_lt_two (p n)
    have h8 : (2:ℕ)^3=8 := by norm_num
    rw [h8]
    omega
  have h1 : uSG n*d n≤(Nat.clog 2 (p n)+3)*d n := Nat.mul_le_mul_right _ hu
  have e : (Nat.clog 2 (p n)+3)*d n*64=64*d n*(Nat.clog 2 (p n)+3) := by ring
  have hp : p n=6*b n := rfl
  omega

/-- All small-gap hypotheses on every axis. -/
theorem Big.smallgap (h : Big n) (i : Fin (d n)) :
    8*p n≤2^uSG n ∧ 1/(4*(p n : ℝ))≤(t n i : ℝ)/s n i-1 ∧
      (1 : ℝ)/4≤(d n : ℝ)*((t n i : ℝ)/s n i-1) ∧ uSG n*d n≤p n := by
  have hθ := h.eta_lt_theta i
  have hd : (0 : ℝ)<d n := by exact_mod_cast h.one_le_d
  have hdp : (d n : ℝ)≤p n := by
    have : d n≤p n := (d_le_b n).trans (by unfold p; omega)
    exact_mod_cast this
  unfold eta at hθ
  refine ⟨two_pow_uSG n, ?_, ?_, h.uSG_mul_d_le⟩
  · refine le_trans ?_ hθ.le
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · have := mul_lt_mul_of_pos_left hθ hd
    have e : (d n : ℝ)*(1/(4*d n))=1/4 := by field_simp
    linarith

end IntegerMultBounds.MathlibTM2.Mult.Sizes
