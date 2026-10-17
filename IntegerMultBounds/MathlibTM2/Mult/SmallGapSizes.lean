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

private theorem four_sq_le (c : ℕ) (hc : 10 ≤ c) : 4*c^2 ≤ 3*2^(c-1) := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
    have h2 : 2^(c+1-1)=2*2^(c-1) := by
      rw [show c+1-1=(c-1)+1 by omega, pow_succ]; ring
    rw [h2]
    nlinarith

variable {n : ℕ}

/-- `u² ≤ 36 b` at the large sizes. -/
theorem Big.uSG_sq_le (h : Big n) : uSG n^2≤36*b n := by
  have hb : 16≤b n := h.sixteen_le_b
  have hp : 8*p n=48*b n := by unfold p; ring
  have hlt : 2^(uSG n-1)<48*b n := by
    have := Nat.pow_pred_clog_lt_self one_lt_two (show 1<8*p n by omega)
    simpa [uSG, hp, Nat.pred_eq_sub_one] using this
  have hc : 10≤uSG n := by
    by_contra hlt10
    have hle : 8*p n≤2^9 := (two_pow_uSG n).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have := h.pow_le_b (k := 2) (by norm_num)
    have := h.2
    nlinarith
  have := four_sq_le _ hc
  nlinarith

/-- `u d ≤ p`. -/
theorem Big.uSG_mul_d_le (h : Big n) : uSG n*d n≤p n := by
  have hu := h.uSG_sq_le
  have hd := h.pow_le_b (k := 2) (by norm_num)
  have hsq : (uSG n*d n)^2≤(p n)^2 := by
    unfold p
    rw [mul_pow]
    nlinarith
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq

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
