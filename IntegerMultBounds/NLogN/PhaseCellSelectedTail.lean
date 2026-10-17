module

public import IntegerMultBounds.NLogN.PhaseCellTailBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds

/-! Explicit dyadic truncation error for the selected phase-cell band.
The width condition `16*p ≤ u*w²` is kept visible until the executable band
parameter is supplied. Every omitted signed lattice contribution is included;
no assumption of a single periodic alias is used. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellTailBounds

open Real
noncomputable section

theorem tailRatio_le_half (α : ℝ) (hα : 1≤α^2) (w : ℕ) : tailRatio α w≤1/2 := by
  have hw : (1 : ℝ)≤w+1 := le_add_of_nonneg_left (Nat.cast_nonneg w)
  have hprod : 1≤π*α^2*(w+1) := by
    calc 1≤π := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
      _≤π*α^2 := le_mul_of_one_le_right Real.pi_pos.le hα
      _≤π*α^2*(w+1) := le_mul_of_one_le_right (by positivity) hw
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) Real.exp_one_gt_two.le
  calc tailRatio α w≤Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        nlinarith
    _≤1/2 := by simpa [Real.exp_neg, one_div] using h

/-- Each signed tail has a purely dyadic bound once the squared width is a
positive integer. -/
theorem signed_tail_dyadic (s t : ℕ) (hs : 0<s) (hst : s≤t)
    (α : ℝ) (hα : 0<α) (u : ℕ) (hu : α^2=(u : ℝ)) (hu1 : 1≤u)
    (j : ℤ) (negative : Bool) (w : ℕ) :
    (∑' n : ℕ, Real.exp (normExp s t α j (tailIndex negative w n)))≤
      2/(2 : ℝ)^(3*u*w*(w+1)) := by
  have hα1 : (1 : ℝ)≤α^2 := by rw [hu]; exact_mod_cast hu1
  have hr := tailRatio_le_half α hα1 w
  have hden : 0<1-tailRatio α w := by linarith
  have hpref : Real.exp (-π*α^2*(w : ℝ)*(w+1))≤
      1/(2 : ℝ)^(3*u*w*(w+1)) := by
    have hpow : (2 : ℝ)^(3*u*w*(w+1))≤Real.exp (3*u*w*(w+1)) := by
      calc (2 : ℝ)^(3*u*w*(w+1))≤Real.exp 1^(3*u*w*(w+1)) :=
          pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
        _=Real.exp (3*u*w*(w+1)) := by
          rw [←Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    calc Real.exp (-π*α^2*(w : ℝ)*(w+1))≤Real.exp (-((3*u*w*(w+1) : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          rw [hu]
          push_cast
          have h := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
            (show 0≤(u : ℝ)*w*(w+1) by positivity)
          nlinarith
      _≤1/(2 : ℝ)^(3*u*w*(w+1)) := by
          have h := one_div_le_one_div_of_le (by positivity) hpow
          simpa [Real.exp_neg, one_div] using h
  calc _≤Real.exp (-π*α^2*(w : ℝ)*(w+1))/(1-tailRatio α w) :=
      tail_le s t hs hst α hα j negative w
    _≤2*Real.exp (-π*α^2*(w : ℝ)*(w+1)) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (Real.exp_pos (-π*α^2*(w : ℝ)*(w+1))).le
        (show 0≤1/2-tailRatio α w by linarith)]
    _≤2*(1/(2 : ℝ)^(3*u*w*(w+1))) :=
      mul_le_mul_of_nonneg_left hpref (by norm_num)
    _=2/(2 : ℝ)^(3*u*w*(w+1)) := by ring

/-- Both signed tails fit the selected `2^(-46p)` error allowance. This is an
actual lattice sum estimate, independent of the line length and dimension. -/
theorem selected_tail (s t p u w : ℕ) (hs : 0<s) (hst : s≤t) (hp : 0<p)
    (hu1 : 1≤u) (hband : 16*p≤u*w^2) (α : ℝ) (hα : 0<α)
    (hu : α^2=(u : ℝ)) (j : ℤ) :
    (∑' n : ℕ, Real.exp (normExp s t α j (tailIndex false w n)))+
      (∑' n : ℕ, Real.exp (normExp s t α j (tailIndex true w n)))≤
        1/(2 : ℝ)^(46*p) := by
  have hpos := signed_tail_dyadic s t hs hst α hα u hu hu1 j false w
  have hneg := signed_tail_dyadic s t hs hst α hα u hu hu1 j true w
  have hmul : 48*p≤3*u*w*(w+1) := by nlinarith [hband]
  have hmargin : 46*p+2≤3*u*w*(w+1) := by omega
  have hpow : (2 : ℝ)^(46*p+2)≤(2 : ℝ)^(3*u*w*(w+1)) :=
    pow_le_pow_right₀ (by norm_num) hmargin
  have hfinal : 4/(2 : ℝ)^(3*u*w*(w+1))≤1/(2 : ℝ)^(46*p) := by
    calc _≤4/(2 : ℝ)^(46*p+2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
      _=1/(2 : ℝ)^(46*p) := by rw [pow_add]; norm_num; ring
  calc _≤2/(2 : ℝ)^(3*u*w*(w+1))+2/(2 : ℝ)^(3*u*w*(w+1)) := add_le_add hpos hneg
    _=4/(2 : ℝ)^(3*u*w*(w+1)) := by ring
    _≤1/(2 : ℝ)^(46*p) := hfinal

end
end IntegerMultBounds.NLogN.PhaseCellTailBounds
