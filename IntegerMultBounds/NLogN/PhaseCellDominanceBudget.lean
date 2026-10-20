module

import IntegerMultBounds.NLogN.PhaseCellDominance
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! Selected logarithmic Gaussian width gives a polynomial inverse gap even
when alpha squared times the axis gap tends to zero. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDominance

open Real

/-- A dyadic bound on the small opposite neighbour and farther lattice tail. -/
theorem small_terms (u : ℕ) {α : ℝ} (hαu : α^2=(u : ℝ)) :
    Real.exp (-3*π*α^2/4)+4/(2 : ℝ)^(6*u)≤5/(2 : ℝ)^(2*u) := by
  have hpow : (2 : ℝ)^(2*u)≤Real.exp (2*u) := by
    calc _≤(Real.exp 1)^(2*u) := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
      _=Real.exp (2*u) := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  have he : Real.exp (-3*π*α^2/4)≤1/(2 : ℝ)^(2*u) := by
    calc _≤Real.exp (-(2*(u : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [hαu]
          nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) u]
      _≤1/(2 : ℝ)^(2*u) := by
          rw [Real.exp_neg, ←one_div]
          exact one_div_le_one_div_of_le (by positivity) hpow
  have ht : 4/(2 : ℝ)^(6*u)≤4/(2 : ℝ)^(2*u) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  calc _≤1/(2 : ℝ)^(2*u)+4/(2 : ℝ)^(2*u) := add_le_add he ht
    _=5/(2 : ℝ)^(2*u) := by ring

/-- The source's logarithmic width and axis gap give the exact row margin. -/
theorem selected_scalar_gap (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u)
    {α θ : ℝ} (hαu : α^2=(u : ℝ)) (hθ : 1/(4*(p : ℝ))≤θ) :
    Real.exp (-π*α^2*θ/2)+Real.exp (-3*π*α^2/4)+4/(2 : ℝ)^(6*u)≤
      1-1/(4*(p : ℝ)) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0 : ℝ)<p := by linarith
  have hu4 : 4≤u := by
    by_contra h
    have hpow : (2 : ℕ)^u≤2^3 := pow_le_pow_right₀ (by decide) (by omega)
    omega
  have huR : (4 : ℝ)≤u := by exact_mod_cast hu4
  have hx : 1/(p : ℝ)≤α^2*θ := by
    rw [hαu]
    have hm := mul_le_mul_of_nonneg_left hθ (show (0 : ℝ)≤u by positivity)
    rw [mul_one_div] at hm
    have hfour : (u : ℝ)/(4*p)≥1/p := by
      apply (div_le_div_iff₀ hp0 (by positivity)).mpr
      nlinarith
    linarith
  have hmin : 1/(p : ℝ)≤min (α^2*θ) 1 := le_min hx
    ((div_le_one hp0).mpr (by linarith))
  have hweak : Real.exp (-π*α^2*θ/2)≤1-min (α^2*θ) 1/2 := by
    calc _≤Real.exp (-(α^2*θ)) := by
          apply Real.exp_le_exp.mpr
          have hx0 : 0≤α^2*θ := (by positivity : (0 : ℝ)≤1/p).trans hx
          nlinarith [mul_nonneg (show 0≤π-2 by linarith [Real.pi_gt_three]) hx0]
      _≤_ := exp_gap _ ((by positivity : (0 : ℝ)≤1/p).trans hx)
  have hsmall := small_terms u hαu
  have hpowR : (8*(p : ℝ))^2≤(2 : ℝ)^(2*u) := by
    have hw : 8*(p : ℝ)≤(2 : ℝ)^u := by exact_mod_cast hwidth
    have hsq : (8*(p : ℝ))^2≤((2 : ℝ)^u)^2 := by gcongr
    simpa only [←pow_mul, Nat.mul_comm u 2] using hsq
  have herr : 5/(2 : ℝ)^(2*u)≤1/(16*(p : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have htotal := add_le_add hweak (hsmall.trans herr)
  have hid : 1/(16*(p : ℝ))=(1/(p : ℝ))/16 := by ring
  have hid4 : 1/(4*(p : ℝ))=(1/(p : ℝ))/4 := by ring
  rw [hid] at htotal
  rw [hid4]
  have hrecip : (0 : ℝ)≤1/p := by positivity
  linarith

end IntegerMultBounds.NLogN.PhaseCellDominance
