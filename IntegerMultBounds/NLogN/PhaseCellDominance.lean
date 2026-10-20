module
public import IntegerMultBounds.NLogN.PhaseCellRow
import IntegerMultBounds.NLogN.PhaseCellSelectedTail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords


/-! Sharper Gaussian row dominance: at most one nearest neighbour is large.
This avoids the factor of two in the older symmetric geometric estimate. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDominance

open Real
variable (s t : ℕ) [NeZero s] [NeZero t]

omit [NeZero t] in
/-- The two nearest neighbours cannot both attain the worst rounding offset. -/
theorem neighbor_pair (hst : s<t) {α : ℝ} (hα : 0<α) (j : ZMod s) :
    Real.exp (normExp s t α j.val 1)+Real.exp (normExp s t α j.val (-1))≤
      Real.exp (-π*α^2*((t : ℝ)/s-1)/2)+Real.exp (-3*π*α^2/4) := by
  have hs : (0 : ℝ)<s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hρ : (1 : ℝ)≤(t : ℝ)/s := (le_div_iff₀ hs).mpr (by simpa only [one_mul] using (show (s : ℝ)≤t by exact_mod_cast hst.le))
  have hweak (k : ℤ) (hk : k.natAbs=1) :
      Real.exp (normExp s t α j.val k)≤Real.exp (-π*α^2*((t : ℝ)/s-1)/2) := by
    have h := offDiag_term_le s t hst hα (fun _ => 1) (by simp) j k
      (by intro h; simp [h] at hk)
    simpa [hk] using h
  have hstrong (k : ℤ) (hk : 1≤((t : ℝ)*k/s+beta s t j.val)^2) :
      Real.exp (normExp s t α j.val k)≤Real.exp (-3*π*α^2/4) := by
    apply Real.exp_le_exp.mpr
    have h := IntegerMultBounds.NLogN.normExp_le s t α j.val k
    have hπ : 0≤π*α^2 := by positivity
    nlinarith [mul_nonneg hπ (sub_nonneg.mpr hk)]
  by_cases hb : 0≤beta s t j.val
  · have hx : 1≤(t : ℝ)*((1 : ℤ) : ℝ)/s+beta s t j.val := by
      simpa using le_trans hρ (le_add_of_nonneg_right hb)
    have hsq : 1≤((t : ℝ)*((1 : ℤ) : ℝ)/s+beta s t j.val)^2 := by nlinarith
    exact (add_le_add (hstrong 1 hsq) (hweak (-1) (by decide))).trans_eq (add_comm _ _)
  · have hx : (t : ℝ)*((-1 : ℤ) : ℝ)/s+beta s t j.val≤-1 := by
      simp only [Int.cast_neg, Int.cast_one, mul_neg_one, neg_div]
      linarith
    have hsq : 1≤((t : ℝ)*((-1 : ℤ) : ℝ)/s+beta s t j.val)^2 := by nlinarith
    exact add_le_add (hweak 1 (by decide)) (hstrong (-1) hsq)

/-- Exponential decay leaves a linear gap even when the axis gap is tiny. -/
theorem exp_gap (x : ℝ) (hx : 0≤x) : Real.exp (-x)≤1-min x 1/2 := by
  by_cases hsmall : x≤1
  · rw [min_eq_left hsmall]
    have he := Real.add_one_le_exp x
    have hden : 0<1+x := by linarith
    have hi : Real.exp (-x)≤1/(1+x) := by
      rw [Real.exp_neg, ←one_div]
      exact one_div_le_one_div_of_le hden (by linarith)
    apply hi.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · rw [min_eq_right (by linarith)]
    have h : Real.exp (-x)≤Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have hhalf : Real.exp (-1)≤1/2 := by
      rw [Real.exp_neg, ←one_div]
      exact one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
    linarith

/-- A near-identity row bound separating the two neighbours from all farther
lattice offsets; periodic aliases remain included. -/
theorem offDiag_row (hst : s<t) {α : ℝ} (hα : 0<α)
    (u : ℕ) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (v : ZMod s → ℂ) (hv : ∀ k, ‖v k‖≤1) (j : ZMod s) :
    ‖offDiag s t α v j‖≤Real.exp (-π*α^2*((t : ℝ)/s-1)/2)+
      Real.exp (-3*π*α^2/4)+4/(2 : ℝ)^(6*u) := by
  have hfinite : PhaseCellRow.exactWindow s t α 1 v j-v j =
      (Real.exp (normExp s t α j.val 1) : ℂ)*v (j+1)+
      (Real.exp (normExp s t α j.val (-1)) : ℂ)*v (j-1) := by
    have hz : normExp s t α j.val 0=0 := by simp [normExp]
    simp only [PhaseCellRow.exactWindow, PhaseCellRow.window, Finset.sum_range_one,
      Int.cast_zero, Int.cast_neg, add_zero, hz,
      Real.exp_zero, Complex.ofReal_one, one_mul, sub_eq_add_neg]
    ring
  have hmul (k : ℤ) : ‖(Real.exp (normExp s t α j.val k) : ℂ)*v (j+k)‖≤
      Real.exp (normExp s t α j.val k) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hv _)
  have hnear : ‖PhaseCellRow.exactWindow s t α 1 v j-v j‖≤
      Real.exp (-π*α^2*((t : ℝ)/s-1)/2)+Real.exp (-3*π*α^2/4) := by
    rw [hfinite]
    exact ((norm_add_le _ _).trans (add_le_add (by simpa using hmul 1)
      (by simpa [sub_eq_add_neg] using hmul (-1)))).trans (neighbor_pair s t hst hα j)
  have ht (b : Bool) : (∑' n : ℕ, Real.exp (normExp s t α j.val
      (PhaseCellTailBounds.tailIndex b 1 n)))≤2/(2 : ℝ)^(6*u) := by
    have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
    have h := PhaseCellTailBounds.signed_tail_dyadic s t hs hst.le α hα u hαu hu j.val b 1
    simpa only [show 3*u*1*(1+1)=6*u by omega] using h
  have htail := PhaseCellRow.exactWindow_error s t hst hα v hv j 1
  have hnorm : normN s t α v j-v j=offDiag s t α v j := by
    rw [normN_eq s t hst hα]
    simp
  rw [←hnorm]
  calc _≤‖normN s t α v j-PhaseCellRow.exactWindow s t α 1 v j‖+
      ‖PhaseCellRow.exactWindow s t α 1 v j-v j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤_ := by
      have hfar := htail.trans (add_le_add (ht false) (ht true))
      have htotal := add_le_add hfar hnear
      convert htotal using 1
      ring

end IntegerMultBounds.NLogN.PhaseCellDominance
