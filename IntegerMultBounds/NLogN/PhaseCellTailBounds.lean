module
public import IntegerMultBounds.NLogN.ResamplingInverse
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
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


/-! A dimension-independent lattice tail for the actual normalized Gaussian
coefficients. The quadratic exponent lower bound keeps the full Gaussian
decay, rather than paying the relative axis gap in the tail. The two signed
tails retain every integer lattice contribution, including periodic aliases. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellTailBounds

open Real
noncomputable section

theorem exponent_lower (ρ b c : ℝ) (hρ : 1≤ρ) (hb : |b|≤1/2) (hc : |c|≤1/2)
    (δ : ℤ) (hδ : δ≠0) :
    (δ : ℝ)^2-|(δ : ℝ)|≤(ρ*δ+b)^2-c^2 := by
  have hm : (1 : ℝ)≤|(δ : ℝ)| := by exact_mod_cast Int.one_le_abs hδ
  have hρ0 : 0≤ρ := by linarith
  have hρm : |(δ : ℝ)|≤ρ*|(δ : ℝ)| := by
    nlinarith [mul_nonneg (show 0≤ρ-1 by linarith) (abs_nonneg (δ : ℝ))]
  have hlower : ρ*|(δ : ℝ)|-1/2≤|ρ*δ+b| := by
    have h := abs_sub_abs_le_abs_sub (ρ*(δ : ℝ)) (-b)
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_of_nonneg hρ0] at h
    linarith
  have hnonneg : 0≤ρ*|(δ : ℝ)|-1/2 := by linarith
  have hsq : (ρ*|(δ : ℝ)|-1/2)^2≤(ρ*δ+b)^2 := by
    rw [←sq_abs (ρ*δ+b)]
    gcongr
  have hc2 : c^2≤(1 : ℝ)/4 := by
    have h : |c|^2≤(1/2 : ℝ)^2 := by gcongr
    rw [sq_abs] at h
    nlinarith
  have hprod := mul_nonneg (show 0≤ρ*|(δ : ℝ)|-|(δ : ℝ)| by linarith)
    (show 0≤ρ*|(δ : ℝ)|+|(δ : ℝ)|-1 by linarith)
  rw [←sq_abs (δ : ℝ)]
  nlinarith

theorem normExp_le (s t : ℕ) (hs : 0<s) (hst : s≤t) (α : ℝ) (j δ : ℤ) :
    normExp s t α j δ≤-π*α^2*((δ : ℝ)^2-|(δ : ℝ)|) := by
  by_cases hδ : δ=0
  · subst δ
    simp [normExp]
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hstR : (s : ℝ)≤t := by exact_mod_cast hst
  have hρ : (1 : ℝ)≤(t : ℝ)/s := (le_div_iff₀ hsR).mpr (by simpa using hstR)
  have h := exponent_lower ((t : ℝ)/s) (beta s t j) (beta s t (j+δ)) hρ
    (abs_beta_le s t j) (abs_beta_le s t (j+δ)) δ hδ
  have hm := mul_le_mul_of_nonneg_left h (mul_nonneg Real.pi_pos.le (sq_nonneg α))
  have hdiv : (t : ℝ)*δ/s=((t : ℝ)/s)*(δ : ℝ) := by ring
  unfold normExp
  rw [hdiv]
  nlinarith

def tailIndex (negative : Bool) (w n : ℕ) : ℤ :=
  if negative then -((w+1+n : ℕ) : ℤ) else ((w+1+n : ℕ) : ℤ)

def tailRatio (α : ℝ) (w : ℕ) : ℝ := Real.exp (-2*π*α^2*(w+1))

theorem tail_term_le (s t : ℕ) (hs : 0<s) (hst : s≤t)
    (α : ℝ) (j : ℤ) (negative : Bool) (w n : ℕ) :
    Real.exp (normExp s t α j (tailIndex negative w n))≤
      Real.exp (-π*α^2*(w : ℝ)*(w+1))*tailRatio α w^n := by
  have h := normExp_le s t hs hst α j (tailIndex negative w n)
  have habs : |(tailIndex negative w n : ℝ)|=(w : ℝ)+1+n := by
    cases negative
    · change |(((w+1+n : ℕ) : ℤ) : ℝ)|=(w : ℝ)+1+n
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      ring
    · change |((-(↑(w+1+n : ℕ)) : ℤ) : ℝ)|=(w : ℝ)+1+n
      rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      ring
  have hsq : (tailIndex negative w n : ℝ)^2=((w : ℝ)+1+n)^2 := by
    rw [←sq_abs, habs]
  rw [hsq, habs] at h
  have hn : (n : ℝ)≤(n : ℝ)^2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
  have hpoly : (w : ℝ)*(w+1)+2*(w+1)*n≤((w : ℝ)+1+n)^2-((w : ℝ)+1+n) := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hpoly (mul_nonneg Real.pi_pos.le (sq_nonneg α))
  unfold tailRatio
  rw [←Real.exp_nat_mul, ←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem tailRatio_lt_one (α : ℝ) (hα : 0<α) (w : ℕ) : tailRatio α w<1 := by
  apply Real.exp_lt_one_iff.mpr
  have hsq : 0<α^2 := sq_pos_of_pos hα
  have hw : (0 : ℝ)<w+1 := by positivity
  have h := mul_pos (mul_pos Real.pi_pos hsq) hw
  nlinarith

/-- Each signed omitted lattice tail is bounded by an explicit geometric sum.
No volume, axis count or relative-gap loss occurs in this estimate. -/
theorem tail_le (s t : ℕ) (hs : 0<s) (hst : s≤t) (α : ℝ) (hα : 0<α)
    (j : ℤ) (negative : Bool) (w : ℕ) :
    (∑' n : ℕ, Real.exp (normExp s t α j (tailIndex negative w n)))≤
      Real.exp (-π*α^2*(w : ℝ)*(w+1))/(1-tailRatio α w) := by
  have hr0 : 0≤tailRatio α w := (Real.exp_pos _).le
  have hr1 := tailRatio_lt_one α hα w
  have hgeom : Summable (fun n : ℕ =>
      Real.exp (-π*α^2*(w : ℝ)*(w+1))*tailRatio α w^n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hterm := tail_term_le s t hs hst α j negative w
  have hsum := hgeom.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hterm
  calc _≤∑' n : ℕ, Real.exp (-π*α^2*(w : ℝ)*(w+1))*tailRatio α w^n :=
      hsum.tsum_le_tsum hterm hgeom
    _=Real.exp (-π*α^2*(w : ℝ)*(w+1))/(1-tailRatio α w) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end
end IntegerMultBounds.NLogN.PhaseCellTailBounds
