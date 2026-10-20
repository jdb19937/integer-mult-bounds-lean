module

import IntegerMultBounds.NLogN.SchurBlockError
import IntegerMultBounds.NLogN.PhaseCellBoundarySolve
import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.PhaseCellMatrix
public import IntegerMultBounds.NLogN.SchurBlockSolve
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! Error composition of the rounded four-step solve on the actual rounded
periodic Gaussian matrix. Off-diagonal row mass is at most one, so stage
errors `e₁…e₅` give boundary error `e₃+8p(e₁+e₂)` and interior error
`e₅+8p(e₄+e₃+8p(e₁+e₂))`, independent of the number of cells. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance ContinuousLinearMap
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- Every off-diagonal row of the actual matrix has absolute mass at most one. -/
theorem offDiag_mass (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) (j : ZMod s) :
    ∑ l∈univ.erase j, |realMatrix s t p u j l|≤1 := by
  have hnorm := rounded_sub_one s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hone : ‖(fun _ : ZMod s => (1 : ℂ))‖≤1 := by simp
  have hv := (PhaseCellOperator.rounded s t p u-1).le_of_opNorm_le_of_le hnorm hone
  have hr := (norm_le_pi_norm ((PhaseCellOperator.rounded s t p u-1) (fun _ => 1)) j).trans hv
  simp only [sub_apply, Pi.sub_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply, mul_one] at hr
  rw [←row_sum s t p u j, ←Complex.ofReal_one, ←Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hr
  have hm : (∑ l, realMatrix s t p u j l)≤2 := by
    have h := le_abs_self ((∑ l, realMatrix s t p u j l)-1)
    have : 0≤1/(8*(p : ℝ)) := by positivity
    linarith
  have hd : 1≤realMatrix s t p u j j := by
    unfold realMatrix
    exact_mod_cast matrix_diag s t p u j
  have hpos (l : ZMod s) : 0≤realMatrix s t p u j l := by
    unfold realMatrix
    exact_mod_cast matrix_nonneg s t p u j l
  simp_rw [abs_of_nonneg (hpos _)]
  have hsplit := sum_erase_add univ (fun l => realMatrix s t p u j l) (mem_univ j)
  linarith

theorem rounded_four_step (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) I (R c) c)
    (b x : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b)
    (e₁ e₂ e₃ e₄ e₅ : ℝ) (he₁ : 0≤e₁) (he₂ : 0≤e₂) (he₃ : 0≤e₃)
    (y r Z xB c xI : ZMod s → ℝ)
    (hy : ∀ j∈I, |y j-R b j|≤e₁)
    (hr : ∀ i∈univ\I, |r i-(b i-∑ j∈I, realMatrix s t p u i j*y j)|≤e₂)
    (hZ : ∀ i∈univ\I, schurOp (realMatrix s t p u) I (univ\I) R Z i=r i)
    (hxB : ∀ j∈univ\I, |xB j-Z j|≤e₃)
    (hc : ∀ i∈I, |c i-(b i-couple (realMatrix s t p u) (univ\I) xB i)|≤e₄)
    (hxI : ∀ j∈I, |xI j-R c j|≤e₅) :
    (∀ j∈univ\I, |xB j-x j|≤e₃+8*p*(e₁+e₂)) ∧
      ∀ j∈I, |xI j-x j|≤e₅+8*p*(e₄+(e₃+8*p*(e₁+e₂))) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  rw [←hU] at hA
  have hxs := solves_of_mulVec s t p u x b hx
  rw [←hU] at hxs
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  have hmass (i : ZMod s) (T : Finset (ZMod s)) (hiT : i∉T) :
      ∑ j∈T, |realMatrix s t p u i j|≤1 :=
    (sum_le_sum_of_subset_of_nonneg (fun j hj => mem_erase.mpr ⟨fun h => hiT (by rw [←h]; exact hj),
      mem_univ j⟩) fun _ _ _ => abs_nonneg _).trans
      (offDiag_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)
  have h := SchurDominance.rounded_four_step _ I _ hIB _ hμ hA R hR b x hxs 1 zero_le_one
    (fun i hi => hmass i I (mem_sdiff.mp hi).2)
    (fun i hi => hmass i _ (fun h => (mem_sdiff.mp h).2 hi))
    e₁ e₂ e₃ e₄ e₅ he₁ he₂ he₃ y r Z xB c xI hy hr hZ hxB hc hxI
  have hdiv (q : ℝ) : q/(1/(8*(p : ℝ)))=8*p*q := by field_simp
  simp only [one_mul, hdiv] at h
  exact h

end IntegerMultBounds.NLogN.PhaseCellMatrix
