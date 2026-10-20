module

import IntegerMultBounds.NLogN.SchurIdentify
import IntegerMultBounds.NLogN.SchurLURounded
import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.PhaseCellMatrix
public import IntegerMultBounds.NLogN.SchurLU
public import IntegerMultBounds.NLogN.SchurBlockSolve
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! Rounded boundary solve of the actual rounded periodic Gaussian matrix.
After eliminating the interior, the boundary Schur matrix keeps margin
`1/(8p)` and row mass at most two, so its elimination factors have multiplier
rows at most `1+16p` and pivot rows at most two. Rounded factors and rounded
triangular solves give the boundary stage error `e₃` against the exact Schur
solution. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance ContinuousLinearMap
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- Every row of the actual matrix has absolute mass at most two. -/
theorem row_mass (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) (j : ZMod s) :
    ∑ l, |realMatrix s t p u j l|≤2 := by
  have hnorm := rounded_sub_one s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hone : ‖(fun _ : ZMod s => (1 : ℂ))‖≤1 := by simp
  have hv := (PhaseCellOperator.rounded s t p u-1).le_of_opNorm_le_of_le hnorm hone
  have hr := (norm_le_pi_norm ((PhaseCellOperator.rounded s t p u-1) (fun _ => 1)) j).trans hv
  simp only [sub_apply, Pi.sub_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply, mul_one] at hr
  rw [←row_sum s t p u j, ←Complex.ofReal_one, ←Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hr
  have hpos (l : ZMod s) : 0≤realMatrix s t p u j l := by
    unfold realMatrix
    exact_mod_cast matrix_nonneg s t p u j l
  simp_rw [abs_of_nonneg (hpos _)]
  have h := le_abs_self ((∑ l, realMatrix s t p u j l)-1)
  have : 0≤1/(8*(p : ℝ)) := by positivity
  linarith

theorem rounded_boundary (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) I (R c) c)
    (ks kb : List (ZMod s)) (hks : ks.toFinset=I)
    (Lh Uh : Matrix (ZMod s) (ZMod s) ℝ) (Z r xh y : ZMod s → ℝ)
    (hZ : ∀ i∈univ\I, schurOp (realMatrix s t p u) I (univ\I) R Z i=r i)
    (εL εU η δ ρ : ℝ) (hδ : 0≤δ) (hεL : 0≤εL) (hεU : 0≤εU) (hρ : 0≤ρ)
    (hr : ∀ i∈univ\I, |r i|≤ρ)
    (hLh : ∀ i∈univ\I, ∑ k∈univ\I, |Lh i k-luL (run (realMatrix s t p u) univ ks).1
      (univ\I) kb i k|≤εL)
    (hUh : ∀ k∈univ\I, ∑ j∈univ\I, |Uh k j-luU (run (realMatrix s t p u) univ ks).1
      (univ\I) kb k j|≤εU)
    (hf : ∀ k∈univ\I, |y k+∑ j∈(univ\I).erase k, Lh k j*y j-r k|≤η)
    (hb : ∀ k∈univ\I, |∑ j∈univ\I, Uh k j*xh j-y k|≤δ)
    (hsmall : ((1+16*p)*εU+εL*(2+εU))*(8*p)≤1/2) (j : ZMod s) (hj : j∈univ\I) :
    |xh j-Z j|≤2*(((1+16*p)*δ+η+εL*δ)*(8*p)+((1+16*p)*εU+εL*(2+εU))*(8*p)*(8*p*ρ)) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  set μ : ℝ := 1/(8*(p : ℝ))
  have hμ : 0<μ := by positivity
  have hdiv (q : ℝ) : q/μ=q*(8*p) := by simp only [μ]; field_simp
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  have hA0 := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hA := hA0
  rw [←hU] at hA
  set Sm := (run (realMatrix s t p u) univ ks).1
  have hSm : Sm=(run (realMatrix s t p u) (I∪(univ\I)) ks).1 := by rw [hU]
  have hSdom : DominatesOn Sm (univ\I) μ := by
    rw [hSm]
    exact schur_dominates _ I _ hIB μ hμ hA ks hks
  have hsol : Solves Sm (univ\I) Z r := by
    intro i hi
    rw [←hZ i hi, schurOp_eq_run _ I _ hIB μ hμ hA R hR ks hks Z i hi, hSm]
  have hmass : ∀ i∈univ\I, ∑ k∈univ\I, |Sm i k|≤2 := by
    intro i _
    have h := run_mass (realMatrix s t p u) univ μ hμ hA0 ks i
    rw [run_set, hks] at h
    exact h.trans (row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)
  have hX : ∀ i∈univ\I, |Z i|≤8*p*ρ := by
    intro i hi
    have h := solves_bound Sm _ μ hμ hSdom Z r hsol ρ hr i hi
    rwa [hdiv, mul_comm] at h
  have hΛ : ∀ i∈univ\I, ∑ k∈univ\I, |luL Sm (univ\I) kb i k|≤1+16*p := by
    intro i hi
    have h := luL_mass Sm _ μ hμ hSdom kb i hi
    rw [hdiv] at h
    nlinarith [hmass i hi]
  have hM : ∀ k∈univ\I, ∑ j∈univ\I, |luU Sm (univ\I) kb k j|≤2 := fun k hk =>
    (luU_row Sm _ μ hμ hSdom kb k hk).2.trans (hmass k hk)
  have hsmall' : ((1+16*p)*εU+εL*(2+εU))/μ≤1/2 := by rwa [hdiv]
  have h := rounded_lu Sm Lh Uh (univ\I) μ hμ hSdom kb Z r xh y hsol (1+16*p) 2 εL εU η δ
    (8*p*ρ) hδ hεL hεU (by positivity) hΛ (by positivity) (by norm_num) hM hLh hUh hX hf hb
    hsmall' j hj
  rwa [hdiv, hdiv] at h

end IntegerMultBounds.NLogN.PhaseCellMatrix
