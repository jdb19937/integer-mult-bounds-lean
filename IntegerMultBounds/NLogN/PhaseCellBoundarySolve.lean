module

import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.SchurSolve
public import IntegerMultBounds.NLogN.PhaseCellMatrix
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.Machine

/-! Exact boundary solves for the actual rounded periodic Gaussian matrix.
After any interior elimination, the reduced system with the carried
right-hand side has exactly the restricted full solution, and its solutions
are bounded by `8p` times the reduced right-hand side. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
variable (s t : ℕ) [NeZero s] [NeZero t]

omit [NeZero t] in
theorem solves_of_mulVec (p u : ℕ) (x b : ZMod s → ℝ)
    (hx : Matrix.mulVec (realMatrix s t p u) x=b) :
    SchurDominance.Solves (realMatrix s t p u) Finset.univ x b := fun i _ => by
  rw [←hx]
  rfl

/-- The reduced boundary system determines the full solution and is
conditioned by the selected margin `1/(8p)`. -/
theorem boundary_solve (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (ks : List (ZMod s)) (x b y : ZMod s → ℝ)
    (hx : Matrix.mulVec (realMatrix s t p u) x=b)
    (hy : SchurDominance.Solves
      (SchurDominance.run (realMatrix s t p u) Finset.univ ks).1
      (SchurDominance.run (realMatrix s t p u) Finset.univ ks).2 y
      (SchurDominance.runRhs (realMatrix s t p u) Finset.univ b ks))
    (B : ℝ) (hB : ∀ i∈(SchurDominance.run (realMatrix s t p u) Finset.univ ks).2,
      |SchurDominance.runRhs (realMatrix s t p u) Finset.univ b ks i|≤B)
    (i : ZMod s) (hi : i∈(SchurDominance.run (realMatrix s t p u) Finset.univ ks).2) :
    y i=x i ∧ |y i|≤8*p*B := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  refine ⟨SchurDominance.run_solution _ _ _ hμ hA ks x b y
    (solves_of_mulVec s t p u x b hx) hy i hi, ?_⟩
  have h := SchurDominance.solves_bound _ _ _ hμ
    (boundary_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget ks) y _ hy B hB i hi
  rwa [div_div_eq_mul_div, div_one, mul_comm] at h

end IntegerMultBounds.NLogN.PhaseCellMatrix
