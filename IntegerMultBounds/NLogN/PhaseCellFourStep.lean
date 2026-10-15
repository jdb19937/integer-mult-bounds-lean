module

public import IntegerMultBounds.NLogN.PhaseCellBoundarySolve
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! The four-step interior/boundary solve on the actual rounded periodic
Gaussian matrix. For any interior set and any exact interior solver, the
Schur boundary solution and the interior recovery reproduce the full solution,
and the boundary values are bounded by `8p` times the right-hand side. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s] [NeZero t]

theorem four_step (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) I (R c) c)
    (b x xB : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b)
    (hS : ∀ i∈univ\I, schurOp (realMatrix s t p u) I (univ\I) R xB i=
      residual (realMatrix s t p u) I R b i)
    (C : ℝ) (hb : ∀ i, |b i|≤C) :
    (∀ j∈univ\I, xB j=x j ∧ |xB j|≤8*p*C) ∧
      ∀ j∈I, R (b-couple (realMatrix s t p u) (univ\I) xB) j=x j := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  rw [←hU] at hA
  have hxs := solves_of_mulVec s t p u x b hx
  rw [←hU] at hxs
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  obtain ⟨hBx, hIx⟩ := SchurDominance.four_step _ I _ hIB _ hμ hA R hR b x xB hxs hS
  refine ⟨fun j hj => ⟨hBx j hj, ?_⟩, hIx⟩
  have h := four_step_bound _ I _ hIB _ hμ hA R hR b xB hS C (fun i _ => hb i) j hj
  rwa [div_div_eq_mul_div, div_one, mul_comm] at h

end IntegerMultBounds.NLogN.PhaseCellMatrix
