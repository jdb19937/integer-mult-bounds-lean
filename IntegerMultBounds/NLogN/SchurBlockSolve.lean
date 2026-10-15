module

public import IntegerMultBounds.NLogN.SchurSolve

/-! The source's two interior passes and one boundary solve, for any exact
interior solver `R` and disjoint interior `I` and boundary `B`:
`y = R b`, `r = b_B - A_BI y`, `S x_B = r`, `x_I = R (b - A_IB x_B)`.
Under a dominance margin on `I ∪ B`, the glued vector is the unique full
solution and every boundary solution is bounded by `max |b| / μ`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- Boundary-to-interior coupling `A_IB x_B`. -/
def couple (A : Matrix ι ι ℝ) (B : Finset ι) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j∈B, A i j*x j

/-- Interior recovery glued to the boundary values. -/
def glue (I : Finset ι) (xI xB : ι → ℝ) (j : ι) : ℝ := if j∈I then xI j else xB j

/-- The Schur boundary operator `A_BB x - A_BI R (A_IB x)`. -/
def schurOp (A : Matrix ι ι ℝ) (I B : Finset ι) (R : (ι → ℝ) → ι → ℝ) (x : ι → ℝ)
    (i : ι) : ℝ :=
  couple A B x i-∑ j∈I, A i j*R (couple A B x) j

/-- The boundary residual `b_B - A_BI R b`. -/
def residual (A : Matrix ι ι ℝ) (I : Finset ι) (R : (ι → ℝ) → ι → ℝ) (b : ι → ℝ)
    (i : ι) : ℝ :=
  b i-∑ j∈I, A i j*R b j

theorem dominates_mono (A : Matrix ι ι ℝ) (S T : Finset ι) (μ : ℝ) (hST : T⊆S)
    (hA : DominatesOn A S μ) : DominatesOn A T μ := fun i hi =>
  le_trans (add_le_add_right (sum_le_sum_of_subset_of_nonneg (erase_subset_erase i hST)
    fun _ _ _ => abs_nonneg _) μ) (hA i (hST hi))

/-- Any boundary values satisfying the boundary rows glue to a full solution. -/
theorem glue_solves (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c) (b xB : ι → ℝ)
    (hxB : ∀ i∈B, ∑ j∈I, A i j*R (b-couple A B xB) j+couple A B xB i=b i) :
    Solves A (I∪B) (glue I (R (b-couple A B xB)) xB) b := by
  intro i hi
  rw [sum_union hIB]
  have hI : ∑ j∈I, A i j*glue I (R (b-couple A B xB)) xB j=
      ∑ j∈I, A i j*R (b-couple A B xB) j :=
    sum_congr rfl fun j hj => by simp [glue, hj]
  have hB : ∑ j∈B, A i j*glue I (R (b-couple A B xB)) xB j=couple A B xB i :=
    sum_congr rfl fun j hj => by simp [glue, disjoint_right.mp hIB hj]
  rw [hI, hB]
  rcases mem_union.mp hi with hiI | hiB
  · rw [hR _ i hiI]
    simp
  · exact hxB i hiB

/-- Exact interior solves are linear on the interior. -/
theorem solver_sub (A : Matrix ι ι ℝ) (I : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A I μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (c c' : ι → ℝ) (j : ι) (hj : j∈I) : R (c-c') j=R c j-R c' j := by
  refine solves_unique A I μ hμ hA _ (R c-R c') (c-c') (hR _) ?_ j hj
  intro i hi
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib, hR c i hi, hR c' i hi]

/-- The four-step solve is exact: a boundary solution of `S x_B = r` glued
to `x_I = R (b - A_IB x_B)` is the unique full solution `x`. -/
theorem four_step (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (b x xB : ι → ℝ) (hx : Solves A (I∪B) x b)
    (hS : ∀ i∈B, schurOp A I B R xB i=residual A I R b i) :
    (∀ j∈B, xB j=x j) ∧ ∀ j∈I, R (b-couple A B xB) j=x j := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  have hglue := glue_solves A I B hIB R hR b xB (fun i hi => by
    have h := hS i hi
    simp only [schurOp, residual] at h
    rw [sum_congr rfl fun j hj => by rw [solver_sub A I μ hμ hAI R hR b _ j hj]]
    simp only [mul_sub, sum_sub_distrib]
    linarith)
  have hu := solves_unique A _ μ hμ hA _ x b hglue hx
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := hu j (mem_union_right _ hj)
    simpa [glue, disjoint_right.mp hIB hj] using this
  · have := hu j (mem_union_left _ hj)
    simpa [glue, hj] using this

/-- Every boundary solution is bounded by the full right-hand side and margin. -/
theorem four_step_bound (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ)
    (hμ : 0<μ) (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ)
    (hR : ∀ c, Solves A I (R c) c) (b xB : ι → ℝ)
    (hS : ∀ i∈B, schurOp A I B R xB i=residual A I R b i) (C : ℝ)
    (hb : ∀ i∈I∪B, |b i|≤C) (j : ι) (hj : j∈B) : |xB j|≤C/μ := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  have hglue := glue_solves A I B hIB R hR b xB (fun i hi => by
    have h := hS i hi
    simp only [schurOp, residual] at h
    rw [sum_congr rfl fun j hj => by rw [solver_sub A I μ hμ hAI R hR b _ j hj]]
    simp only [mul_sub, sum_sub_distrib]
    linarith)
  have := solves_bound A _ μ hμ hA _ b hglue C hb j (mem_union_right _ hj)
  simpa [glue, disjoint_right.mp hIB hj] using this

end IntegerMultBounds.NLogN.SchurDominance
