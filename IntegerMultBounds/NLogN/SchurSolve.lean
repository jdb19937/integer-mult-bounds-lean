module

public import IntegerMultBounds.NLogN.SchurElimination

/-! Exact solves through successive Schur elimination. Every full solution
restricts to a solution of the eliminated system with the carried right-hand
side, eliminated vertices are recovered from their pivot rows, and a positive
dominance margin bounds and determines every active solution. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- The linear system on active rows and columns. -/
def Solves (A : Matrix ι ι ℝ) (S : Finset ι) (x b : ι → ℝ) : Prop :=
  ∀ i∈S, ∑ j∈S, A i j*x j=b i

/-- Right-hand-side updates carried alongside `run`. -/
noncomputable def runRhs (A : Matrix ι ι ℝ) (S : Finset ι) (b : ι → ℝ) :
    List ι → ι → ℝ
  | [] => b
  | k::ks => if k∈S then
      runRhs (eliminate A k) (S.erase k) (fun i => b i-A i k/A k k*b k) ks
    else runRhs A S b ks

theorem eliminate_solves (A : Matrix ι ι ℝ) (S : Finset ι) (k : ι) (hk : k∈S)
    (hdiag : A k k≠0) (x b : ι → ℝ) (h : Solves A S x b) :
    Solves (eliminate A k) (S.erase k) x (fun i => b i-A i k/A k k*b k) := fun i hi =>
  eliminate_equation A S k i hk hdiag x b (h i (Finset.mem_of_mem_erase hi)) (h k hk)

/-- Every full solution solves the eliminated system on the remaining set. -/
theorem run_solves (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (ks : List ι) (x b : ι → ℝ) (h : Solves A S x b) :
    Solves (run A S ks).1 (run A S ks).2 x (runRhs A S b ks) := by
  induction ks generalizing A S b with
  | nil => exact h
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [run, runRhs, ite_eq_left hk]
      exact ih _ _ (eliminate_preserves A S μ hμ hA k hk) _
        (eliminate_solves A S k hk (pivot_pos A S μ hμ hA k hk).ne' x b h)
    · simpa only [run, runRhs, ite_eq_right hk] using ih A S hA b h

/-- Back substitution: a pivot row determines its own coordinate. -/
theorem pivot_recover (A : Matrix ι ι ℝ) (S : Finset ι) (x b : ι → ℝ)
    (h : Solves A S x b) (k : ι) (hk : k∈S) (hdiag : A k k≠0) :
    x k=(b k-∑ j∈S.erase k, A k j*x j)/A k k := by
  have hsplit := Finset.sum_erase_add S (fun j => A k j*x j) hk
  rw [h k hk] at hsplit
  field_simp
  linarith

/-- A positive dominance margin bounds every active solution coordinate. -/
theorem solves_bound (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (x b : ι → ℝ) (h : Solves A S x b) (B : ℝ)
    (hb : ∀ i∈S, |b i|≤B) (i : ι) (hi : i∈S) : |x i|≤B/μ := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S (fun j => |x j|) ⟨i, hi⟩
  have hsplit := Finset.sum_erase_add S (fun j => A m j*x j) hm
  rw [h m hm] at hsplit
  have hoff : |∑ j∈S.erase m, A m j*x j|≤(∑ j∈S.erase m, |A m j|)*|x m| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_of_mem_erase hj)) (abs_nonneg _)
  have hdom := hA m hm
  have hdiag := pivot_pos A S μ hμ hA m hm
  have hcenter : |A m m*x m|=A m m*|x m| := by rw [abs_mul, abs_of_pos hdiag]
  have htri : |A m m*x m|≤|b m|+|∑ j∈S.erase m, A m j*x j| := by
    have : A m m*x m=b m-∑ j∈S.erase m, A m j*x j := by linarith
    rw [this]
    exact abs_sub _ _
  have hgap : μ*|x m|≤(A m m-∑ j∈S.erase m, |A m j|)*|x m| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hxm : μ*|x m|≤B := by nlinarith [hb m hm]
  rw [le_div_iff₀ hμ]
  nlinarith [hmax i hi]

/-- Active solutions with a common right-hand side coincide. -/
theorem solves_unique (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (x y b : ι → ℝ) (hx : Solves A S x b) (hy : Solves A S y b)
    (i : ι) (hi : i∈S) : x i=y i := by
  have hd : Solves A S (x-y) 0 := by
    intro j hj
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hx j hj, hy j hj,
      sub_self, Pi.zero_apply]
  have hbound := solves_bound A S μ hμ hA (x-y) 0 hd 0 (by simp) i hi
  simp only [zero_div, Pi.sub_apply] at hbound
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hbound)

/-- Solving the eliminated system recovers the full solution on the remaining
set, and any such solution is bounded by the margin. -/
theorem run_solution (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (ks : List ι) (x b y : ι → ℝ) (hx : Solves A S x b)
    (hy : Solves (run A S ks).1 (run A S ks).2 y (runRhs A S b ks))
    (i : ι) (hi : i∈(run A S ks).2) : y i=x i :=
  solves_unique _ _ μ hμ (run_gap A S μ hμ hA ks) y x _ hy
    (run_solves A S μ hμ hA ks x b hx) i hi

end IntegerMultBounds.NLogN.SchurDominance
