module

public import IntegerMultBounds.NLogN.SchurBlockError

/-! Exact block-Schur identification. Eliminating every interior vertex, in
any order, leaves exactly the boundary set, and the reduced matrix acts on
boundary vectors as the block Schur operator `A_BB - A_BI A_II⁻¹ A_IB`. In
particular the Schur operator has the reduced matrix's dominance margin. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem run_set (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) :
    (run A S ks).2=S\ks.toFinset := by
  induction ks generalizing A S with
  | nil => simp [run]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [run, ite_eq_left hk, List.toFinset_cons]
      refine (ih _ _).trans ?_
      ext j
      simp only [mem_sdiff, mem_erase, mem_insert]
      tauto
    · simp only [run, ite_eq_right hk, ih, List.toFinset_cons]
      ext j
      simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨hj, hjk⟩
        exact ⟨hj, fun h => h.elim (fun e => hk (e ▸ hj)) hjk⟩
      · rintro ⟨hj, hjk⟩
        exact ⟨hj, fun h => hjk (Or.inr h)⟩

/-- Right-hand sides vanishing on eliminated vertices are carried unchanged. -/
theorem runRhs_of_zero (A : Matrix ι ι ℝ) (S : Finset ι) (b : ι → ℝ) (ks : List ι)
    (hb : ∀ k∈ks, b k=0) : runRhs A S b ks=b := by
  induction ks generalizing A S with
  | nil => rfl
  | cons k ks ih =>
    have hk0 := hb k List.mem_cons_self
    have hrest : ∀ k'∈ks, b k'=0 := fun k' h => hb k' (List.mem_cons_of_mem _ h)
    by_cases hk : k∈S
    · simp only [runRhs, ite_eq_left hk, hk0, mul_zero, sub_zero]
      exact ih _ _ hrest
    · simp only [runRhs, ite_eq_right hk]
      exact ih _ _ hrest

/-- The Schur operator is the reduced matrix after eliminating the interior. -/
theorem schurOp_eq_run (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ)
    (hμ : 0<μ) (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ)
    (hR : ∀ c, Solves A I (R c) c) (ks : List ι) (hks : ks.toFinset=I)
    (x : ι → ℝ) (i : ι) (hi : i∈B) :
    schurOp A I B R x i=∑ j∈B, (run A (I∪B) ks).1 i j*x j := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  have hset : (run A (I∪B) ks).2=B := by
    rw [run_set, hks, union_sdiff_left, sdiff_eq_self_of_disjoint hIB.symm]
  -- Glue the interior response to the boundary values.
  set v := couple A B x
  set X := glue I (R (0-v)) x with hX
  have hR0 : ∀ k∈I, R 0 k=0 := fun k hk =>
    solves_unique A I μ hμ hAI _ 0 0 (hR 0) (fun i _ => by simp) k hk
  have hneg : ∀ k∈I, R (0-v) k=-R v k := fun k hk => by
    rw [solver_sub A I μ hμ hAI R hR 0 v k hk, hR0 k hk, zero_sub]
  have hXI : ∑ j∈I, A i j*X j=-∑ j∈I, A i j*R v j := by
    rw [←sum_neg_distrib]
    exact sum_congr rfl fun j hj => by
      simp only [hX, glue, hj, ↓reduceIte]
      rw [hneg j hj, mul_neg]
  have hXB (i' : ι) : ∑ j∈B, A i' j*X j=v i' :=
    sum_congr rfl fun j hj => by simp [hX, glue, disjoint_right.mp hIB hj]
  set c : ι → ℝ := fun i' => ∑ j∈I∪B, A i' j*X j with hc
  have hsol : Solves A (I∪B) X c := fun _ _ => rfl
  have hcI : ∀ k∈ks, c k=0 := by
    intro k hk
    have hkI : k∈I := hks ▸ List.mem_toFinset.mpr hk
    simp only [hc]
    rw [sum_union hIB, hXB]
    have hrow := hR (0-v) k hkI
    have hIk : ∑ j∈I, A k j*X j=∑ j∈I, A k j*R (0-v) j :=
      sum_congr rfl fun j hj => by simp [hX, glue, hj]
    rw [hIk, hrow]
    simp
  have hred := run_solves A (I∪B) μ hμ hA ks X c hsol
  rw [runRhs_of_zero A (I∪B) c ks hcI, hset] at hred
  have h := hred i hi
  have hcB : c i=schurOp A I B R x i := by
    simp only [hc, schurOp]
    rw [sum_union hIB, hXI, hXB]
    ring
  rw [←hcB, ←h]
  exact sum_congr rfl fun j hj => by simp [hX, glue, disjoint_right.mp hIB hj]

/-- The Schur operator inherits the reduced matrix's dominance margin. -/
theorem schur_dominates (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ)
    (hμ : 0<μ) (hA : DominatesOn A (I∪B) μ) (ks : List ι) (hks : ks.toFinset=I) :
    DominatesOn (run A (I∪B) ks).1 B μ := by
  have h := run_gap A (I∪B) μ hμ hA ks
  rwa [run_set, hks, union_sdiff_left, sdiff_eq_self_of_disjoint hIB.symm] at h

end IntegerMultBounds.NLogN.SchurDominance
