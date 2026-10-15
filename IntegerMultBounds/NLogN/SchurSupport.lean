module

public import IntegerMultBounds.NLogN.SchurElimination

/-! Fill-in through successive Schur elimination. If every eliminated vertex
couples only to vertices of its own cell, then every entry of the reduced
matrix is either an original entry or joins two vertices of one cell. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A new entry needs both of its links through the pivot. -/
theorem eliminate_support (A : Matrix ι ι ℝ) (k i j : ι) (h : eliminate A k i j≠0) :
    A i j≠0 ∨ (A i k≠0 ∧ A k j≠0) := by
  by_contra hc
  push Not at hc
  apply h
  unfold eliminate
  by_cases hik : A i k=0
  · simp [hc.1, hik]
  · simp [hc.1, hc.2 hik]

/-- Entries of `M` are original entries of `A` or lie within one cell. -/
def CellSupported {κ : Type*} (A M : Matrix ι ι ℝ) (c : ι → κ) : Prop :=
  ∀ i j, M i j≠0 → A i j≠0 ∨ c i=c j

theorem run_cellSupported {κ : Type*} (A : Matrix ι ι ℝ) (c : ι → κ) (E : ι → Prop)
    (hloc : ∀ k, E k → ∀ i, (A i k≠0 → c i=c k) ∧ (A k i≠0 → c i=c k))
    (M : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (hks : ∀ k∈ks, E k)
    (hM : CellSupported A M c) : CellSupported A (run M S ks).1 c := by
  induction ks generalizing M S with
  | nil => exact hM
  | cons k ks ih =>
    have hk := hks k List.mem_cons_self
    have hrest : ∀ k'∈ks, E k' := fun k' h => hks k' (List.mem_cons_of_mem _ h)
    by_cases hkS : k∈S
    · simp only [run, ite_eq_left hkS]
      refine ih _ _ hrest ?_
      intro i j hij
      rcases eliminate_support M k i j hij with h | ⟨hik, hkj⟩
      · exact hM i j h
      · right
        have hci : c i=c k := (hM i k hik).elim (hloc k hk i).1 id
        have hcj : c j=c k := (hM k j hkj).elim (hloc k hk j).2 (fun h => h.symm)
        rw [hci, hcj]
    · simpa only [run, ite_eq_right hkS] using ih M S hrest hM

/-- Eliminating local vertices of `A` leaves only original or same-cell entries. -/
theorem run_support {κ : Type*} (A : Matrix ι ι ℝ) (c : ι → κ) (E : ι → Prop)
    (hloc : ∀ k, E k → ∀ i, (A i k≠0 → c i=c k) ∧ (A k i≠0 → c i=c k))
    (S : Finset ι) (ks : List ι) (hks : ∀ k∈ks, E k) (i j : ι)
    (h : (run A S ks).1 i j≠0) : A i j≠0 ∨ c i=c j :=
  run_cellSupported A c E hloc A S ks hks (fun _ _ h => Or.inl h) i j h

end IntegerMultBounds.NLogN.SchurDominance
