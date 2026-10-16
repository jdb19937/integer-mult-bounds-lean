module

public import IntegerMultBounds.NLogN.SchurLU
public import IntegerMultBounds.NLogN.SchurSupport
public import IntegerMultBounds.NLogN.SchurLUBackward

/-! Fill of ordered elimination. Eliminate in increasing order of a position
function. If a support relation contains every original entry and is closed
under fill through earlier pivots (`R i k → R k j → R i j` whenever the pivot
precedes both), then every multiplier and every pivot-row entry lies in the
relation. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open Finset
variable {ι : Type*} [DecidableEq ι]

/-- Ordered closure of a support relation. -/
def FillClosed (pos : ι → ℕ) (R : ι → ι → Prop) : Prop :=
  ∀ k i j, pos k<pos i → pos k<pos j → R i k → R k j → R i j

theorem fill_support (pos : ι → ℕ) (R : ι → ι → Prop) (hR : FillClosed pos R) (ks : List ι) :
    ∀ (A : Matrix ι ι ℝ) (S : Finset ι), S⊆ks.toFinset → ks.Pairwise (fun a b => pos a<pos b) →
      (∀ i∈S, ∀ j∈S, A i j≠0 → R i j) →
      (∀ i k, luL A S ks i k≠0 → i=k ∨ R i k) ∧ (∀ k j, luU A S ks k j≠0 → R k j) := by
  induction ks with
  | nil =>
    intro A S hsub _ hA
    have hS : S=∅ := by simpa using hsub
    subst hS
    refine ⟨fun i k h => ?_, fun k j h => ?_⟩ <;> simp [luL, luU] at h
  | cons k ks ih =>
    intro A S hsub hsort hA
    have hsort' := List.pairwise_cons.mp hsort
    by_cases hk : k∈S
    · have hsub' : S.erase k⊆ks.toFinset := by
        intro x hx
        have hxS := mem_of_mem_erase hx
        have := hsub hxS
        simp only [List.toFinset_cons, mem_insert] at this
        rcases this with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      have hlater : ∀ x∈S.erase k, pos k<pos x := fun x hx =>
        hsort'.1 x (List.mem_toFinset.mp (hsub' hx))
      have hA' : ∀ i∈S.erase k, ∀ j∈S.erase k, elimM A k i j≠0 → R i j := by
        intro i hi j hj h
        rcases eliminate_support A k i j h with h1 | ⟨h1, h2⟩
        · exact hA i (mem_of_mem_erase hi) j (mem_of_mem_erase hj) h1
        · exact hR k i j (hlater i hi) (hlater j hj) (hA i (mem_of_mem_erase hi) k hk h1)
            (hA k hk j (mem_of_mem_erase hj) h2)
      obtain ⟨hL, hU⟩ := ih (elimM A k) (S.erase k) hsub' hsort'.2 hA'
      refine ⟨fun i j h => ?_, fun i j h => ?_⟩
      · simp only [luL, hk, ite_true] at h
        split at h
        · rename_i hjk
          subst hjk
          split at h
          · exact Or.inl ‹_›
          · split at h
            · right
              by_contra hR'
              apply h
              rw [hA i ‹_› j hk |>.mt hR' |> not_not.mp, zero_div]
            · exact absurd rfl h
        · exact hL i j h
      · simp only [luU, hk, ite_true] at h
        split at h
        · rename_i hik
          subst hik
          split at h
          · by_contra hR'
            exact h ((hA i hk j ‹_›).mt hR' |> not_not.mp)
          · exact absurd rfl h
        · exact hU i j h
    · have hsub' : S⊆ks.toFinset := by
        intro x hx
        have := hsub hx
        simp only [List.toFinset_cons, mem_insert] at this
        rcases this with h | h
        · exact absurd (h ▸ hx) hk
        · exact h
      obtain ⟨hL, hU⟩ := ih A S hsub' hsort'.2 hA
      refine ⟨fun i j h => ?_, fun i j h => ?_⟩
      · simp only [luL, hk, ite_false] at h
        exact hL i j h
      · simp only [luU, hk, ite_false] at h
        exact hU i j h

/-- Rounded elimination with `rd 0 = 0` creates no entries outside the exact
fill: if the relation contains the original entries and is closed under
ordered fill, every rounded multiplier and pivot-row entry lies in it, and the
factors are triangular in the elimination order. -/
theorem fill_support_r (rd : ℝ → ℝ) (hrd0 : rd 0=0) (pos : ι → ℕ) (R : ι → ι → Prop)
    (hR : FillClosed pos R) (ks : List ι) :
    ∀ (A : Matrix ι ι ℝ) (S : Finset ι), S⊆ks.toFinset → ks.Pairwise (fun a b => pos a<pos b) →
      (∀ i∈S, ∀ j∈S, A i j≠0 → R i j) →
      (∀ i k, luLr rd A S ks i k≠0 → i=k ∨ (R i k ∧ pos k<pos i)) ∧
        (∀ k j, luUr rd A S ks k j≠0 → R k j ∧ pos k≤pos j) := by
  induction ks with
  | nil =>
    intro A S hsub _ hA
    have hS : S=∅ := by simpa using hsub
    subst hS
    refine ⟨fun i k h => ?_, fun k j h => ?_⟩ <;> simp [luLr, luUr] at h
  | cons k ks ih =>
    intro A S hsub hsort hA
    have hsort' := List.pairwise_cons.mp hsort
    by_cases hk : k∈S
    · have hsub' : S.erase k⊆ks.toFinset := by
        intro x hx
        have := hsub (mem_of_mem_erase hx)
        simp only [List.toFinset_cons, mem_insert] at this
        rcases this with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      have hlater : ∀ x∈S.erase k, pos k<pos x := fun x hx =>
        hsort'.1 x (List.mem_toFinset.mp (hsub' hx))
      have hA' : ∀ i∈S.erase k, ∀ j∈S.erase k, relim rd A k i j≠0 → R i j := by
        intro i hi j hj h
        by_contra hR'
        apply h
        have hij : A i j=0 := by
          by_contra hne; exact hR' (hA i (mem_of_mem_erase hi) j (mem_of_mem_erase hj) hne)
        unfold relim
        by_cases hik : A i k=0
        · rw [hij, hik, zero_div, hrd0, zero_mul, sub_zero, hrd0]
        · have hkj : A k j=0 := by
            by_contra hne
            exact hR' (hR k i j (hlater i hi) (hlater j hj) (hA i (mem_of_mem_erase hi) k hk hik)
              (hA k hk j (mem_of_mem_erase hj) hne))
          rw [hij, hkj, mul_zero, sub_zero, hrd0]
      obtain ⟨hL, hU⟩ := ih (relim rd A k) (S.erase k) hsub' hsort'.2 hA'
      refine ⟨fun i j h => ?_, fun i j h => ?_⟩
      · simp only [luLr, hk, ite_true] at h
        split at h
        · rename_i hjk
          subst hjk
          split at h
          · exact Or.inl ‹_›
          · split at h
            · rename_i hik hiS
              right
              refine ⟨?_, hlater i (mem_erase.mpr ⟨hik, hiS⟩)⟩
              by_contra hR'
              apply h
              rw [show A i j=0 by by_contra hne; exact hR' (hA i hiS j hk hne), zero_div, hrd0]
            · exact absurd rfl h
        · rcases hL i j h with h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
      · simp only [luUr, hk, ite_true] at h
        split at h
        · rename_i hik
          subst hik
          split at h
          · rename_i hjS
            refine ⟨?_, ?_⟩
            · by_contra hR'
              exact h (by by_contra hne; exact hR' (hA i hk j hjS hne))
            · by_cases hji : j=i
              · rw [hji]
              · exact (hlater j (mem_erase.mpr ⟨hji, hjS⟩)).le
          · exact absurd rfl h
        · exact hU i j h
    · have hsub' : S⊆ks.toFinset := by
        intro x hx
        have := hsub hx
        simp only [List.toFinset_cons, mem_insert] at this
        rcases this with h | h
        · exact absurd (h ▸ hx) hk
        · exact h
      obtain ⟨hL, hU⟩ := ih A S hsub' hsort'.2 hA
      refine ⟨fun i j h => ?_, fun i j h => ?_⟩
      · simp only [luLr, hk, ite_false] at h
        exact hL i j h
      · simp only [luUr, hk, ite_false] at h
        exact hU i j h

end IntegerMultBounds.NLogN.SchurDominance
