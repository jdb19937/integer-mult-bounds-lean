module

public import IntegerMultBounds.NLogN.SchurFill

/-! Rounded forward and back substitution in elimination order. Forward
substitution rounds each unit-lower row once; back substitution rounds each
quotient by the pivot once. With triangular factors in the order of the list,
the computed vectors satisfy the residual hypotheses of `backward_lu`:
forward rows within `η`, back rows within `M η` for pivots at most `M`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- Forward substitution along a list, with the processed set `done`. -/
noncomputable def fwd (rd : ℝ → ℝ) (L : Matrix ι ι ℝ) (b : ι → ℝ) :
    Finset ι → (ι → ℝ) → List ι → ι → ℝ
  | _, y, [] => y
  | done, y, k::ks => fwd rd L b (insert k done)
      (Function.update y k (rd (b k-∑ j∈done, L k j*y j))) ks

/-- Back substitution along a list, dividing by the pivot. -/
noncomputable def bwd (rd : ℝ → ℝ) (U : Matrix ι ι ℝ) (y : ι → ℝ) :
    Finset ι → (ι → ℝ) → List ι → ι → ℝ
  | _, x, [] => x
  | done, x, k::ks => bwd rd U y (insert k done)
      (Function.update x k (rd ((y k-∑ j∈done, U k j*x j)/U k k))) ks

theorem fwd_off (rd : ℝ → ℝ) (L : Matrix ι ι ℝ) (b : ι → ℝ) (ks : List ι) :
    ∀ (done : Finset ι) (y : ι → ℝ) (x : ι), x∉ks → fwd rd L b done y ks x=y x := by
  induction ks with
  | nil => intro _ _ _ _; rfl
  | cons k ks ih =>
    intro done y x hx
    simp only [List.mem_cons, not_or] at hx
    simp only [fwd]
    rw [ih _ _ x hx.2, Function.update_of_ne hx.1]

theorem bwd_off (rd : ℝ → ℝ) (U : Matrix ι ι ℝ) (y : ι → ℝ) (ks : List ι) :
    ∀ (done : Finset ι) (x : ι → ℝ) (z : ι), z∉ks → bwd rd U y done x ks z=x z := by
  induction ks with
  | nil => intro _ _ _ _; rfl
  | cons k ks ih =>
    intro done x z hz
    simp only [List.mem_cons, not_or] at hz
    simp only [bwd]
    rw [ih _ _ z hz.2, Function.update_of_ne hz.1]

/-- Forward residual: with a lower factor triangular in the list order, every
processed row is rounded within `η`. -/
theorem fwd_residual (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (pos : ι → ℕ)
    (L : Matrix ι ι ℝ) (b : ι → ℝ) (S : Finset ι)
    (hL : ∀ i k, L i k≠0 → i=k ∨ pos k<pos i) (ks : List ι) :
    ∀ (done : Finset ι) (y : ι → ℝ), ks.Pairwise (fun a b => pos a<pos b) →
      (∀ k∈ks, k∈S) → done=S\ks.toFinset →
      ∀ k∈ks, |fwd rd L b done y ks k+∑ j∈S.erase k, L k j*fwd rd L b done y ks j-b k|≤η := by
  induction ks with
  | nil => intro _ _ _ _ _ k hk; simp at hk
  | cons k ks ih =>
    intro done y hsort hks hdone k' hk'
    have hsort' := List.pairwise_cons.mp hsort
    have hkS := hks k List.mem_cons_self
    have hknot : k∉ks := fun h => (lt_irrefl _ (hsort'.1 k h))
    have hdone' : insert k done=S\ks.toFinset := by
      rw [hdone]
      ext x
      simp only [mem_insert, mem_sdiff, List.mem_toFinset, List.toFinset_cons]
      constructor
      · rintro (rfl | ⟨hx, hx'⟩)
        · exact ⟨hkS, hknot⟩
        · exact ⟨hx, fun h => hx' (Or.inr h)⟩
      · rintro ⟨hx, hx'⟩
        by_cases hxk : x=k
        · exact Or.inl hxk
        · exact Or.inr ⟨hx, fun h => h.elim hxk hx'⟩
    rcases List.mem_cons.mp hk' with rfl | hk'
    · -- the head row: all its earlier columns are already final
      set y' := Function.update y k' (rd (b k'-∑ j∈done, L k' j*y j))
      have hfin : ∀ j∉ks, fwd rd L b (insert k' done) y' ks j=y' j :=
        fun j hj => fwd_off rd L b ks _ _ j hj
      simp only [fwd]
      rw [hfin k' hknot]
      have hsum : ∑ j∈S.erase k', L k' j*fwd rd L b (insert k' done) y' ks j=
          ∑ j∈done, L k' j*y j := by
        symm
        apply sum_subset_zero_on_sdiff
        · intro j hj
          rw [hdone] at hj
          have := mem_sdiff.mp hj
          refine mem_erase.mpr ⟨fun h => ?_, this.1⟩
          rw [h] at this
          exact this.2 (by simp)
        · intro j hj
          have hj' := mem_sdiff.mp hj
          by_cases hz : L k' j=0
          · rw [hz, zero_mul]
          · exfalso
            rcases hL k' j hz with h | h
            · exact (ne_of_mem_erase hj'.1) h.symm
            · apply hj'.2
              rw [hdone]
              refine mem_sdiff.mpr ⟨mem_of_mem_erase hj'.1, fun hm => ?_⟩
              simp only [List.toFinset_cons, mem_insert, List.mem_toFinset] at hm
              rcases hm with hm | hm
              · exact (ne_of_mem_erase hj'.1) hm
              · exact lt_asymm h (hsort'.1 j hm)
        · intro j hj
          rw [hdone] at hj
          have hjks : j∉ks := fun h => (mem_sdiff.mp hj).2 (by simp [h])
          have hjk : j≠k' := fun h => (mem_sdiff.mp hj).2 (by simp [h])
          simp only [y', Function.update_of_ne hjk, hfin j hjks]
      rw [hsum]
      simp only [y', Function.update_self]
      have := hrd (b k'-∑ j∈done, L k' j*y j)
      calc |rd (b k'-∑ j∈done, L k' j*y j)+∑ j∈done, L k' j*y j-b k'|
          =|rd (b k'-∑ j∈done, L k' j*y j)-(b k'-∑ j∈done, L k' j*y j)| := by ring_nf
        _≤η := this
    · simp only [fwd]
      exact ih _ _ hsort'.2 (fun x hx => hks x (List.mem_cons_of_mem _ hx)) hdone' k' hk'

/-- Back residual: with an upper factor triangular in the list order (the list
descending), pivots nonzero with `|U k k| ≤ M`, every row is within `M η`. -/
theorem bwd_residual (rd : ℝ → ℝ) (η M : ℝ) (hrd : ∀ x, |rd x-x|≤η) (pos : ι → ℕ)
    (hpos : Function.Injective pos) (U : Matrix ι ι ℝ) (y : ι → ℝ) (S : Finset ι)
    (hU : ∀ k j, U k j≠0 → pos k≤pos j) (hdiag : ∀ k∈S, U k k≠0 ∧ |U k k|≤M) (ks : List ι) :
    ∀ (done : Finset ι) (x : ι → ℝ), ks.Pairwise (fun a b => pos b<pos a) →
      (∀ k∈ks, k∈S) → done=S\ks.toFinset →
      ∀ k∈ks, |∑ j∈S, U k j*bwd rd U y done x ks j-y k|≤M*η := by
  induction ks with
  | nil => intro _ _ _ _ _ k hk; simp at hk
  | cons k ks ih =>
    intro done x hsort hks hdone k' hk'
    have hsort' := List.pairwise_cons.mp hsort
    have hkS := hks k List.mem_cons_self
    have hknot : k∉ks := fun h => (lt_irrefl _ (hsort'.1 k h))
    have hdone' : insert k done=S\ks.toFinset := by
      rw [hdone]
      ext z
      simp only [mem_insert, mem_sdiff, List.mem_toFinset, List.toFinset_cons]
      constructor
      · rintro (rfl | ⟨hz, hz'⟩)
        · exact ⟨hkS, hknot⟩
        · exact ⟨hz, fun h => hz' (Or.inr h)⟩
      · rintro ⟨hz, hz'⟩
        by_cases hzk : z=k
        · exact Or.inl hzk
        · exact Or.inr ⟨hz, fun h => h.elim hzk hz'⟩
    rcases List.mem_cons.mp hk' with rfl | hk'
    · set z := y k'-∑ j∈done, U k' j*x j
      set x' := Function.update x k' (rd (z/U k' k'))
      have hfin : ∀ j∉ks, bwd rd U y (insert k' done) x' ks j=x' j :=
        fun j hj => bwd_off rd U y ks _ _ j hj
      simp only [bwd]
      have hsplit := sum_erase_add S (fun j => U k' j*bwd rd U y (insert k' done) x' ks j) hkS
      have hrest : ∑ j∈S.erase k', U k' j*bwd rd U y (insert k' done) x' ks j=
          ∑ j∈done, U k' j*x j := by
        symm
        apply sum_subset_zero_on_sdiff
        · intro j hj
          rw [hdone] at hj
          have := mem_sdiff.mp hj
          refine mem_erase.mpr ⟨fun h => ?_, this.1⟩
          rw [h] at this
          exact this.2 (by simp)
        · intro j hj
          have hj' := mem_sdiff.mp hj
          by_cases hzr : U k' j=0
          · rw [hzr, zero_mul]
          · exfalso
            have hle := hU k' j hzr
            have hne : pos k'≠pos j := fun h => (ne_of_mem_erase hj'.1) (hpos h).symm
            apply hj'.2
            rw [hdone]
            refine mem_sdiff.mpr ⟨mem_of_mem_erase hj'.1, fun hm => ?_⟩
            simp only [List.toFinset_cons, mem_insert, List.mem_toFinset] at hm
            rcases hm with hm | hm
            · exact (ne_of_mem_erase hj'.1) hm
            · exact absurd (hsort'.1 j hm) (by omega)
        · intro j hj
          rw [hdone] at hj
          have hjks : j∉ks := fun h => (mem_sdiff.mp hj).2 (by simp [h])
          have hjk : j≠k' := fun h => (mem_sdiff.mp hj).2 (by simp [h])
          simp only [x', Function.update_of_ne hjk, hfin j hjks]
      rw [←hsplit, hrest, hfin k' hknot]
      simp only [x', Function.update_self]
      obtain ⟨hd0, hdM⟩ := hdiag k' hkS
      have hr := hrd (z/U k' k')
      have heq : ∑ j∈done, U k' j*x j+U k' k'*rd (z/U k' k')-y k'=
          U k' k'*(rd (z/U k' k')-z/U k' k') := by
        rw [mul_sub, mul_div_cancel₀ _ hd0]
        simp only [z]
        ring
      rw [heq, abs_mul]
      exact mul_le_mul hdM hr (abs_nonneg _) ((abs_nonneg _).trans hdM)
    · simp only [bwd]
      exact ih _ _ hsort'.2 (fun z hz => hks z (List.mem_cons_of_mem _ hz)) hdone' k' hk'

/-- The concrete rounded solve: rounded elimination, then rounded forward and
back substitution with the computed factors. -/
noncomputable def bandSolve (rd : ℝ → ℝ) (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι)
    (b : ι → ℝ) : ι → ℝ :=
  bwd rd (luUr rd A S ks) (fwd rd (luLr rd A S ks) b ∅ (fun _ => 0) ks) ∅ (fun _ => 0) ks.reverse

/-- End-to-end error of the concrete rounded solve of a dominant system. -/
theorem bandSolve_error (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (pos : ι → ℕ) (hpos : Function.Injective pos)
    (A : Matrix ι ι ℝ) (S : Finset ι) (μ m M n : ℝ) (hμ : 0<μ) (hM : 0≤M) (hm0 : 0≤m)
    (hinv : StageInv A S μ m) (hcard : (S.card : ℝ)≤n) (ks : List ι) (hks : ks.toFinset=S)
    (hsort : ks.Pairwise (fun a b => pos a<pos b))
    (hm : m+ks.length*(η*(n+M))≤M) (hmu : μ/2+2*ks.length*(η*(n+M))≤μ)
    (x b : ι → ℝ) (hx : Solves A S x b) (X : ℝ) (hX : 0≤X) (hxX : ∀ j∈S, |x j|≤X)
    (hsmall : n*(ks.length*(η*(1+M)))/μ≤1/2) (j : ι) (hj : j∈S) :
    |bandSolve rd A S ks b j-x j|≤
      2*(((1+ks.length*(2*M/μ+η))*(M*η)+η)/μ+n*(ks.length*(η*(1+M)))/μ*X) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  obtain ⟨-, hU, -⟩ := lur_good rd η hrd μ M n hμ hM hn ks A S μ m hinv hcard hm0 hm hmu
  obtain ⟨hLt, hUt⟩ := fill_support_r rd hrd0 pos (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    ks A S (by rw [hks]) hsort (fun _ _ _ _ _ => trivial)
  have hmem : ∀ k∈ks, k∈S := fun k hk => hks ▸ List.mem_toFinset.mpr hk
  have hdone : (∅ : Finset ι)=S\ks.toFinset := by rw [hks, sdiff_self]; rfl
  have hf := fwd_residual rd η hrd pos (luLr rd A S ks) b S
    (fun i k h => (hLt i k h).imp id And.right) ks ∅ (fun _ => 0) hsort hmem hdone
  have hdiag : ∀ k∈S, luUr rd A S ks k k≠0 ∧ |luUr rd A S ks k k|≤M := by
    intro k hk
    obtain ⟨hd, hmass⟩ := hU k hk
    have h0 : 0≤∑ j∈S.erase k, |luUr rd A S ks k j| := sum_nonneg fun _ _ => abs_nonneg _
    have hpos' : 0<luUr rd A S ks k k := by linarith
    refine ⟨hpos'.ne', ?_⟩
    have := single_le_sum (f := fun j => |luUr rd A S ks k j|) (fun _ _ => abs_nonneg _) hk
    linarith
  have hb := bwd_residual rd η M hrd pos hpos (luUr rd A S ks)
    (fwd rd (luLr rd A S ks) b ∅ (fun _ => 0) ks) S (fun k j h => (hUt k j h).2) hdiag
    ks.reverse ∅ (fun _ => 0) (List.pairwise_reverse.mpr hsort)
    (fun k hk => hmem k (List.mem_reverse.mp hk)) (by rw [List.toFinset_reverse]; exact hdone)
  exact rounded_elimination_solve rd η hrd A S μ m M n hμ hM hm0 hinv hcard ks hm hmu x b
    (bandSolve rd A S ks b) (fwd rd (luLr rd A S ks) b ∅ (fun _ => 0) ks) hx (M*η) X hX hxX
    (fun k hk => hf k (List.mem_toFinset.mp (hks ▸ hk)))
    (fun k hk => hb k (List.mem_reverse.mpr (List.mem_toFinset.mp (hks ▸ hk)))) hsmall j hj

end IntegerMultBounds.NLogN.SchurDominance
