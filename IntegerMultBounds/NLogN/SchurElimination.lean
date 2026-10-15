module

public import IntegerMultBounds.NLogN.SchurDominance

/-! Literal successive Schur updates on active vertices, with preserved gap,
nonincreasing row mass and the exact one-step right-hand-side equation. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem pivot_pos (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (k : ι) (hk : k∈S) : 0<A k k := by
  have h := hA k hk
  have hs : 0≤∑ j∈S.erase k, |A k j| := Finset.sum_nonneg (by intros; positivity)
  linarith

theorem eliminate_preserves (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (k : ι) (hk : k∈S) :
    DominatesOn (eliminate A k) (S.erase k) μ := by
  intro i hi
  have h := Finset.mem_erase.mp hi
  rw [Finset.erase_right_comm]
  exact eliminate_gap A S μ hμ hA k i hk h.2 h.1

/-- Repeated updates skip absent or already-eliminated vertices. -/
noncomputable def run (A : Matrix ι ι ℝ) (S : Finset ι) : List ι → Matrix ι ι ℝ × Finset ι
  | [] => (A,S)
  | k::ks => if k∈S then run (eliminate A k) (S.erase k) ks else run A S ks

theorem run_gap (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (ks : List ι) :
    DominatesOn (run A S ks).1 (run A S ks).2 μ := by
  induction ks generalizing A S with
  | nil => exact hA
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [run, ite_eq_left hk]
      exact ih _ _ (eliminate_preserves A S μ hμ hA k hk)
    · simpa only [run, ite_eq_right hk] using ih A S hA

theorem run_mass (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (ks : List ι) (i : ι) :
    (∑ j∈(run A S ks).2, |(run A S ks).1 i j|)≤∑ j∈S, |A i j| := by
  induction ks generalizing A S with
  | nil => exact le_refl _
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [run, ite_eq_left hk]
      have hnext := eliminate_preserves A S μ hμ hA k hk
      have hrow : (∑ j∈S.erase k, |A k j|)≤A k k := by
        have h := hA k hk
        linarith
      exact (ih _ _ hnext).trans (eliminate_mass A S k i hk (pivot_pos A S μ hμ hA k hk) hrow)
    · simpa only [run, ite_eq_right hk] using ih A S hA

/-- The Schur right-hand-side update follows from the actual pivot equation. -/
theorem eliminate_equation (A : Matrix ι ι ℝ) (S : Finset ι) (k i : ι)
    (hk : k∈S) (hdiag : A k k≠0) (x b : ι → ℝ)
    (hi : ∑ j∈S, A i j*x j=b i) (hpivot : ∑ j∈S, A k j*x j=b k) :
    (∑ j∈S.erase k, eliminate A k i j*x j)=b i-A i k/A k k*b k := by
  have hsplit_i := Finset.sum_erase_add S (fun j => A i j*x j) hk
  have hsplit_k := Finset.sum_erase_add S (fun j => A k j*x j) hk
  rw [hi] at hsplit_i
  rw [hpivot] at hsplit_k
  have hdist : (∑ j∈S.erase k, eliminate A k i j*x j)=
      (∑ j∈S.erase k, A i j*x j)-A i k/A k k*(∑ j∈S.erase k, A k j*x j) := by
    rw [Finset.mul_sum, ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [eliminate]
    ring
  rw [hdist]
  have hc : A i k/A k k*A k k=A i k := div_mul_cancel₀ _ hdiag
  have hsi : (∑ j∈S.erase k, A i j*x j)=b i-A i k*x k := by linarith
  have hsk : (∑ j∈S.erase k, A k j*x j)=b k-A k k*x k := by linarith
  rw [hsi, hsk, mul_sub]
  have hcancel : A i k/A k k*(A k k*x k)=A i k*x k := by rw [←mul_assoc, hc]
  rw [hcancel]
  ring

end IntegerMultBounds.NLogN.SchurDominance
