module

public import Mathlib.Tactic

/-! One-step Schur elimination preserves a positive row-dominance margin and
never increases row mass. No symmetry or positive-definiteness is assumed. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- Literal Schur update on the remaining row/column indices. -/
noncomputable def eliminate (A : Matrix ι ι ℝ) (k i j : ι) : ℝ :=
  A i j-A i k/A k k*A k j

/-- Strict diagonal dominance with positive real diagonal. -/
def DominatesOn (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) : Prop :=
  ∀ i∈S, μ+∑ j ∈ S.erase i, |A i j|≤A i i

/-- Eliminating a genuine diagonal pivot preserves the same margin. -/
theorem eliminate_gap (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (k i : ι) (hkS : k∈S) (hiS : i∈S) (hik : i≠k) :
    μ+∑ j ∈ (S.erase i).erase k, |eliminate A k i j|≤eliminate A k i i := by
  have hdiag : 0<A k k := by
    have h := hA k hkS
    have hs : 0≤∑ j ∈ S.erase k, |A k j| := Finset.sum_nonneg (by intros; positivity)
    linarith
  let c := |A i k|/A k k
  have hc : 0≤c := div_nonneg (abs_nonneg _) hdiag.le
  have hc_eq : c*A k k=|A i k| := div_mul_cancel₀ _ hdiag.ne'
  have hsplit_i := Finset.sum_erase_add (S.erase i)
    (fun j => |A i j|) (by simp [hkS, Ne.symm hik] : k∈S.erase i)
  have hsplit_k := Finset.sum_erase_add (S.erase k)
    (fun j => |A k j|) (by simp [hiS, hik] : i∈S.erase k)
  rw [Finset.erase_right_comm] at hsplit_k
  have habs : |A i k/A k k*A k i|=c*|A k i| := by
    simp only [abs_mul, abs_div, abs_of_pos hdiag, c]
  have hdiag_lower : A i i-c*|A k i|≤eliminate A k i i := by
    have h := le_abs_self (A i k/A k k*A k i)
    rw [habs] at h
    dsimp [eliminate]
    linarith
  have hoff : (∑ j ∈ (S.erase i).erase k, |eliminate A k i j|)≤
      (∑ j ∈ (S.erase i).erase k, |A i j|)+
        c*∑ j ∈ (S.erase i).erase k, |A k j| := by
    rw [Finset.mul_sum, ←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    calc |eliminate A k i j|≤|A i j|+|A i k/A k k*A k j| := abs_sub _ _
      _=|A i j|+c*|A k j| := by simp [abs_mul, abs_div, abs_of_pos hdiag, c]
  have hi := hA i hiS
  have hk := hA k hkS
  nlinarith [mul_nonneg hc hμ.le,
    mul_le_mul_of_nonneg_left hk hc]

/-- The total absolute row mass cannot grow through a dominant pivot. -/
theorem eliminate_mass (A : Matrix ι ι ℝ) (S : Finset ι) (k i : ι) (hkS : k∈S)
    (hdiag : 0<A k k)
    (hrow : (∑ j ∈ S.erase k, |A k j|)≤A k k) :
    (∑ j ∈ S.erase k, |eliminate A k i j|)≤∑ j∈S, |A i j| := by
  let c := |A i k|/A k k
  have hc : 0≤c := div_nonneg (abs_nonneg _) hdiag.le
  have hc_eq : c*A k k=|A i k| := div_mul_cancel₀ _ hdiag.ne'
  have hsplit := Finset.sum_erase_add S (fun j => |A i j|)
    hkS
  calc _≤(∑ j ∈ S.erase k, |A i j|)+
        c*∑ j ∈ S.erase k, |A k j| := by
        rw [Finset.mul_sum, ←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro j _
        calc |eliminate A k i j|≤|A i j|+|A i k/A k k*A k j| := abs_sub _ _
          _=|A i j|+c*|A k j| := by simp [abs_mul, abs_div, abs_of_pos hdiag, c]
    _≤(∑ j ∈ S.erase k, |A i j|)+c*A k k :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrow hc)
    _=∑ j∈S, |A i j| := by rw [hc_eq]; exact hsplit

end IntegerMultBounds.NLogN.SchurDominance
