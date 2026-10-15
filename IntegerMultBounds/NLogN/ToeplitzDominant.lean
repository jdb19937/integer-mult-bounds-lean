module

public import IntegerMultBounds.NLogN.ToeplitzInverse
public import IntegerMultBounds.NLogN.SchurSolve
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A symmetric Toeplitz matrix with unit diagonal and off-diagonal row mass
`ρ<1` has an actual two-sided inverse. Its rows have absolute sum at most
`1/(1-ρ)`, and its corner satisfies `x₀ ≥ 1-ρ/(1-ρ)`, so for `ρ<1/2` the
Gohberg–Semencul factorization applies. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.ToeplitzInverse

open scoped BigOperators
open Finset

/-- Off-diagonal absolute row mass of the Toeplitz matrix of size `L`. -/
def RowMass (L : ℕ) (g : ℕ → ℝ) (ρ : ℝ) : Prop :=
  ∀ i<L, ∑ k∈(range L).erase i, |g (gap i k)|≤ρ

/-- The Toeplitz matrix with natural indices. -/
def natMatrix (g : ℕ → ℝ) : Matrix ℕ ℕ ℝ := fun i k => g (gap i k)

/-- The same matrix on `Fin L`. -/
def finMatrix (L : ℕ) (g : ℕ → ℝ) : Matrix (Fin L) (Fin L) ℝ := fun i k => g (gap i k)

/-- The natural-indexed inverse, zero outside `range L`. -/
noncomputable def natInv (L : ℕ) (g : ℕ → ℝ) : ℕ → ℕ → ℝ := fun i j =>
  if h : i<L ∧ j<L then (finMatrix L g)⁻¹ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

variable {L : ℕ} {g : ℕ → ℝ} {ρ : ℝ}

theorem gap_self (i : ℕ) : gap i i=0 := by
  unfold gap
  omega

/-- Each distance occurs at most twice in a row, once on each side. -/
theorem rowMass_of_sum (σ : ℝ) (hσ : ∑ δ∈Ico 1 L, |g δ|≤σ) : RowMass L g (2*σ) := by
  intro i hi
  have part (P : ℕ → Prop) [DecidablePred P]
      (hinj : Set.InjOn (gap i) ↑(((range L).erase i).filter P)) :
      ∑ k∈((range L).erase i).filter P, |g (gap i k)|≤σ := by
    rw [←sum_image (f := fun δ => |g δ|) hinj]
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _) hσ
    intro δ hδ
    simp only [mem_image, mem_filter, mem_erase, mem_range] at hδ
    obtain ⟨k, ⟨⟨hki, hkL⟩, _⟩, rfl⟩ := hδ
    rw [mem_Ico]
    unfold gap
    omega
  rw [←sum_filter_add_sum_filter_not _ (fun k : ℕ => k < i), two_mul]
  refine add_le_add (part _ ?_) (part _ ?_) <;>
  · intro a ha b hb hab
    simp only [coe_filter, mem_erase, mem_range, Set.mem_ofPred_eq] at ha hb
    unfold gap at hab
    omega

theorem dominates (hg : g 0=1) (hρ : RowMass L g ρ) :
    SchurDominance.DominatesOn (natMatrix g) (range L) (1-ρ) := by
  intro i hi
  have h := hρ i (mem_range.mp hi)
  simp only [natMatrix, gap_self, hg]
  linarith

private def extend (v : Fin L → ℝ) (k : ℕ) : ℝ := if h : k<L then v ⟨k, h⟩ else 0

private theorem mulVec_extend (v : Fin L → ℝ) (i : Fin L) :
    Matrix.mulVec (finMatrix L g) v i=∑ k∈range L, natMatrix g i k*extend v k := by
  rw [←Fin.sum_univ_eq_sum_range (fun k => natMatrix g i k*extend v k) L]
  simp only [Matrix.mulVec, dotProduct]
  exact Fintype.sum_congr _ _ fun k => by simp [finMatrix, natMatrix, extend, k.isLt]

theorem isUnit_det (hg : g 0=1) (hρ : RowMass L g ρ) (hρ1 : ρ<1) :
    IsUnit (finMatrix L g).det := by
  rw [←Matrix.isUnit_iff_isUnit_det, ←Matrix.mulVec_injective_iff_isUnit]
  intro v v' hvv
  funext i
  have hsol (w : Fin L → ℝ) :
      SchurDominance.Solves (natMatrix g) (range L) (extend w)
        (extend (Matrix.mulVec (finMatrix L g) w)) := by
    intro l hl
    have hl' := mem_range.mp hl
    rw [show extend (Matrix.mulVec (finMatrix L g) w) l=
      Matrix.mulVec (finMatrix L g) w ⟨l, hl'⟩ by simp [extend, hl'], mulVec_extend]
  have h := SchurDominance.solves_unique _ _ _ (by linarith) (dominates hg hρ)
    (extend v) (extend v') _ (hsol v) (hvv ▸ hsol v') i (mem_range.mpr i.isLt)
  simpa [extend, i.isLt] using h

theorem isInverse (hg : g 0=1) (hρ : RowMass L g ρ) (hρ1 : ρ<1) :
    IsInverse L g (natInv L g) := by
  have hdet := isUnit_det hg hρ hρ1
  refine ⟨fun i j hij => ?_, fun i j hi hj => ?_, fun i j hi hj => ?_⟩
  · simp only [natInv]
    split
    · exfalso
      omega
    · rfl
  · have h := congrFun (congrFun (Matrix.mul_nonsing_inv _ hdet) ⟨i, hi⟩) ⟨j, hj⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [←Fin.sum_univ_eq_sum_range (fun k => g (gap i k)*natInv L g k j) L]
    simpa only [natInv, finMatrix, Fin.is_lt, hj, and_self, ↓reduceDIte, Fin.eta,
      Fin.mk.injEq] using h
  · have h := congrFun (congrFun (Matrix.nonsing_inv_mul _ hdet) ⟨i, hi⟩) ⟨j, hj⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [←Fin.sum_univ_eq_sum_range (fun k => natInv L g i k*g (gap k j)) L]
    simpa only [natInv, finMatrix, Fin.is_lt, hi, and_self, ↓reduceDIte, Fin.eta,
      Fin.mk.injEq] using h

/-- Every row of the inverse has absolute sum at most `1/(1-ρ)`. -/
theorem row_abs_sum (hg : g 0=1) (hρ : RowMass L g ρ) (hρ1 : ρ<1) (i : ℕ) (hi : i<L) :
    ∑ j∈range L, |natInv L g i j|≤1/(1-ρ) := by
  have h := isInverse hg hρ hρ1
  set b : ℕ → ℝ := fun j => if 0≤natInv L g i j then 1 else -1 with hb
  set y : ℕ → ℝ := fun k => ∑ j∈range L, natInv L g k j*b j with hy
  have hsol : SchurDominance.Solves (natMatrix g) (range L) y b := by
    intro l hl
    simp only [hy, natMatrix, mul_sum]
    rw [sum_comm]
    simp_rw [←mul_assoc, ←sum_mul]
    rw [sum_congr rfl fun j hj => by
      rw [h.right l j (mem_range.mp hl) (mem_range.mp hj)]]
    simp [hl]
  have hbound := SchurDominance.solves_bound _ _ _ (by linarith) (dominates hg hρ) y b hsol 1
    (fun j _ => by simp only [hb]; split <;> simp) i (mem_range.mpr hi)
  have hyi : y i=∑ j∈range L, |natInv L g i j| := by
    simp only [hy, hb]
    refine sum_congr rfl fun j _ => ?_
    split
    · rw [abs_of_nonneg ‹_›, mul_one]
    · rw [abs_of_neg (not_le.mp ‹_›), mul_neg_one]
  rw [←hyi]
  exact (le_abs_self _).trans hbound

/-- The corner of the inverse stays close to one. -/
theorem corner_lower (hg : g 0=1) (hρ : RowMass L g ρ) (hρ1 : ρ<1) (hL : 0<L) :
    1-ρ/(1-ρ)≤natInv L g 0 0 := by
  have h := isInverse hg hρ hρ1
  have hμ : 0<1-ρ := by linarith
  have hrow := h.right 0 0 hL hL
  simp only [ite_true] at hrow
  have hsplit := sum_erase_add (range L) (fun k => g (gap 0 k)*natInv L g k 0)
    (mem_range.mpr hL)
  rw [hrow] at hsplit
  simp only [gap_self, hg, one_mul] at hsplit
  have hcol : ∀ k∈range L, |natInv L g k 0|≤1/(1-ρ) := by
    intro k hk
    have := row_abs_sum hg hρ hρ1 0 hL
    rw [symm h 0 k]
    exact (single_le_sum (f := fun j => |natInv L g 0 j|) (fun _ _ => abs_nonneg _) hk).trans this
  have hoff : |∑ k∈(range L).erase 0, g (gap 0 k)*natInv L g k 0|≤ρ/(1-ρ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _≤∑ k∈(range L).erase 0, |g (gap 0 k)| * (1/(1-ρ)) := by
          refine sum_le_sum fun k hk => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hcol k (mem_of_mem_erase hk)) (abs_nonneg _)
      _≤ρ*(1/(1-ρ)) := by
          rw [←sum_mul]
          exact mul_le_mul_of_nonneg_right (hρ 0 hL) (by positivity)
      _=ρ/(1-ρ) := by ring
  have := le_abs_self (∑ k∈(range L).erase 0, g (gap 0 k)*natInv L g k 0)
  linarith

/-- Gohberg–Semencul for every dominant symmetric Toeplitz block with
`ρ ≤ 1/8`: the corner is at least `6/7`. -/
theorem selected (hg : g 0=1) (hρ : RowMass L g ρ) (hρ8 : ρ≤1/8) (hL : 0<L) :
    6/7≤natInv L g 0 0 ∧ ∀ i j, i<L → j<L →
      natInv L g 0 0*natInv L g i j=∑ k∈range (min i j+1),
        (col (natInv L g) (i-min i j+k)*col (natInv L g) (j-min i j+k)-
          rev L (natInv L g) (i-min i j+k)*rev L (natInv L g) (j-min i j+k)) := by
  have hρ1 : ρ<1 := by linarith
  have hμ : 0<1-ρ := by linarith
  refine ⟨?_, fun i j hi hj => entry (isInverse hg hρ hρ1) ?_ i j hi hj⟩
  · have hc := corner_lower hg hρ hρ1 hL
    have hq : ρ/(1-ρ)≤1/7 := by
      rw [div_le_iff₀ hμ]
      linarith
    linarith
  · have hc := corner_lower hg hρ hρ1 hL
    have hq : ρ/(1-ρ)≤1/7 := by
      rw [div_le_iff₀ hμ]
      linarith
    intro h0
    linarith

end IntegerMultBounds.NLogN.ToeplitzInverse
