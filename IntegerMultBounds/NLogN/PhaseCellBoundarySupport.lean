module

public import IntegerMultBounds.NLogN.PhaseCellMatrix
public import IntegerMultBounds.NLogN.PhaseCellIntervals
public import IntegerMultBounds.NLogN.SchurSupport

/-! Boundary sparsity for the actual rounded periodic Gaussian matrix. Its
entries lie in the cyclic band of the selected width. A vertex whose whole
band stays inside one phase cell is interior; eliminating interior vertices
in any order leaves only band entries or entries joining one phase cell. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open PhaseCellRow
variable (s t : ℕ) [NeZero s]

theorem window_ne_zero (f : ℤ → ℚ) (w : ℕ) (h : window f w≠0) :
    ∃ m : ℤ, |m|≤w ∧ f m≠0 := by
  by_contra hc
  push Not at hc
  apply h
  have hpos : ∀ n∈Finset.range w, f ((n : ℤ)+1)=0 := fun n hn => hc _ (by
    have := Finset.mem_range.mp hn
    rw [abs_of_nonneg (by positivity)]
    omega)
  have hneg : ∀ n∈Finset.range w, f (-((n : ℤ)+1))=0 := fun n hn => hc _ (by
    have := Finset.mem_range.mp hn
    rw [abs_neg, abs_of_nonneg (by positivity)]
    omega)
  unfold window
  rw [Finset.sum_eq_zero hpos, Finset.sum_eq_zero hneg, hc 0 (by simp)]
  simp

omit [NeZero s] in
/-- Nonzero entries lie in the cyclic band of the selected width. -/
theorem matrix_support (p u : ℕ) (j l : ZMod s) (h : realMatrix s t p u j l≠0) :
    ∃ m : ℤ, |m|≤PhaseCellBand.width p u ∧ j+(m : ZMod s)=l := by
  have hq : matrix s t p u j l≠0 := fun hq => h (by simp [realMatrix, hq])
  obtain ⟨m, hm, hf⟩ := window_ne_zero _ _ hq
  refine ⟨m, hm, ?_⟩
  by_contra hne
  simp [hne] at hf

/-- An interior vertex: its band lies inside the array and inside one cell. -/
def Interior (w : ℕ) (k : ZMod s) : Prop :=
  w≤k.val ∧ k.val+w<s ∧ PhaseCell.phase s t (k.val-w : ℤ)=PhaseCell.phase s t (k.val+w : ℤ)

/-- The phase cell of a physical index. -/
noncomputable def cell (j : ZMod s) : ℤ := PhaseCell.phase s t j.val

private theorem val_of_add (i k : ZMod s) (m : ℤ) (h : i+(m : ZMod s)=k)
    (hlo : 0≤(k.val : ℤ)-m) (hhi : (k.val : ℤ)-m<s) : (i.val : ℤ)=k.val-m := by
  have hi : i=(((k.val : ℤ)-m : ℤ) : ZMod s) := by
    rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, ←h]
    ring
  rw [hi, ZMod.val_intCast, Int.emod_eq_of_lt hlo hhi]

private theorem cell_of_near (hst : s<t) (w : ℕ) (k : ZMod s) (hk : Interior s t w k)
    (i : ZMod s) (m : ℤ) (hm : |m|≤w) (hi : (i.val : ℤ)=k.val-m) : cell s t i=cell s t k := by
  obtain ⟨hlo, hhi, hph⟩ := hk
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hm' := abs_le.mp hm
  unfold cell
  rw [hi, PhaseCellIntervals.phase_eq_of_between hs hst.le (by omega) (by omega) hph]
  exact (PhaseCellIntervals.phase_eq_of_between hs hst.le (by omega) (by omega) hph).symm

/-- Interior vertices couple only within their own phase cell. -/
theorem interior_local (hst : s<t) (p u : ℕ) (k : ZMod s)
    (hk : Interior s t (PhaseCellBand.width p u) k) (i : ZMod s) :
    (realMatrix s t p u i k≠0 → cell s t i=cell s t k) ∧
      (realMatrix s t p u k i≠0 → cell s t i=cell s t k) := by
  have hw := hk
  obtain ⟨hlo, hhi, -⟩ := hw
  constructor
  · intro h
    obtain ⟨m, hm, hik⟩ := matrix_support s t p u i k h
    have hm' := abs_le.mp hm
    exact cell_of_near s t hst _ k hk i m hm
      (val_of_add s i k m hik (by omega) (by omega))
  · intro h
    obtain ⟨m, hm, hki⟩ := matrix_support s t p u k i h
    have hm' := abs_le.mp hm
    have hneg : |-m|≤PhaseCellBand.width p u := by rwa [abs_neg]
    have hik : i+((-m : ℤ) : ZMod s)=k := by rw [←hki]; push_cast; ring
    exact cell_of_near s t hst _ k hk i (-m) hneg
      (val_of_add s i k (-m) hik (by omega) (by omega))

/-- After eliminating any interior vertices, every remaining coupling is a
band entry of the actual matrix or joins two vertices of one phase cell. -/
theorem boundary_support (hst : s<t) (p u : ℕ) (ks : List (ZMod s))
    (hks : ∀ k∈ks, Interior s t (PhaseCellBand.width p u) k) (S : Finset (ZMod s))
    (i j : ZMod s) (h : (SchurDominance.run (realMatrix s t p u) S ks).1 i j≠0) :
    (∃ m : ℤ, |m|≤PhaseCellBand.width p u ∧ i+(m : ZMod s)=j) ∨ cell s t i=cell s t j :=
  (SchurDominance.run_support _ (cell s t) _ (fun k hk => interior_local s t hst p u k hk)
    S ks hks i j h).imp_left (matrix_support s t p u i j)

end IntegerMultBounds.NLogN.PhaseCellMatrix
