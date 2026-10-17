module

public import IntegerMultBounds.NLogN.PhaseCellInteriorRow
public import IntegerMultBounds.NLogN.ToeplitzLocal
public import IntegerMultBounds.NLogN.ToeplitzDominant

/-! Exact interior solves of the actual rounded periodic Gaussian matrix. On a
consecutive interval of interior vertices that contains every active vertex
of its phase cell, every interior solution is the similarity-scaled
Gohberg–Semencul inverse of the shared Toeplitz kernel. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s]

/-- Similarity weight at offset `k` from `lo`. -/
noncomputable def weight (p u : ℕ) (lo : ZMod s) (k : ℕ) : ℝ :=
  (PhaseCellConcreteCoefficients.similarity (2^15*p) s t u (lo+(k : ZMod s)).val : ℝ)

omit [NeZero s] in
theorem val_offset (lo : ZMod s) (L k : ℕ) (hfit : lo.val+L≤s) (hk : k<L) :
    (lo+(k : ZMod s)).val=lo.val+k := by
  have hks : (k : ZMod s).val=k := ZMod.val_cast_of_lt (by omega)
  rw [ZMod.val_add_of_lt (by omega), hks]

theorem cell_solve (hst : s<t) {α d : ℝ} (p u : ℕ) (hp : 0<p) (hu : 1≤u)
    (hαu : α^2=(u : ℝ)) (hθ : 0<(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (x c : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) I x c)
    (lo : ZMod s) (L : ℕ) (hL : 0<L) (hfit : lo.val+L≤s)
    (hint : ∀ k<L, Interior s t (PhaseCellBand.width p u) (lo+(k : ZMod s)) ∧ lo+(k : ZMod s)∈I)
    (hcell : ∀ k<L, cell s t (lo+(k : ZMod s))=cell s t lo)
    (hmax : ∀ j∈I, cell s t j=cell s t lo → ∃ k<L, lo+(k : ZMod s)=j)
    (a : ℕ) (ha : a<L) :
    x (lo+(a : ZMod s))=weight s t p u lo a*
      ∑ k∈range L, ToeplitzInverse.natInv L
        (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u)) a k*
        (c (lo+(k : ZMod s))/weight s t p u lo k) := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hpos (k : ℕ) : 0<weight s t p u lo k := by
    unfold weight
    exact_mod_cast PhaseCellConcreteCoefficients.selected_similarity_pos _ hp hs hαu hθ hgap hbudget
  have hP : 13≤2^15*p := by
    calc 13≤2^15*1 := by norm_num
      _≤2^15*p := Nat.mul_le_mul_left _ hp
  obtain ⟨hinv, -⟩ := PhaseCellToeplitz.block_inverse (w := PhaseCellBand.width p u) hP hs hst.le hu L hL
  refine local_toeplitz _ I x c hx L (fun k => lo+(k : ZMod s)) (fun k hk => (hint k hk).2)
    (fun a' ha' k hk h => ?_) (fun a' ha' j hj hA => ?_) (weight s t p u lo)
    (fun k _ => (hpos k).ne') _ _ hinv (fun a' ha' k hk => ?_) a ha
  · have := congrArg ZMod.val h
    rw [val_offset s lo L a' hfit ha', val_offset s lo L k hfit hk] at this
    omega
  · have hj' := (interior_local s t hst p u _ (hint a' ha').1 j).2 hA
    exact hmax j hj (hj'.trans (hcell a' ha'))
  · rw [interior_row s t hst p u _ _ (hint a' ha').1 (by
        have h := hpos k
        unfold weight at h
        exact_mod_cast h.ne'),
      val_offset s lo L a' hfit ha', val_offset s lo L k hfit hk]
    have hg : ToeplitzInverse.gap (lo.val+a') (lo.val+k)=ToeplitzInverse.gap a' k := by
      unfold ToeplitzInverse.gap
      omega
    rw [hg]
    unfold weight
    rw [val_offset s lo L a' hfit ha', val_offset s lo L k hfit hk]

end IntegerMultBounds.NLogN.PhaseCellMatrix
