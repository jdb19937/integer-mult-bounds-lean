module

public import IntegerMultBounds.NLogN.PhaseCellRoundedSchur
import IntegerMultBounds.NLogN.PhaseCellIntervals
import Mathlib.Data.List.GetD
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.Machine

/-! # The folded boundary order

The boundary system of the phase-cell solve is a cyclic band in boundary rank order: every
coupling joins ranks at cyclic distance at most `4w` (`schur_cycRel`), the wrap-around entries
joining the first and last ranks. Listing the ranks as `0, n-1, 1, n-2, …` (`bFoldOrder`, the fold
of `PhaseCellFold` on the `n` boundary ranks) turns a cyclic band of half width `D` into an
ordinary band of half width `2D + 1` in folded position (`cycRel_foldBRel`), which is closed
under fill (`foldBRel_closed`). So the rounded factors of a boundary matrix supported in that
band stay in it (`boundary_factors_fold`), in the format of the banded line. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset SchurDominance
variable (s t : ℕ) [NeZero s]

/-! ### Ranks and positions -/

theorem bRank_le_val (B : Finset (ZMod s)) (i : ZMod s) : bRank s B i ≤ i.val := by
  have h := card_filter_interval B 0 i.val
  unfold bRank
  simpa using h

/-- The vertex of rank `r`. -/
def rankAt (B : Finset (ZMod s)) (r : ℕ) : ZMod s := (bOrder s B).getD r 0

omit [NeZero s] in
theorem bOrder_nodup (B : Finset (ZMod s)) : (bOrder s B).Nodup :=
  (bOrder_val_sorted s B).imp fun h => ne_of_apply_ne ZMod.val (ne_of_lt h)

theorem bRank_getElem (B : Finset (ZMod s)) (r : ℕ) (hr : r<(bOrder s B).length) :
    bRank s B (bOrder s B)[r]=r := by
  have hs := bOrder_val_sorted s B
  have hnd := bOrder_nodup s B
  have hlt : ∀ (i j : ℕ) (hi : i<(bOrder s B).length) (hj : j<(bOrder s B).length),
      (bOrder s B)[i].val<(bOrder s B)[j].val ↔ i<j := by
    intro i j hi hj
    constructor
    · intro h
      by_contra hji
      rcases (not_lt.mp hji).lt_or_eq with h' | h'
      · have := List.pairwise_iff_getElem.mp hs j i hj hi h'
        omega
      · subst h'; omega
    · exact fun h => List.pairwise_iff_getElem.mp hs i j hi hj h
  unfold bRank
  have himg : (B.filter fun k : ZMod s => ZMod.val k<ZMod.val (bOrder s B)[r])=
      (range r).image fun i => (bOrder s B).getD i 0 := by
    ext k
    simp only [mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨hkB, hk⟩
      have hkl : k∈bOrder s B := by rw [←List.mem_toFinset, bOrder_toFinset]; exact hkB
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkl
      exact ⟨i, (hlt i r hi hr).mp hk, by rw [List.getD_eq_getElem _ _ hi]⟩
    · rintro ⟨i, hir, rfl⟩
      have hi : i<(bOrder s B).length := by omega
      rw [List.getD_eq_getElem _ _ hi]
      refine ⟨?_, (hlt i r hi hr).mpr hir⟩
      have hmem : (bOrder s B)[i]∈bOrder s B := List.getElem_mem hi
      rwa [←List.mem_toFinset, bOrder_toFinset] at hmem
  rw [himg, card_image_of_injOn, card_range]
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  dsimp only at hij
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hij
  exact (List.Nodup.getElem_inj_iff hnd).mp hij

theorem bRank_rankAt (B : Finset (ZMod s)) (r : ℕ) (hr : r<B.card) :
    bRank s B (rankAt s B r)=r := by
  have hr' : r<(bOrder s B).length := by rw [bOrder_length]; exact hr
  rw [rankAt, List.getD_eq_getElem _ _ hr']
  exact bRank_getElem s B r hr'

theorem rankAt_mem (B : Finset (ZMod s)) (r : ℕ) (hr : r<B.card) : rankAt s B r∈B := by
  have hr' : r<(bOrder s B).length := by rw [bOrder_length]; exact hr
  have hmem : (bOrder s B)[r]∈bOrder s B := List.getElem_mem hr'
  rw [rankAt, List.getD_eq_getElem _ _ hr']
  rwa [←List.mem_toFinset, bOrder_toFinset] at hmem

theorem bRank_injOn (B : Finset (ZMod s)) {i j : ZMod s} (hi : i∈B) (hj : j∈B)
    (h : bRank s B i=bRank s B j) : i=j := by
  apply ZMod.val_injective
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · have := bRank_strictMono (B := B) hi hlt; omega
  · exact heq
  · have := bRank_strictMono (B := B) hj hgt; omega

theorem rankAt_bRank (B : Finset (ZMod s)) (x : ZMod s) (hx : x∈B) :
    rankAt s B (bRank s B x)=x :=
  bRank_injOn s B (rankAt_mem s B _ (bRank_lt hx)) hx (bRank_rankAt s B _ (bRank_lt hx))

/-! ### The cyclic rank band -/

/-- Ranks at cyclic distance at most `D` among the `|B|` boundary ranks. -/
def CycRel (B : Finset (ZMod s)) (D : ℕ) (i j : ZMod s) : Prop :=
  (bRank s B i≤bRank s B j+D ∧ bRank s B j≤bRank s B i+D) ∨
    bRank s B i+B.card≤bRank s B j+D ∨ bRank s B j+B.card≤bRank s B i+D

instance (B : Finset (ZMod s)) (D : ℕ) (i j : ZMod s) : Decidable (CycRel s B D i j) := by
  unfold CycRel; infer_instance

omit [NeZero s] in
theorem cycRel_mono (B : Finset (ZMod s)) {D D' : ℕ} (hD : D≤D') {i j : ZMod s}
    (h : CycRel s B D i j) : CycRel s B D' i j := by
  unfold CycRel at *
  omega

/-- A band entry joins ranks at cyclic distance at most `w`. -/
theorem band_cycRel (B : Finset (ZMod s)) (w : ℕ) (i j : ZMod s) (m : ℤ) (hm : |m|≤w)
    (hij : i+(m : ZMod s)=j) : CycRel s B w i j := by
  have hBs : B.card≤s := by
    have := Finset.card_le_univ B
    rwa [ZMod.card] at this
  have hri : bRank s B i≤B.card := card_le_card (filter_subset _ _)
  have hrj : bRank s B j≤B.card := card_le_card (filter_subset _ _)
  by_cases hbig : s≤w
  · unfold CycRel; omega
  have hm' := abs_le.mp hm
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have hs : (0 : ℤ)<s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hv : (j.val : ℤ)=((i.val : ℤ)+m)%s := by
    have h2 : j=(((i.val : ℤ)+m : ℤ) : ZMod s) := by
      rw [←hij, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [h2, ZMod.val_intCast]
  have hcase : (j.val : ℤ)=(i.val : ℤ)+m ∨ (j.val : ℤ)=(i.val : ℤ)+m+s ∨
      (j.val : ℤ)=(i.val : ℤ)+m-s := by
    rcases lt_or_ge ((i.val : ℤ)+m) 0 with hneg | hnn
    · right; left
      rw [hv, Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    · rcases lt_or_ge ((i.val : ℤ)+m) s with hlt | hge
      · left; rw [hv, Int.emod_eq_of_lt hnn hlt]
      · right; right
        rw [hv, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  have htop (x : ZMod s) : (B.filter fun k => x.val≤k.val).card≤s-x.val := by
    have := card_filter_interval B x.val s
    refine le_trans (card_le_card fun k hk => ?_) this
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2, ZMod.val_lt k⟩
  unfold CycRel
  rcases hcase with h | h | h
  · rcases le_total i.val j.val with hle | hle
    · have e := bRank_sub (B := B) hle
      have hc := card_filter_interval B i.val j.val
      left; omega
    · have e := bRank_sub (B := B) hle
      have hc := card_filter_interval B j.val i.val
      left; omega
  · -- `i` near `0`, `j` near the end
    have e := bRank_top (B := B) j
    have hc := htop j
    have hl := bRank_le_val s B i
    right; left; omega
  · -- `i` near the end, `j` near `0`
    have e := bRank_top (B := B) i
    have hc := htop i
    have hl := bRank_le_val s B j
    right; right; omega

/-- A same-cell entry joins boundary ranks at distance at most `4w`. -/
theorem cell_cycRel (hst : s<t) (w : ℕ) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t w j) (i j : ZMod s) (hc : cell s t i=cell s t j) :
    CycRel s (univ\I) (4*w) i j := by
  unfold CycRel
  left
  rcases le_total i.val j.val with hle | hle
  · have e := bRank_sub (B := univ\I) hle
    have hb := same_cell_interval s t hst w I hI i j hc
    omega
  · have e := bRank_sub (B := univ\I) hle
    have hb := same_cell_interval s t hst w I hI j i hc.symm
    omega

/-- **The boundary system is a cyclic rank band.** After eliminating interior vertices, every
coupling between boundary vertices joins ranks at cyclic distance at most `4w`. -/
theorem schur_cycRel (hst : s<t) (p u : ℕ) (ks : List (ZMod s))
    (hks : ∀ k∈ks, Interior s t (PhaseCellBand.width p u) k) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j) (i j : ZMod s)
    (h : (run (realMatrix s t p u) univ ks).1 i j≠0) :
    CycRel s (univ\I) (4*PhaseCellBand.width p u) i j := by
  rcases boundary_support s t hst p u ks hks univ i j h with ⟨m, hm, hij⟩ | hc
  · exact cycRel_mono s _ (by omega) (band_cycRel s _ _ i j m hm hij)
  · exact cell_cycRel s t hst _ I hI i j hc

/-! ### The fold -/

/-- Folded boundary position: ranks of the first half at even positions, the second half
reversed at odd positions; vertices outside `B` after all of them. -/
def bFoldPos (B : Finset (ZMod s)) (x : ZMod s) : ℕ :=
  if x∈B then (if 2*bRank s B x<B.card then 2*bRank s B x else 2*(B.card-1-bRank s B x)+1)
  else B.card+x.val

/-- The vertex at folded position `m`. -/
def bFoldAt (B : Finset (ZMod s)) (m : ℕ) : ZMod s :=
  rankAt s B (if m%2=0 then m/2 else B.card-1-m/2)

/-- The folded boundary order. -/
def bFoldOrder (B : Finset (ZMod s)) : List (ZMod s) := (List.range B.card).map (bFoldAt s B)

omit [NeZero s] in
theorem bFoldPos_lt (B : Finset (ZMod s)) (x : ZMod s) (hx : x∈B) : bFoldPos s B x<B.card := by
  have := bRank_lt hx
  unfold bFoldPos
  simp only [hx, ite_true]
  split <;> omega

theorem bFoldPos_injective (B : Finset (ZMod s)) : Function.Injective (bFoldPos s B) := by
  intro a b h
  unfold bFoldPos at h
  by_cases ha : a∈B <;> by_cases hb : b∈B <;> simp only [ha, hb, ite_true, ite_false] at h
  · have h1 := bRank_lt ha
    have h2 := bRank_lt hb
    refine bRank_injOn s B ha hb ?_
    split at h <;> split at h <;> omega
  · have := bRank_lt ha; split at h <;> omega
  · have := bRank_lt hb; split at h <;> omega
  · exact ZMod.val_injective s (by omega)

theorem bFoldPos_bFoldAt (B : Finset (ZMod s)) (m : ℕ) (hm : m<B.card) :
    bFoldPos s B (bFoldAt s B m)=m := by
  have hr : (if m%2=0 then m/2 else B.card-1-m/2)<B.card := by split <;> omega
  have hmem := rankAt_mem s B _ hr
  have hrk := bRank_rankAt s B _ hr
  unfold bFoldPos bFoldAt
  simp only [hmem, ite_true]
  rw [hrk]
  split <;> split <;> omega

theorem bFoldAt_mem (B : Finset (ZMod s)) (m : ℕ) (hm : m<B.card) : bFoldAt s B m∈B :=
  rankAt_mem s B _ (by split <;> omega)

theorem bFoldAt_bFoldPos (B : Finset (ZMod s)) (x : ZMod s) (hx : x∈B) :
    bFoldAt s B (bFoldPos s B x)=x :=
  bFoldPos_injective s B (bFoldPos_bFoldAt s B _ (bFoldPos_lt s B x hx))

theorem bFoldOrder_sorted (B : Finset (ZMod s)) :
    (bFoldOrder s B).Pairwise fun a b => bFoldPos s B a<bFoldPos s B b := by
  unfold bFoldOrder
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := B.card)).imp_of_mem fun {a b} ha hb hab => ?_
  rw [bFoldPos_bFoldAt s B a (List.mem_range.mp ha), bFoldPos_bFoldAt s B b (List.mem_range.mp hb)]
  exact hab

theorem bFoldOrder_toFinset (B : Finset (ZMod s)) : (bFoldOrder s B).toFinset=B := by
  ext x
  simp only [bFoldOrder, List.mem_toFinset, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact bFoldAt_mem s B m hm
  · intro hx; exact ⟨bFoldPos s B x, bFoldPos_lt s B x hx, bFoldAt_bFoldPos s B x hx⟩

omit [NeZero s] in
theorem bFoldOrder_length (B : Finset (ZMod s)) : (bFoldOrder s B).length=B.card := by
  simp [bFoldOrder]

/-- Ordinary band of half width `W` in folded boundary positions. -/
def FoldBRel (B : Finset (ZMod s)) (W : ℕ) (i j : ZMod s) : Prop :=
  bFoldPos s B i≤bFoldPos s B j+W ∧ bFoldPos s B j≤bFoldPos s B i+W

instance (B : Finset (ZMod s)) (W : ℕ) (i j : ZMod s) : Decidable (FoldBRel s B W i j) := by
  unfold FoldBRel; infer_instance

omit [NeZero s] in
theorem foldBRel_closed (B : Finset (ZMod s)) (W : ℕ) :
    FillClosed (bFoldPos s B) (FoldBRel s B W) := by
  intro k i j hki hkj hik hkj'
  unfold FoldBRel at *
  omega

omit [NeZero s] in
/-- The fold turns a cyclic band of half width `D` into an ordinary band of half width
`2D + 1`. -/
theorem cycRel_foldBRel (B : Finset (ZMod s)) (D : ℕ) {i j : ZMod s} (hi : i∈B) (hj : j∈B)
    (h : CycRel s B D i j) : FoldBRel s B (2*D+1) i j := by
  have h1 := bRank_lt hi
  have h2 := bRank_lt hj
  unfold CycRel at h
  unfold FoldBRel bFoldPos
  simp only [hi, hj, ite_true]
  split <;> split <;> omega

/-- Rounded factors of a boundary matrix supported in the folded band stay in it, triangular in
the folded position. -/
theorem boundary_factors_fold (B : Finset (ZMod s)) (W : ℕ) (Sh : Matrix (ZMod s) (ZMod s) ℝ)
    (hSh : ∀ i∈B, ∀ j∈B, Sh i j≠0 → FoldBRel s B W i j)
    (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (hrd0 : rd 0=0) (hmul0 : ∀ b, mul 0 b=0) :
    (∀ i k, luLr rd mul Sh B (bFoldOrder s B) i k≠0 →
      i=k ∨ (FoldBRel s B W i k ∧ bFoldPos s B k<bFoldPos s B i)) ∧
    (∀ k j, luUr rd mul Sh B (bFoldOrder s B) k j≠0 →
      FoldBRel s B W k j ∧ bFoldPos s B k≤bFoldPos s B j) :=
  fill_support_r rd mul hrd0 hmul0 _ _ (foldBRel_closed s _ _) _ _ _
    (by rw [bFoldOrder_toFinset]) (bFoldOrder_sorted s _) hSh

end IntegerMultBounds.NLogN.PhaseCellMatrix
