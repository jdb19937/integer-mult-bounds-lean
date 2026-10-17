module

public import IntegerMultBounds.NLogN.SchurSubst
import IntegerMultBounds.NLogN.PhaseCellBoundarySupport
public import IntegerMultBounds.NLogN.PhaseCellMatrix
public import IntegerMultBounds.NLogN.SchurFill
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.Machine

/-! Folded elimination order. Listing a cyclic line as `0, s-1, 1, s-2, …`
turns its cyclic band of half width `w` into an ordinary band of half width
`2w+1`, so ordered elimination creates no border fill: every factor entry
lies within `2w+1` positions of the diagonal in folded order. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset SchurDominance
variable (s t : ℕ) [NeZero s]

/-- Folded position: the first half at even positions, the second half
reversed at odd positions. -/
def foldPos (i : ZMod s) : ℕ := if 2*i.val<s then 2*i.val else 2*(s-1-i.val)+1

/-- The element at folded position `m`. -/
def foldAt (m : ℕ) : ZMod s := if m%2=0 then ((m/2 : ℕ) : ZMod s) else ((s-1-m/2 : ℕ) : ZMod s)

/-- The folded elimination order. -/
def foldOrder : List (ZMod s) := (List.range s).map (foldAt s)

omit [NeZero s] in
theorem foldPos_foldAt (m : ℕ) (hm : m<s) : foldPos s (foldAt s m)=m := by
  unfold foldPos foldAt
  split
  · rename_i he
    rw [ZMod.val_cast_of_lt (by omega)]
    split <;> omega
  · rename_i ho
    rw [ZMod.val_cast_of_lt (by omega)]
    split <;> omega

theorem foldPos_lt (i : ZMod s) : foldPos s i<s := by
  have := ZMod.val_lt i
  unfold foldPos; split <;> omega

theorem foldPos_injective : Function.Injective (foldPos s) := by
  intro a b h
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  apply ZMod.val_injective
  unfold foldPos at h
  split at h <;> split at h <;> omega

omit [NeZero s] in
theorem foldOrder_sorted : (foldOrder s).Pairwise (fun a b => foldPos s a<foldPos s b) := by
  unfold foldOrder
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := s)).imp_of_mem fun {a b} ha hb hab => ?_
  rw [foldPos_foldAt s a (List.mem_range.mp ha), foldPos_foldAt s b (List.mem_range.mp hb)]
  exact hab

theorem foldAt_foldPos (i : ZMod s) : foldAt s (foldPos s i)=i :=
  foldPos_injective s (foldPos_foldAt s _ (foldPos_lt s i))

theorem foldOrder_toFinset : (foldOrder s).toFinset=univ := by
  ext x
  simp only [foldOrder, List.mem_toFinset, List.mem_map, List.mem_range, mem_univ, iff_true]
  exact ⟨foldPos s x, foldPos_lt s x, foldAt_foldPos s x⟩

omit [NeZero s] in
theorem foldOrder_length : (foldOrder s).length=s := by simp [foldOrder]

/-- Ordinary band of half width `B` in folded positions. -/
def FoldRel (B : ℕ) (i j : ZMod s) : Prop := foldPos s i ≤ foldPos s j + B ∧ foldPos s j ≤ foldPos s i + B

omit [NeZero s] in
theorem foldRel_closed (B : ℕ) : FillClosed (foldPos s) (FoldRel s B) := by
  intro k i j hki hkj hik hkj'
  unfold FoldRel at *
  omega

/-- The cyclic band of half width `w` lies in the folded band of half width `2w+1`. -/
theorem bandRel_fold (w : ℕ) (i j : ZMod s) (m : ℤ) (hm : |m|≤w) (hij : i+(m : ZMod s)=j) :
    FoldRel s (2*w+1) i j := by
  have hm' := abs_le.mp hm
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  by_cases hbig : s≤2*w+1
  · have h1 := foldPos_lt s i
    have h2 := foldPos_lt s j
    unfold FoldRel; omega
  have hv : (j.val : ℤ)=((i.val : ℤ)+m)%s := by
    have h2 : j=(((i.val : ℤ)+m : ℤ) : ZMod s) := by
      rw [←hij, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [h2, ZMod.val_intCast]
  have hs : (0 : ℤ)<s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  -- the representative of `i+m` is `i+m`, `i+m+s` or `i+m-s`
  have hcase : (j.val : ℤ)=(i.val : ℤ)+m ∨ (j.val : ℤ)=(i.val : ℤ)+m+s ∨
      (j.val : ℤ)=(i.val : ℤ)+m-s := by
    rcases lt_or_ge ((i.val : ℤ)+m) 0 with hneg | hnn
    · right; left
      rw [hv, Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    · rcases lt_or_ge ((i.val : ℤ)+m) s with hlt | hge
      · left; rw [hv, Int.emod_eq_of_lt hnn hlt]
      · right; right
        rw [hv, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold FoldRel foldPos
  split <;> split <;> omega

theorem matrix_foldRel (p u : ℕ) (i j : ZMod s) (h : realMatrix s t p u i j≠0) :
    FoldRel s (2*PhaseCellBand.width p u+1) i j := by
  obtain ⟨m, hm, hij⟩ := matrix_support s t p u i j h
  exact bandRel_fold s _ i j m hm hij

/-- Every rounded factor entry of the actual matrix in folded order lies within the
folded band `2w+1`; the factors are triangular in folded order. -/
theorem factor_foldRel (p u : ℕ) (rd : ℝ → ℝ) (hrd0 : rd 0=0) :
    (∀ i k, luLr rd (divMul rd) (realMatrix s t p u) univ (foldOrder s) i k≠0 →
      i=k ∨ (FoldRel s (2*PhaseCellBand.width p u+1) i k ∧ foldPos s k<foldPos s i)) ∧
    (∀ k j, luUr rd (divMul rd) (realMatrix s t p u) univ (foldOrder s) k j≠0 →
      FoldRel s (2*PhaseCellBand.width p u+1) k j ∧ foldPos s k≤foldPos s j) :=
  fill_support_r rd (divMul rd) hrd0 (fun b => by simp [divMul, hrd0]) _ _ (foldRel_closed s _) (foldOrder s) _ univ
    (by rw [foldOrder_toFinset]) (foldOrder_sorted s) (fun i _ j _ h => matrix_foldRel s t p u i j h)

end IntegerMultBounds.NLogN.PhaseCellMatrix
