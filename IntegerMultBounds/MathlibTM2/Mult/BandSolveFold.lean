module

public import IntegerMultBounds.MathlibTM2.Mult.BandSolveList
public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0

/-! The banded line solve in folded positions. The machine stores the window
matrix of coefficient numerators `aZ` at folded positions: row `i` and column
`j` of `foldZ` are the vertices `foldAt i` and `foldAt j`. The folded matrix is
banded with half width `2w+1`, and the numerator line solve on it gives, at
folded position `i`, the B̃₀ machine solver `machSolveT` at vertex `foldAt i`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandFactor

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandList

variable (P K : ℕ) (s : ℕ) [NeZero s]

theorem window_eq_zero {E : Type*} [AddCommMonoid E] (f : ℤ → E) (w : ℕ)
    (hf : ∀ k : ℤ, k.natAbs ≤ w → f k=0) : PhaseCellRow.window f w=0 := by
  unfold PhaseCellRow.window
  rw [hf 0 (by simp), Finset.sum_eq_zero fun n hn => hf _ (by have := Finset.mem_range.mp hn; omega),
    Finset.sum_eq_zero fun n hn => hf _ (by have := Finset.mem_range.mp hn; omega)]
  simp

/-- The integer window matrix of coefficient numerators. -/
def wmZ (w : ℕ) (aZ : ZMod s → ℤ → ℤ) (j l : ZMod s) : ℤ :=
  PhaseCellRow.window (fun k => if j+(k : ZMod s)=l then aZ j k else 0) w

theorem wmZ_gv (w : ℕ) (aZ : ZMod s → ℤ → ℤ) (j l : ZMod s) :
    gv P (wmZ s w aZ j l)=windowMatrix s w (fun j k => gv P (aZ j k)) j l := by
  simp only [wmZ, windowMatrix, PhaseCellRow.window, gv]
  push_cast
  simp only [add_div, Finset.sum_div, apply_ite (fun x : ℝ => x/2^P), zero_div]

/-- The folded numerator matrix on natural positions, zero outside `s × s`. -/
def foldZ (w : ℕ) (aZ : ZMod s → ℤ → ℤ) (i j : ℕ) : ℤ :=
  if i<s ∧ j<s then wmZ s w aZ (foldAt s i) (foldAt s j) else 0

theorem foldZ_band (w : ℕ) (aZ : ZMod s → ℤ → ℤ) :
    BandFrom (2*w+1) (gvM P (foldZ s w aZ)) 0 := by
  intro i j _ _ h
  have hz : foldZ s w aZ i j≠0 := fun h0 => h (by simp [gvM, h0, gv_zero])
  unfold foldZ at hz
  split at hz
  · rename_i hij
    obtain ⟨k, hk, hkz⟩ : ∃ k : ℤ, k.natAbs ≤ w ∧
        (if foldAt s i+(k : ZMod s)=foldAt s j then aZ (foldAt s i) k else 0)≠0 := by
      by_contra hall
      push_neg at hall
      exact hz (window_eq_zero _ w hall)
    have heq : foldAt s i+(k : ZMod s)=foldAt s j := by
      by_contra hne; simp [hne] at hkz
    have hr := bandRel_fold s w (foldAt s i) (foldAt s j) k (by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hk) heq
    unfold FoldRel at hr
    rw [foldPos_foldAt s i hij.1, foldPos_foldAt s j hij.2] at hr
    omega
  · exact absurd rfl hz

theorem image_foldPos : (Finset.univ : Finset (ZMod s)).image (foldPos s)=Finset.Ico 0 s := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ico, Nat.zero_le]
  constructor
  · rintro ⟨a, rfl⟩; exact foldPos_lt s a
  · intro hx; exact ⟨foldAt s x, foldPos_foldAt s x hx⟩

theorem foldOrder_map_foldPos : (foldOrder s).map (foldPos s)=List.range' 0 s := by
  rw [foldOrder, List.map_map, List.range_eq_range']
  conv_rhs => rw [← List.map_id (List.range' 0 s)]
  refine List.map_congr_left fun m hm => ?_
  exact foldPos_foldAt s m (by have := List.mem_range'_1.mp hm; omega)

/-- The numerator line solve on the folded matrix is the B̃₀ machine solver, read
in folded positions. -/
theorem lineSolveFold_eq (hP : 2 ≤ P) (w : ℕ) (aZ : ZMod s → ℤ → ℤ) (bZ : List ℤ)
    (hlen : bZ.length=s) :
    (lineSolveZ P K (2*w+1) s (foldZ s w aZ) bZ).map (gv P)=(List.range' 0 s).map fun i =>
      FastB0.machSolveT K (rdP P) (windowMatrix s w fun j k => gv P (aZ j k))
        (fun a => gv P (bZ.getD (foldPos s a) 0)) (foldAt s i) := by
  rw [lineSolveZ_eq P K (2*w+1) s hP (foldZ s w aZ) (foldZ_band P s w aZ)
    (fun i j h => by unfold foldZ; rw [if_neg (by omega)]) bZ hlen]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i<s := by have := List.mem_range'_1.mp hi; omega
  have hmap := bandSolveG_map (rdP P) (mRule P K) (foldPos s) (foldPos_injective s)
    (fun c => NewtonRecip.newtonR (rdP P) c K) (windowMatrix s w fun j k => gv P (aZ j k))
    (gvM P (foldZ s w aZ)) (fun a c => by
      simp only [gvM, foldZ, foldPos_lt, and_self, ite_true, foldAt_foldPos]
      exact wmZ_gv P s w aZ a c)
    Finset.univ (foldOrder s) (fun a => gv P (bZ.getD (foldPos s a) 0))
    (fun i => gv P (bZ.getD i 0)) (fun _ => rfl) (foldAt s i)
  rw [image_foldPos, foldOrder_map_foldPos, foldPos_foldAt s i hi'] at hmap
  exact hmap

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
