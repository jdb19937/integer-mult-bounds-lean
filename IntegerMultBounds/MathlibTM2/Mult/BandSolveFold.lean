module

public import IntegerMultBounds.MathlibTM2.Mult.BandSolveList
public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0
public import IntegerMultBounds.NLogN.PhaseCellInteriorRow

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
      push Not at hall
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
    (fun i j h => by unfold foldZ; rw [ite_eq_right (by omega)]) bZ hlen]
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

/-- The forward residue of `l - j`. -/
def fdist (j l : ZMod s) : ℕ := (l.val+s-j.val) % s

theorem cast_fdist (j l : ZMod s) : j+((fdist s j l : ℕ) : ZMod s)=l := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hj := ZMod.val_lt j
  unfold fdist
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  ring

theorem fdist_unique (j l : ZMod s) (k : ℤ) (h : j+(k : ZMod s)=l) :
    ((fdist s j l : ℕ) : ℤ) ≡ k [ZMOD s] := by
  have h2 := (cast_fdist s j l).trans h.symm
  have h3 : ((fdist s j l : ℕ) : ZMod s)=(k : ZMod s) := add_left_cancel h2
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  exact h3

/-- When the line is longer than the band, a window entry is the single coefficient at
the centered residue. -/
theorem wmZ_single (w : ℕ) (hsw : 2*w+1 < s) (aZ : ZMod s → ℤ → ℤ) (j l : ZMod s) :
    wmZ s w aZ j l=if fdist s j l ≤ w then aZ j (fdist s j l)
      else if s-w ≤ fdist s j l then aZ j ((fdist s j l : ℤ)-s) else 0 := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hd : fdist s j l < s := Nat.mod_lt _ hs
  set d := fdist s j l with hddef
  -- the indicator of `j + k = l` on the window is the indicator of `k ≡ d`
  have hind : ∀ k : ℤ, k.natAbs ≤ w → (j+(k : ZMod s)=l ↔ k=(if d ≤ w then (d : ℤ) else (d : ℤ)-s)) := by
    intro k hk
    constructor
    · intro h
      have hm := fdist_unique s j l k h
      rw [← hddef] at hm
      obtain ⟨q, hq⟩ := Int.ModEq.dvd hm.symm
      have hkb : -(w : ℤ) ≤ k ∧ k ≤ w := by omega
      have : -(s : ℤ) < (d : ℤ)-k ∧ (d : ℤ)-k < 2*s := by omega
      have hq' : (d : ℤ)-k=s*q := by linarith
      have hq0 : q=0 ∨ q=1 := by
        rcases lt_trichotomy q 0 with h | h | h
        · nlinarith
        · left; exact h
        · have : q ≤ 1 := by nlinarith
          right; omega
      split_ifs with hdw
      · rcases hq0 with rfl | rfl
        · linarith
        · omega
      · rcases hq0 with rfl | rfl
        · omega
        · linarith
    · intro h
      rw [h]
      split_ifs
      · simpa [hddef] using cast_fdist s j l
      · push_cast; rw [ZMod.natCast_self, sub_zero]; simpa [hddef] using cast_fdist s j l
  set k0 : ℤ := if d ≤ w then (d : ℤ) else (d : ℤ)-s with hk0
  rw [wmZ, NLogN.PhaseCellMatrix.window_eq_Icc]
  rw [Finset.sum_congr rfl (g := fun k => if k=k0 then aZ j k else 0) (fun k hk => by
    have hk' := Finset.mem_Icc.mp hk
    have hka : k.natAbs ≤ w := by omega
    by_cases hc : j+(k : ZMod s)=l
    · rw [ite_eq_left hc, ite_eq_left ((hind k hka).mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((hind k hka).mpr h))]), Finset.sum_ite_eq']
  by_cases hdw : d ≤ w
  · rw [ite_eq_left (Finset.mem_Icc.mpr ⟨by simp [hk0, hdw], by simp [hk0, hdw]⟩), ite_eq_left hdw]
    simp [hk0, hdw]
  · rw [ite_eq_right hdw]
    by_cases hsd : s-w ≤ d
    · rw [ite_eq_left (Finset.mem_Icc.mpr ⟨by simp [hk0, hdw]; omega, by simp [hk0, hdw]; omega⟩), ite_eq_left hsd]
      simp [hk0, hdw]
    · rw [ite_eq_right hsd, ite_eq_right (fun h => by have := Finset.mem_Icc.mp h; simp [hk0, hdw] at this; omega)]

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
