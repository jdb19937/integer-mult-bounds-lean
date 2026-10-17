module

public import IntegerMultBounds.Networks.PairedStarCount
import Mathlib.Data.Nat.BitIndices

/-! What the star count means. A merge pass finds no more matches than the
leaf lists whose lifted mask occurs in the other copy's list, and equal lifted
masks of increasing leaf lists are equal lifted leaf sets. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarCount

theorem insertSorted_perm (a : ℕ) (l : List ℕ) : (insertSorted a l).Perm (a :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons b bs ih =>
    simp only [insertSorted]
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.cons b ih).trans (List.Perm.swap a b bs)

theorem sortList_perm (l : List ℕ) : (sortList l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a as ih => exact (insertSorted_perm a _).trans (List.Perm.cons a ih)

theorem filter_length_mono (l B B' : List ℕ) (h : ∀ x, x ∈ B → x ∈ B') :
    (l.filter (fun x => decide (x ∈ B))).length ≤ (l.filter (fun x => decide (x ∈ B'))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun x _ hx => by simpa using h x (by simpa using hx))

/-- A merge pass counts only genuine common entries, each at most once. -/
theorem mergeCount_le (A B : List ℕ) :
    mergeCount A B ≤ (A.filter (fun x => decide (x ∈ B))).length := by
  induction A generalizing B with
  | nil => simp [mergeCount]
  | cons a as ih =>
    show mergeCount.mergeGo a (mergeCount as) B ≤ _
    induction B with
    | nil => simp [mergeCount.mergeGo]
    | cons b bs ihb =>
      simp only [mergeCount.mergeGo]
      split_ifs with hab hlt
      · subst hab
        have h1 := ih bs
        have h2 := filter_length_mono as bs (a :: bs) (fun x hx => List.mem_cons_of_mem a hx)
        rw [List.filter_cons_of_pos (by simp), List.length_cons]
        omega
      · have h1 := ih (b :: bs)
        have h2 : (as.filter (fun x => decide (x ∈ b :: bs))).length ≤
            ((a :: as).filter (fun x => decide (x ∈ b :: bs))).length := by
          simp only [List.filter_cons]
          split_ifs <;> simp
        omega
      · have h2 := filter_length_mono (a :: as) bs (b :: bs) (fun x hx => List.mem_cons_of_mem b hx)
        omega

/-- The leaf lists of center `c' - 1` whose lift into copy `c` meets a lifted
leaf list of center `c` in copy `c'`. -/
def matched (c c' : ℕ) : List (List ℕ) :=
  (fam (c' - 1)).filter (fun xs => decide (liftMask c (maskOf xs) ∈ lifted c' c))

theorem mem_lifted (c v m : ℕ) : m ∈ lifted c v ↔ ∃ xs ∈ fam v, liftMask c (maskOf xs) = m := by
  simp only [lifted, sortedMasks, List.mem_map, (sortList_perm _).mem_iff]
  constructor
  · rintro ⟨n, ⟨xs, hxs, rfl⟩, rfl⟩; exact ⟨xs, hxs, rfl⟩
  · rintro ⟨xs, hxs, rfl⟩; exact ⟨_, ⟨xs, hxs, rfl⟩, rfl⟩

theorem pairCount_le (c c' : ℕ) : pairCount c c' ≤ (matched c c').length := by
  have h := mergeCount_le (lifted c (c' - 1)) (lifted c' c)
  have hp : (lifted c (c' - 1)).Perm ((fam (c' - 1)).map (fun xs => liftMask c (maskOf xs))) := by
    simp only [lifted, sortedMasks]
    have := (sortList_perm ((fam (c' - 1)).map maskOf)).map (liftMask c)
    simpa [List.map_map, Function.comp_def] using this
  rw [(hp.filter _).length_eq, List.filter_map, List.length_map] at h
  exact h

theorem rowCount_le (c' : ℕ) :
    rowCount c' ≤ ((List.range c').map fun c => (matched c c').length).sum := by
  simp only [rowCount]
  induction (List.range c') with
  | nil => simp [sumNat]
  | cons c cs ih =>
    simp only [List.map_cons, sumNat, List.sum_cons]
    have := pairCount_le c c'
    omega

theorem sum_map_le {X : Type*} (l : List X) (f g : X → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem sumNat_eq (l : List ℕ) : sumNat l = l.sum := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [sumNat, ih]

/-- At least 40,256 matched leaf lists over all copy pairs `c < c'`. -/
theorem matched_total :
    40256 ≤ ((List.range 50).map fun c' =>
      ((List.range c').map fun c => (matched c c').length).sum).sum := by
  have hl := lowCount_eq
  have hh := highCount_eq
  have hsplit : List.range 50 = List.range 25 ++ List.range' 25 25 := by decide
  rw [hsplit, List.map_append, List.sum_append]
  simp only [lowCount, highCount, sumNat_eq] at hl hh
  have h1 : ((List.range 25).map rowCount).sum ≤ ((List.range 25).map fun c' =>
      ((List.range c').map fun c => (matched c c').length).sum).sum :=
    sum_map_le _ _ _ (fun c' _ => rowCount_le c')
  have h2 : ((List.range' 25 25).map rowCount).sum ≤ ((List.range' 25 25).map fun c' =>
      ((List.range c').map fun c => (matched c c').length).sum).sum :=
    sum_map_le _ _ _ (fun c' _ => rowCount_le c')
  omega

/-! ### Masks and leaf sets -/

theorem increasing_pairwise : ∀ xs : List ℕ, increasing xs = true → xs.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := increasing_pairwise (b :: rest) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

theorem testBit_maskOf (xs : List ℕ) (hx : xs.Pairwise (· < ·)) (y : ℕ) :
    (maskOf xs).testBit y = true ↔ y ∈ xs := by
  have hs : xs.SortedLT := List.sortedLT_iff_pairwise.mpr hx
  rw [← Nat.mem_bitIndices, maskOf, sumNat_eq, Nat.bitIndices_sum_map_two_pow hs]

/-- The `succAbove` embedding on local vertex numbers. -/
def sa (c x : ℕ) : ℕ := if x < c then x else x + 1

theorem testBit_liftMask (c m y : ℕ) :
    (liftMask c m).testBit y = true ↔ (y < c ∧ m.testBit y = true) ∨ (c < y ∧ m.testBit (y - 1) = true) := by
  have hlt : m % 2 ^ c < 2 ^ (c + 1) :=
    (Nat.mod_lt _ (Nat.two_pow_pos c)).trans (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self c))
  rw [liftMask, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlt]
  split_ifs with hy
  · rw [Nat.testBit_mod_two_pow]
    by_cases hc : y < c
    · simp only [hc, decide_true, Bool.true_and]
      exact ⟨fun h => Or.inl ⟨trivial, h⟩, fun h => h.elim (fun h => h.2) (fun h => absurd h.1 (by omega))⟩
    · have : y = c := by omega
      subst this
      simp
  · rw [Nat.testBit_div_two_pow, show y - (c + 1) + c = y - 1 by omega]
    constructor
    · intro h; exact Or.inr ⟨by omega, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · omega
      · exact h

theorem testBit_lift (c : ℕ) (xs : List ℕ) (hx : xs.Pairwise (· < ·)) (y : ℕ) :
    (liftMask c (maskOf xs)).testBit y = true ↔ y ∈ xs.map (sa c) := by
  rw [testBit_liftMask, testBit_maskOf xs hx, testBit_maskOf xs hx, List.mem_map]
  constructor
  · rintro (⟨hy, hm⟩ | ⟨hy, hm⟩)
    · exact ⟨y, hm, by simp [sa, hy]⟩
    · exact ⟨y - 1, hm, by simp only [sa]; split_ifs <;> omega⟩
  · rintro ⟨x, hm, rfl⟩
    simp only [sa]
    split_ifs with h
    · exact Or.inl ⟨h, hm⟩
    · exact Or.inr ⟨by omega, by simpa using hm⟩

/-- A matched leaf list has a partner in center `c` with the same lifted leaves. -/
theorem matched_spec (c c' : ℕ) (hc : c < c') (hc' : c' < 50) (xs : List ℕ) (hm : xs ∈ matched c c') :
    xs ∈ fam (c' - 1) ∧ ∃ ys ∈ fam c, ∀ y, y ∈ xs.map (sa c) ↔ y ∈ ys.map (sa c') := by
  simp only [matched, List.mem_filter, decide_eq_true_eq] at hm
  obtain ⟨ys, hys, he⟩ := (mem_lifted c' c _).mp hm.2
  refine ⟨hm.1, ys, hys, fun y => ?_⟩
  have hx := increasing_pairwise xs (by
    have := (List.all_eq_true.mp (fam_shape (c' - 1) (by omega))) xs hm.1
    simp only [leafShape, Bool.and_eq_true] at this
    exact this.1.1.1.1)
  have hy := increasing_pairwise ys (by
    have := (List.all_eq_true.mp (fam_shape c (by omega))) ys hys
    simp only [leafShape, Bool.and_eq_true] at this
    exact this.1.1.1.1)
  rw [← testBit_lift c xs hx, ← testBit_lift c' ys hy, he]

/-- The semantic shape of every listed leaf list. -/
theorem fam_shape' (v : ℕ) (hv : v < 49) (xs : List ℕ) (hm : xs ∈ fam v) :
    xs.Pairwise (· < ·) ∧ v ∉ xs ∧ (∀ x ∈ xs, x < 49) ∧ 2 ≤ xs.length ∧ xs.length ≤ 46 := by
  have h := (List.all_eq_true.mp (fam_shape v hv)) xs hm
  simp only [leafShape, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨increasing_pairwise xs h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Distinct listed leaf lists at one center have distinct masks. -/
theorem fam_nodup (v : ℕ) (hv : v < 49) : (fam v).Nodup := by
  have h := increasing_pairwise _ (masks_increasing v hv)
  have hn : (sortedMasks v).Nodup := h.imp (fun h => ne_of_lt h)
  rw [sortedMasks, (sortList_perm _).nodup_iff] at hn
  exact List.Nodup.of_map _ hn

theorem matched_nodup (c c' : ℕ) (hc' : c' - 1 < 49) : (matched c c').Nodup :=
  (fam_nodup _ hc').filter _

end IntegerMultBounds.Networks.PairedStarCount
