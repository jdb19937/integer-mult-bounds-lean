module

public import IntegerMultBounds.MathlibTM2.M8.Local.WordB

/-! Structural ordering lemmas for source and readout keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local
noncomputable section
open Classical

/-- A duplicate-free key is ordered by its own positions. -/
theorem pairwise_key_positions (key : List Nat) (hnd : key.Nodup) :
    key.Pairwise (fun a b => key.idxOf a ≤ key.idxOf b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [hnd.idxOf_getElem i hi, hnd.idxOf_getElem j hj]
  omega

/-- Filtering a complete key and then sorting by that key recovers its filtered order. -/
theorem keyed_filter_of_perm (key ss : List Nat) (hnd : key.Nodup)
    (hp : ss.Perm key) (p : Nat → Bool) :
    keyed key (ss.filter p) = key.filter p := by
  have hperm : (keyed key (ss.filter p)).Perm (key.filter p) :=
    (List.mergeSort_perm _ _).trans (hp.filter p)
  have hsort : (keyed key (ss.filter p)).Pairwise (fun a b => key.idxOf a ≤ key.idxOf b) := by
    have h := List.pairwise_mergeSort
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (le := fun a b : Nat => decide (key.idxOf a ≤ key.idxOf b)) (ss.filter p)
    exact h.imp of_decide_eq_true
  apply List.Perm.eq_of_pairwise _ hsort ((pairwise_key_positions key hnd).filter p) hperm
  intro a b ha _ hab hba
  have ha' : a ∈ key := List.mem_of_mem_filter ((hperm.mem_iff).mp ha)
  exact (List.idxOf_inj ha').mp (by omega)

theorem keyed_eq_of_perm (key ss : List Nat) (hnd : key.Nodup) (hp : ss.Perm key) :
    keyed key ss = key := by
  simpa using keyed_filter_of_perm key ss hnd hp (fun _ => true)

/-- An independently checked inverse position table proves key uniqueness without
quadratic duplicate checks or comparison of large concrete list terms. -/
theorem nodup_of_index_inverse {α : Type*} (xs : List α) (index : α → Nat)
    (h : ∀ i (hi : i < xs.length), index xs[i] = i) : xs.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j he
  apply Fin.ext
  have hs := congrArg index he
  simpa only [h i.val i.isLt, h j.val j.isLt] using hs

end
end IntegerMultBounds.MathlibTM2.M8.Local
