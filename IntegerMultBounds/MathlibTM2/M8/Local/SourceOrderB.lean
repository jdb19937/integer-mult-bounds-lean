module

public import IntegerMultBounds.MathlibTM2.M8.Local.KeyIndexB
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotSortB

/-! Structural ordering of source operations through their target slots. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local
noncomputable section
open Classical

/-- Sorting operations by a slot key sorts their target projection by the same key. -/
theorem keyedOps_targets (key : List Nat) (ops : List Op) :
    (keyedOps key ops).map Op.target = keyed key (ops.map Op.target) :=
  List.map_mergeSort (fun _ _ _ _ => rfl)

/-- A complete target key determines the projected order of the source operations. -/
theorem keyedOps_targets_eq (key : List Nat) (ops : List Op) (hnd : key.Nodup)
    (hp : (ops.map Op.target).Perm key) :
    (keyedOps key ops).map Op.target = key := by
  rw [keyedOps_targets]
  exact keyed_eq_of_perm key _ hnd hp

/-- Sorting a permutation of source operations recovers their complete target-key order. -/
theorem keyedOps_eq_of_perm (key : List Nat) (ops wanted : List Op)
    (hkey : wanted.map Op.target = key) (hnd : key.Nodup) (hp : ops.Perm wanted) :
    keyedOps key ops = wanted := by
  have hperm : (keyedOps key ops).Perm wanted := (List.mergeSort_perm _ _).trans hp
  have hsort : (keyedOps key ops).Pairwise
      (fun a b => key.idxOf a.target ≤ key.idxOf b.target) := by
    have h := List.pairwise_mergeSort
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (le := fun a b : Op => decide (key.idxOf a.target ≤ key.idxOf b.target)) ops
    exact h.imp of_decide_eq_true
  have hw : wanted.Pairwise (fun a b => key.idxOf a.target ≤ key.idxOf b.target) := by
    have h := pairwise_key_positions key hnd
    rw [← hkey, List.pairwise_map] at h
    simpa only [hkey] using h
  have hndw : (wanted.map Op.target).Nodup := hkey.symm ▸ hnd
  apply List.Perm.eq_of_pairwise _ hsort hw hperm
  intro a b ha hb hab hba
  have ha := hperm.mem_iff.mp ha
  have hta : a.target ∈ key := hkey ▸ List.mem_map_of_mem ha
  have he : a.target = b.target := (List.idxOf_inj hta).mp (by omega)
  exact List.inj_on_of_nodup_map hndw ha hb he

/-- A complete duplicate-free key selects exactly the intended source operations. -/
theorem source_filter_perm (ops wanted : List Op) (p : Op → Bool)
    (hops : (ops.map Op.target).Nodup) (hwanted : (wanted.map Op.target).Nodup)
    (hw : ∀ op ∈ wanted, op ∈ ops ∧ p op = true)
    (hc : ∀ op ∈ ops, p op = true → op.target ∈ wanted.map Op.target) :
    (ops.filter p).Perm wanted := by
  apply (List.perm_ext_iff_of_nodup ((List.Nodup.of_map _ hops).filter p)
    (List.Nodup.of_map _ hwanted)).mpr
  intro op
  constructor
  · intro ho
    obtain ⟨ho, hp⟩ := List.mem_filter.mp ho
    obtain ⟨w, hw', he⟩ := List.mem_map.mp (hc op ho hp)
    have he : w = op := List.inj_on_of_nodup_map hops (hw w hw').1 ho he
    simpa only [he] using hw'
  · intro ho
    exact List.mem_filter.mpr (hw op ho)

/-- Checked inverse positions agree with a duplicate-free key's own indices. -/
theorem indexCheck_eq_idxOf (index : Nat → Nat) (key : List Nat)
    (h : indexCheck index 0 key = true) (s : Nat) (hs : s ∈ key) : index s = key.idxOf s := by
  have hi := List.idxOf_lt_length_iff.mpr hs
  simpa only [List.getElem_idxOf hi, Nat.zero_add] using
    indexCheck_get index 0 key h (key.idxOf s) hi

theorem insertSlot_perm (index : Nat → Nat) (x : Nat) : ∀ xs,
    (insertSlot index x xs).Perm (x :: xs)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertSlot
    split_ifs
    · exact List.Perm.refl _
    · exact ((insertSlot_perm index x ys).cons y).trans (List.Perm.swap _ _ _)

theorem sortSlots_perm (index : Nat → Nat) : ∀ xs, (sortSlots index xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => (insertSlot_perm index x _).trans ((sortSlots_perm index xs).cons x)

theorem insertSlot_pairwise (index : Nat → Nat) (x : Nat) : ∀ xs,
    xs.Pairwise (fun a b => index a ≤ index b) →
      (insertSlot index x xs).Pairwise (fun a b => index a ≤ index b)
  | [], _ => by simp [insertSlot]
  | y :: ys, h => by
    obtain ⟨hy, hs⟩ := List.pairwise_cons.mp h
    unfold insertSlot
    split_ifs with hxy
    · apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hy, hs⟩⟩
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact Nat.ble_eq.mp hxy
      · exact (Nat.ble_eq.mp hxy).trans (hy a ha)
    · apply List.pairwise_cons.mpr
      refine ⟨?_, insertSlot_pairwise index x ys hs⟩
      intro a ha
      have ha := (insertSlot_perm index x ys).mem_iff.mp ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        have hxy : ¬ index x ≤ index y := by simpa only [Nat.ble_eq] using hxy
        omega
      · exact hy a ha

theorem sortSlots_pairwise (index : Nat → Nat) : ∀ xs,
    (sortSlots index xs).Pairwise (fun a b => index a ≤ index b)
  | [] => by simp [sortSlots]
  | x :: xs => insertSlot_pairwise index x _ (sortSlots_pairwise index xs)

/-- Sorting a permutation of a key sublist by checked inverse indices recovers it. -/
theorem sort_index_eq (index : Nat → Nat) (key ss wanted : List Nat)
    (hindex : indexCheck index 0 key = true) (hw : wanted.Sublist key) (hp : ss.Perm wanted) :
    sortSlots index ss = wanted := by
  have hnd := nodup_of_indexCheck index key hindex
  have hi := indexCheck_eq_idxOf index key hindex
  have hperm := (sortSlots_perm index ss).trans hp
  have hsort := sortSlots_pairwise index ss
  have hkey : key.Pairwise (fun a b => index a ≤ index b) :=
    (pairwise_key_positions key hnd).imp_of_mem (fun {a b} ha hb hab => by
      rw [hi a ha, hi b hb]
      exact hab)
  apply List.Perm.eq_of_pairwise _ hsort (hkey.sublist hw) hperm
  intro a b ha hb hab hba
  have ha := hw.subset (hperm.mem_iff.mp ha)
  have hb := hw.subset hb
  apply (List.idxOf_inj ha).mp
  rw [← hi a ha, ← hi b hb]
  omega

/-- Projecting a tagged source phase commutes with a slot membership predicate. -/
theorem filter_targets_perm (ops wanted : List Op) (p tag : Op → Bool) (q : Nat → Bool)
    (hp : (ops.filter p).Perm wanted) (hq : ∀ op ∈ ops, q op.target = p op) :
    (((ops.filter tag).map Op.target).filter q).Perm ((wanted.filter tag).map Op.target) := by
  have he : ((ops.filter tag).map Op.target).filter q =
      ((ops.filter p).filter tag).map Op.target := by
    rw [List.filter_map, ← List.filter_comm p tag]
    apply congrArg (List.map Op.target)
    apply List.filter_congr
    intro op ho
    exact hq op (List.mem_filter.mp ho).1
  rw [he]
  exact (hp.filter tag).map Op.target

end
end IntegerMultBounds.MathlibTM2.M8.Local
