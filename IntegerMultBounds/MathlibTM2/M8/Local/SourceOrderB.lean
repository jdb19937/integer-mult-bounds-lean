module

public import IntegerMultBounds.MathlibTM2.M8.Local.KeyedOrderB

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

end
end IntegerMultBounds.MathlibTM2.M8.Local
