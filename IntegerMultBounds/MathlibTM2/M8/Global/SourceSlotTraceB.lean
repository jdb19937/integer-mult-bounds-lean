module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceTraceB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB.Kernel

/-! Small leaf-slot intervals recover the exact filtered source-key traces. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem source_earlyMember (op : Op) (ho : op ∈ dagB.srcB) :
    KeyOrderB.earlyMember op.target = !planB.isDef op.target := by
  by_cases he : KeyOrderB.earlyMember op.target = true
  · rw [he, early_key_not_deferred _ ((earlyMember_spec _).mp he)]
    rfl
  · have he' : KeyOrderB.earlyMember op.target = false := Bool.eq_false_iff.mpr he
    have hk : op.target ∈ planB.keyV := by
      rcases source_target_in_keys op ho with hk | hk
      · exact False.elim (he ((earlyMember_spec _).mpr hk))
      · exact hk
    rw [he', late_key_deferred _ hk]
    rfl

theorem source_lateMember (op : Op) (ho : op ∈ dagB.srcB) :
    KeyOrderB.lateMember op.target = planB.isDef op.target := by
  by_cases he : KeyOrderB.lateMember op.target = true
  · rw [he, late_key_deferred _ ((lateMember_spec _).mp he)]
  · have he' : KeyOrderB.lateMember op.target = false := Bool.eq_false_iff.mpr he
    have hk : op.target ∈ planB.keyE := by
      rcases source_target_in_keys op ho with hk | hk
      · exact hk
      · exact False.elim (he ((lateMember_spec _).mpr hk))
    rw [he', early_key_not_deferred _ hk]

theorem source_leaf_slots (n : Nat) (hn : n < leafCount) :
    ((dagB.srcB.filter fun op => decide (op.node = n)).map Op.target) =
      KeyOrderB.sourceSlots n := by
  rw [Dag.srcB_leaf_targets dagB dagB_valid n hn]
  unfold KeyOrderB.sourceSlots
  rw [dagB_compileTo_next _ (Nat.le_of_lt (hn.trans leafCount_lt)),
    dagB_freeUses_eq _ (hn.trans leafCount_lt)]

theorem sourceUse_targets (us : List Use) (n : Nat) :
    (((us.map sourceOpB).filter fun op => decide (op.node = n)).map Op.target) =
      (sourceUses us n).map useSlotB := by
  rw [List.filter_map, List.map_map]
  have hnode (u : Use) : decide ((sourceOpB u).node = n) = decide (useNodeB u = n) :=
    congrArg (fun k : Nat => decide (k = n)) (show (sourceOpB u).node = useNodeB u from rfl)
  have hpred : (fun u : Use => decide ((sourceOpB u).node = n)) =
      (fun u : Use => decide (useNodeB u = n)) := funext hnode
  have ht : (Op.target ∘ sourceOpB) = useSlotB := funext fun _ => rfl
  change ((us.filter fun u => decide ((sourceOpB u).node = n)).map (Op.target ∘ sourceOpB)) = _
  rw [hpred, ht]
  rfl

theorem early_leaf_slots_perm (n : Nat) (hn : n < leafCount) :
    ((KeyOrderB.sourceSlots n).filter KeyOrderB.earlyMember).Perm
      ((sourceUses earlyV n).map useSlotB) := by
  have h := filter_targets_perm dagB.srcB (earlyV.map sourceOpB)
    (fun op => !planB.isDef op.target) (fun op => decide (op.node = n)) KeyOrderB.earlyMember
    early_sources_perm source_earlyMember
  rw [source_leaf_slots n hn] at h
  rw [sourceUse_targets] at h
  exact h

theorem late_leaf_slots_perm (n : Nat) (hn : n < leafCount) :
    ((KeyOrderB.sourceSlots n).filter KeyOrderB.lateMember).Perm
      ((sourceUses lateV n).map useSlotB) := by
  have h := filter_targets_perm dagB.srcB (lateV.map sourceOpB)
    (fun op => planB.isDef op.target) (fun op => decide (op.node = n)) KeyOrderB.lateMember
    late_sources_perm source_lateMember
  rw [source_leaf_slots n hn] at h
  rw [sourceUse_targets] at h
  exact h

/-- Sorting the small allocation interval recovers the early key's exact order. -/
theorem earlySlots_eq (n : Nat) (hn : n < leafCount) :
    SourceGeometryB.earlySlots n = (sourceUses earlyV n).map useSlotB :=
  sort_index_eq KeyOrderB.earlyIndex (earlyV.map useSlotB) _ _ KeyOrderB.early_indexed
    (List.filter_sublist.map useSlotB) (early_leaf_slots_perm n hn)

/-- Sorting the small allocation interval recovers the late key's exact order. -/
theorem lateSlots_eq (n : Nat) (hn : n < leafCount) :
    SourceGeometryB.lateSlots n = (sourceUses lateV n).map useSlotB :=
  sort_index_eq KeyOrderB.lateIndex (lateV.map useSlotB) _ _ KeyOrderB.late_indexed
    (List.filter_sublist.map useSlotB) (late_leaf_slots_perm n hn)

theorem sourceGeometry_labels_eq (n : Nat) (hn : n < leafCount) :
    SourceGeometryB.sourceLabels n = sourceLabels earlyV n ++ sourceLabels lateV n := by
  rw [SourceGeometryB.sourceLabels, earlySlots_eq n hn, lateSlots_eq n hn, List.map_append]
  simp only [sourceLabels, List.map_map, Function.comp_def]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
