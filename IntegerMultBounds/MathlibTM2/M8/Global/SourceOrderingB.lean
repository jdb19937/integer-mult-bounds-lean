module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceMembershipB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceCoverageChecksB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceOrderB

/-! The checked source keys are exactly the actual ordered compiler phases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical

def sourceOpB (u : Use) : Op := .src (useSlotB u) (useNodeB u)

theorem early_source_targets : (earlyV.map sourceOpB).map Op.target = planB.keyE := by
  rw [keyE_materialized]
  simp only [List.map_map, Function.comp_def, sourceOpB, Op.target]

theorem late_source_targets : (lateV.map sourceOpB).map Op.target = planB.keyV := by
  rw [keyV_materialized]
  simp only [List.map_map, Function.comp_def, sourceOpB, Op.target]

theorem early_key_not_deferred (s : Nat) (hs : s ∈ planB.keyE) : planB.isDef s = false := by
  rw [keyE_materialized] at hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
  have h := List.all_eq_true.mp KeyOrderB.early_phase u hu
  have hz : KeyOrderB.deferredMember (useSlotB u) = false := by
    simpa only [KeyOrderB.sourcePhaseOk, beq_iff_eq] using h
  have hn : useSlotB u ∉ planB.defS := by
    intro hm
    have he := (deferredMember_spec _).mpr hm
    rw [hz] at he
    cases he
  simp [BPlan.isDef, hn]

theorem late_key_deferred (s : Nat) (hs : s ∈ planB.keyV) : planB.isDef s = true := by
  rw [keyV_materialized] at hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
  have h := List.all_eq_true.mp KeyOrderB.late_phase u hu
  have hz : KeyOrderB.deferredMember (useSlotB u) = true := by
    simpa only [KeyOrderB.sourcePhaseOk, beq_iff_eq] using h
  have hm := (deferredMember_spec _).mp hz
  simp [BPlan.isDef, hm]

theorem sourceBlock_materialized (n : Nat) (hn : n < leafCount) :
    dagB.sourceBlock n = (KeyOrderB.sourceSlots n).map (fun s => .src s n) := by
  unfold Dag.sourceBlock KeyOrderB.sourceSlots
  rw [dagB_compileTo_next _ (Nat.le_of_lt (hn.trans leafCount_lt)),
    dagB_freeUses_eq _ (hn.trans leafCount_lt)]

/-- The finite slot coverage checks cover every actual compiler source operation. -/
theorem source_target_in_keys (op : Op) (ho : op ∈ dagB.srcB) :
    op.target ∈ planB.keyE ∨ op.target ∈ planB.keyV := by
  rw [Dag.srcB_eq_sourceBlocks dagB dagB_valid] at ho
  obtain ⟨n, hn, ho⟩ := List.mem_flatMap.mp ho
  have hn := List.mem_range.mp hn
  rw [sourceBlock_materialized n hn] at ho
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ho
  have hc := KeyOrderB.sourceCovered_at n hn
  unfold KeyOrderB.sourceCovered at hc
  have h := List.all_eq_true.mp hc s hs
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl ((earlyMember_spec s).mp h)
  · exact Or.inr ((lateMember_spec s).mp h)

theorem early_sources_perm :
    (dagB.srcB.filter fun op => !planB.isDef op.target).Perm (earlyV.map sourceOpB) := by
  apply source_filter_perm _ _ _ (dagB.srcB_targets_nodup dagB_valid)
    (early_source_targets.symm ▸ early_source_key_nodup)
  · intro op ho
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ho
    have hm := sourceUse_mem_sources u (List.all_eq_true.mp earlyV_sourceUseOk u hu)
    refine ⟨hm, ?_⟩
    have hk : useSlotB u ∈ planB.keyE := by
      rw [keyE_materialized]
      exact List.mem_map_of_mem hu
    simpa only [sourceOpB, Op.target, early_key_not_deferred _ hk] using (show (!false) = true from rfl)
  · intro op ho hp
    rw [early_source_targets]
    rcases source_target_in_keys op ho with h | h
    · exact h
    · rw [late_key_deferred _ h] at hp
      cases hp

theorem late_sources_perm :
    (dagB.srcB.filter fun op => planB.isDef op.target).Perm (lateV.map sourceOpB) := by
  apply source_filter_perm _ _ _ (dagB.srcB_targets_nodup dagB_valid)
    (late_source_targets.symm ▸ late_source_key_nodup)
  · intro op ho
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ho
    have hm := sourceUse_mem_sources u (List.all_eq_true.mp lateV_sourceUseOk u hu)
    refine ⟨hm, ?_⟩
    have hk : useSlotB u ∈ planB.keyV := by
      rw [keyV_materialized]
      exact List.mem_map_of_mem hu
    exact late_key_deferred _ hk
  · intro op ho hp
    rw [late_source_targets]
    rcases source_target_in_keys op ho with h | h
    · rw [early_key_not_deferred _ h] at hp
      cases hp
    · exact h

/-- The compiler's early source sort is exactly the checked use-key order. -/
theorem early_sources_materialized : dagB.vNow planB = earlyV.map sourceOpB := by
  exact keyedOps_eq_of_perm planB.keyE _ _ early_source_targets early_source_key_nodup early_sources_perm

/-- The compiler's late source sort is exactly the checked use-key order. -/
theorem late_sources_materialized : dagB.vLate planB = lateV.map sourceOpB := by
  exact keyedOps_eq_of_perm planB.keyV _ _ late_source_targets late_source_key_nodup late_sources_perm

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
