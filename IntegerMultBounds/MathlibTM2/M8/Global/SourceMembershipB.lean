module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceKeysB
public import IntegerMultBounds.MathlibTM2.M8.Global.KeyOrderB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceListB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceSequenceChecksB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceCoverageKernelB

/-! Indexed membership checks describe the actual source and deferred-slot keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical

theorem deferredMember_spec (s : Nat) : KeyOrderB.deferredMember s = true ↔ s ∈ planB.defS := by
  rw [deferredSlots_materialized]
  exact keyMember_spec _ _ _ _ KeyOrderB.deferred_indexed KeyOrderB.deferred_sequence
    KeyOrderB.deferred_key_length s

theorem earlyMember_spec (s : Nat) : KeyOrderB.earlyMember s = true ↔ s ∈ planB.keyE := by
  rw [keyE_materialized]
  exact keyMember_spec _ _ _ _ KeyOrderB.early_indexed KeyOrderB.early_sequence
    KeyOrderB.early_key_length s

theorem lateMember_spec (s : Nat) : KeyOrderB.lateMember s = true ↔ s ∈ planB.keyV := by
  rw [keyV_materialized]
  exact keyMember_spec _ _ _ _ KeyOrderB.late_indexed KeyOrderB.late_sequence
    KeyOrderB.late_key_length s

/-- A checked free leaf use names an actual source operation. -/
theorem sourceUse_mem_sources (u : Use) (h : sourceUseOk u = true) :
    Op.src (useSlotB u) (useNodeB u) ∈ dagB.srcB := by
  unfold sourceUseOk at h
  obtain ⟨hn, hf⟩ := Bool.and_eq_true_iff.mp h
  have hn := Nat.blt_eq.mp hn
  have hu : u ∈ (bAt (useNodeB u)).2 := by
    rw [← dagB_freeUses_eq _ (hn.trans leafCount_lt)]
    exact freeB_mem hf
  rw [Dag.srcB_eq_sourceBlocks dagB dagB_valid]
  apply List.mem_flatMap.mpr
  refine ⟨useNodeB u, List.mem_range.mpr hn, ?_⟩
  unfold Dag.sourceBlock
  rw [dagB_compileTo_next _ (Nat.le_of_lt (hn.trans leafCount_lt)),
    dagB_freeUses_eq _ (hn.trans leafCount_lt)]
  apply List.mem_map.mpr
  refine ⟨useSlotB u, ?_, rfl⟩
  rw [List.mem_range'_1]
  have hi := List.idxOf_lt_length_iff.mpr hu
  simp only [useSlotB, ite_eq_left hn]
  constructor <;> omega

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
