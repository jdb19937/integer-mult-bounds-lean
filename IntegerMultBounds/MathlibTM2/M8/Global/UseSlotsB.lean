module

public import IntegerMultBounds.MathlibTM2.M8.Global.ArgumentFramesB
public import IntegerMultBounds.MathlibTM2.M8.Local.UseSlotsB

/-! The actual compiler slot of each newly allocated free use, including
uses already consumed by the final compiler state. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical

theorem compiled_allocated_use_slot (n : Nat) (hn : n < nodeCount)
    (i : Nat) (hi : i < (dagB.freeUses n).length) (hnew : n < leafCount ∨ i ≠ 0) :
    dagB.compile.pend (dagB.freeUses n)[i] =
      slotsBefore n + if n < leafCount then i else i - 1 := by
  have hu : (dagB.freeUses n)[i] ∈ dagB.freeUses n := List.getElem_mem hi
  have hsrc := dagB.srcNode_free hu
  rw [Dag.compile, FrameFlow.compileTo_pend_after_source dagB dagB_valid _ (n + 1) dagB.N
    (by rw [hsrc]; omega) (by exact Nat.succ_le_of_lt hn) le_rfl]
  let st := dagB.compileTo n
  by_cases hv : n < leafCount
  · have hs : (dagB.compileTo (n + 1)).pend (dagB.freeUses n)[i] = st.next + i := by
      rw [compile_step]
      unfold Dag.step
      rw [ite_eq_left (show n < dagB.v from hv),
        FrameFlow.serve_pend_index _ _ _ _ (dagB.freeUses_nodup n) i hi]
      split_ifs <;> simp_all [st]
      omega
    rw [hs, ite_eq_left hv]
    exact congrArg (· + i) (dagB_compileTo_next n (Nat.le_of_lt hn))
  · have hi0 : i ≠ 0 := hnew.resolve_left hv
    obtain ⟨p, o, st', _, _, _, hnext, hstep⟩ :=
      FrameFlow.step_internal_shape dagB n (Nat.le_of_not_gt hv) st
    rw [compile_step]
    change (dagB.step st n).pend (dagB.freeUses n)[i] = _
    rw [hstep, FrameFlow.serve_pend_index _ _ _ _ (dagB.freeUses_nodup n) i hi,
      ite_eq_right hi0, hnext, ite_eq_right hv]
    exact congrArg (· + (i - 1)) (dagB_compileTo_next n (Nat.le_of_lt hn))

/-- A free use that receives a fresh slot has its computable slot label. -/
theorem allocated_use_slot (u : Use) (hn : useNodeB u < nodeCount)
    (hfree : freeB (useNodeB u) u = true)
    (hnew : useNodeB u < leafCount ∨ (bAt (useNodeB u)).2.idxOf u ≠ 0) :
    dagB.compile.pend u = useSlotB u := by
  have hu := freeB_mem hfree
  have hm : u ∈ (bAt (useNodeB u)).2 := by rwa [← dagB_freeUses_eq _ hn]
  have hi : (bAt (useNodeB u)).2.idxOf u < (dagB.freeUses (useNodeB u)).length := by
    rw [dagB_freeUses_eq _ hn]
    exact List.idxOf_lt_length_iff.mpr hm
  have he : (dagB.freeUses (useNodeB u))[(bAt (useNodeB u)).2.idxOf u] = u := by
    simp only [dagB_freeUses_eq _ hn]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hm)
  have h := compiled_allocated_use_slot (useNodeB u) hn _ hi hnew
  simpa only [he, useSlotB] using h

theorem sourceUse_slot (u : Use) (h : sourceUseOk u = true) :
    dagB.compile.pend u = useSlotB u := by
  unfold sourceUseOk at h
  obtain ⟨hn, hfree⟩ := Bool.and_eq_true_iff.mp h
  have hn := Nat.blt_eq.mp hn
  exact allocated_use_slot u (hn.trans leafCount_lt) hfree (Or.inl hn)

/-- Deferred internal uses never keep the pivot, so they too have fresh slots. -/
theorem deferredUse_slot (u : Use) (hu : u ∈ deferredUses) :
    dagB.compile.pend u = useSlotB u := by
  have h := deferredOk_of_mem hu
  unfold deferredOk at h
  obtain ⟨⟨hfree, hn⟩, hc⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have hn := Nat.blt_eq.mp hn
  apply allocated_use_slot u hn hfree
  by_cases hv : useNodeB u < leafCount
  · exact Or.inl hv
  · apply Or.inr
    have hv' : Nat.ble leafCount (useNodeB u) = true := Nat.ble_eq.mpr (Nat.le_of_not_gt hv)
    rw [hv', Bool.cond_true] at hc
    have hhead := (Bool.and_eq_true_iff.mp hc).2
    cases hb : (bAt (useNodeB u)).2 with
    | nil => rw [hb] at hhead; cases hhead
    | cons w ws =>
      rw [hb] at hhead
      have hne : w ≠ u := by
        simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] using
          (Bool.and_eq_true_iff.mp hhead).1
      rw [List.idxOf_cons]
      simp [hne]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
