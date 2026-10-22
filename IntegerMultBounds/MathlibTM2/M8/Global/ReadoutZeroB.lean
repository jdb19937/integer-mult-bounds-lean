module

public import IntegerMultBounds.MathlibTM2.M8.Global.TargetMaskTraceB
public import IntegerMultBounds.MathlibTM2.M8.Local.ReadoutCoverageChecksB

/-! All initial readout frames are zero; nonzero frames occur only in the late key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- A nonzero allocated readout label names an actual entry of the checked key. -/
theorem nonzero_sigma_in_readout_order (s : Nat) (hs : s < dagB.compile.next)
    (hz : AssignmentB.sigmaLabel s ≠ Signed.Frame.zero) : s ∈ assignment.readoutOrder := by
  have hb : s < 28866 := by simpa only [compiler_slot_count, GeometryB.slotCount] using hs
  have h := Tree.all_get KeyOrderB.nonzeroCovered (fun _ => true) 28866
    AssignmentB.sigmaTable 32768 0 KeyOrderB.sigmaTable_perfect KeyOrderB.nonzero_coverage s
    (by omega) (by simpa using hb)
  replace h : KeyOrderB.nonzeroCovered s (AssignmentB.sigmaLabel s) = true := by
    simpa only [Nat.zero_add, AssignmentB.sigmaLabel, AssignmentB.sigmaWidth] using h
  unfold KeyOrderB.nonzeroCovered at h
  rw [ite_eq_right hz] at h
  obtain ⟨hi, he⟩ := Bool.and_eq_true_iff.mp h
  have hi : KeyOrderB.readoutIndex s < AssignmentB.readoutOrder.length := by
    rw [KeyOrderB.readout_length]
    exact Nat.blt_eq.mp hi
  have hg := sequenceCheck_get KeyOrderB.readoutAt 0 AssignmentB.readoutOrder
    KeyOrderB.readout_sequence (KeyOrderB.readoutIndex s) hi
  have he : KeyOrderB.readoutAt (KeyOrderB.readoutIndex s) = s := Nat.beq_eq.mp he
  have hm := List.getElem_mem hi
  rw [← hg, Nat.zero_add, he] at hm
  exact hm

/-- The immediate-readout slots have no nonzero frame. -/
theorem now_slot_sigma_zero (s : Nat) (hs : s ∈ nowSlots) : assignment.sigma s = 0 := by
  obtain ⟨hb, hd⟩ := List.mem_filter.mp hs
  have hb := List.mem_range.mp hb
  have hz : AssignmentB.sigmaLabel s = Signed.Frame.zero := by
    by_contra hn
    have hr := nonzero_sigma_in_readout_order s hb hn
    have hm := readout_order_perm_deferred.mem_iff.mp hr
    simp [BPlan.isDef, hm] at hd
  simp [assignment, hz, frameOfLabel, Signed.Frame.eval]

/-- Every initial target-readout occurrence has frame zero, regardless of its mask bit. -/
theorem now_target_trace_zero (t : Nat) :
    ((targetReadouts nowSlots t).map assignment.sigma).all (fun F => decide (F = 0)) = true := by
  apply List.all_eq_true.mpr
  intro F hF
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hF
  simp [now_slot_sigma_zero s (List.mem_filter.mp hs).1]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
