module

public import IntegerMultBounds.MathlibTM2.M8.Global.KeyOrderB
public import IntegerMultBounds.MathlibTM2.M8.Global.CompilerBoundaryB
public import IntegerMultBounds.MathlibTM2.M8.Local.ReadoutOrderChecksB

/-! The actual late-readout order is exactly the checked zero-first partition. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The stage's key is the deferred-use key, with zero frames stably moved first. -/
theorem readout_order_partition :
    assignment.readoutOrder = planB.defS.filter KeyOrderB.zeroReadout ++
      planB.defS.filter (fun s => !KeyOrderB.zeroReadout s) := by
  rw [deferredSlots_materialized]
  exact KeyOrderB.readout_partition

theorem readout_order_perm_deferred : assignment.readoutOrder.Perm planB.defS := by
  rw [deferredSlots_materialized]
  exact KeyOrderB.readout_perm_deferred

theorem readout_order_bound (s : Nat) (hs : s ∈ assignment.readoutOrder) :
    s < dagB.compile.next := by
  have h := List.all_eq_true.mp KeyOrderB.readout_bounded s hs
  have hb : s < 28866 := Nat.blt_eq.mp h
  rw [compiler_slot_count]
  exact hb

theorem deferred_slots_bound (s : Nat) (hs : s ∈ planB.defS) :
    s < dagB.compile.next :=
  readout_order_bound s (readout_order_perm_deferred.mem_iff.mpr hs)

/-- Filtering the allocated slot range retains exactly the deferred key's entries. -/
theorem deferred_range_perm :
    ((List.range dagB.compile.next).filter planB.isDef).Perm planB.defS := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) deferred_slots_nodup).mpr
  intro s
  simp only [List.mem_filter, List.mem_range, BPlan.isDef, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨deferred_slots_bound s h, h⟩⟩

/-- The keyed compiler list is the concrete frame-order key itself, not a
separately generated or simplified approximation of its trace. -/
theorem lateSlots_materialized : lateSlots assignment.readoutOrder = assignment.readoutOrder := by
  exact keyed_eq_of_perm assignment.readoutOrder _ readout_order_nodup
    (deferred_range_perm.trans readout_order_perm_deferred.symm)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
