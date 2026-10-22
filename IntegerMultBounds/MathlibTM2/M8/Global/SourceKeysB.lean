module

public import IntegerMultBounds.MathlibTM2.M8.Global.UseSlotsB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceUseChecksB

/-! The actual compiler's source and deferred-use keys are computable from
checked serving orders and allocation counts. No compiler prefix is evaluated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical

theorem keyE_materialized : planB.keyE = earlyV.map useSlotB := by
  change earlyV.map dagB.compile.pend = earlyV.map useSlotB
  exact List.map_congr_left fun u hu => sourceUse_slot u
    (List.all_eq_true.mp earlyV_sourceUseOk u hu)

theorem keyV_materialized : planB.keyV = lateV.map useSlotB := by
  change lateV.map dagB.compile.pend = lateV.map useSlotB
  exact List.map_congr_left fun u hu => sourceUse_slot u
    (List.all_eq_true.mp lateV_sourceUseOk u hu)

theorem deferredSlots_materialized : planB.defS = deferredUses.map useSlotB := by
  change deferredUses.map dagB.compile.pend = deferredUses.map useSlotB
  exact List.map_congr_left fun u hu => deferredUse_slot u hu

theorem keyD_materialized : planB.keyD = deferredUses.map useSlotB :=
  deferredSlots_materialized

theorem isDef_materialized (s : Nat) :
    planB.isDef s = decide (s ∈ deferredUses.map useSlotB) := by
  rw [BPlan.isDef, deferredSlots_materialized]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
