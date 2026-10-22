module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceKeysB
public import IntegerMultBounds.MathlibTM2.M8.Global.DesignB
public import IntegerMultBounds.MathlibTM2.M8.Local.KeyOrderChecksB

/-! The actual stage's readout and source keys are duplicate-free. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local

theorem readout_order_nodup : assignment.readoutOrder.Nodup :=
  KeyOrderB.readout_nodup

theorem deferred_slots_nodup : planB.defS.Nodup := by
  rw [deferredSlots_materialized]
  exact KeyOrderB.deferred_nodup

theorem early_source_key_nodup : planB.keyE.Nodup := by
  rw [keyE_materialized]
  exact KeyOrderB.early_nodup

theorem late_source_key_nodup : planB.keyV.Nodup := by
  rw [keyV_materialized]
  exact KeyOrderB.late_nodup

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
