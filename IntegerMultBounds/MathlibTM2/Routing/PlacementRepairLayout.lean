module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairPlacement

/-! The joint placement/R2 bank shares exactly the record stream. All indexing
proofs are structural in an arbitrary core bank and instantiated here last. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable abbrev placementRepairT (t₀ : ℕ) : ℕ := sharedScheduleT repairT t₀

noncomputable def placementRepairEmbed {t₀ : ℕ} : Fin repairT → Fin (placementRepairT t₀) :=
  sharedCoreEmbed

noncomputable def placementScheduleSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (placementRepairT t₀) :=
  sharedScheduleSlot repairHost.src

theorem placementRepairEmbed_injective {t₀ : ℕ} : Function.Injective (placementRepairEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective (N := repairT) (t₀ := t₀)

theorem placementScheduleSlot_injective {t₀ : ℕ} : Function.Injective (placementScheduleSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (t₀ := t₀) repairHost.src

@[simp] theorem placementScheduleSlot_str {t₀ : ℕ} :
    placementScheduleSlot (t₀ := t₀) .str = placementRepairEmbed repairHost.src :=
  sharedScheduleSlot_str (t₀ := t₀) repairHost.src

theorem placementScheduleSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin repairT) : placementScheduleSlot r ≠ placementRepairEmbed i :=
  sharedScheduleSlot_separate repairHost.src r hr i

theorem placementRepairEmbed_separate {t₀ : ℕ} (i : Fin repairT) (hi : i ≠ repairHost.src)
    (r : BinaryScheduleReg t₀ 3) : placementRepairEmbed i ≠ placementScheduleSlot r :=
  sharedCoreEmbed_separate repairHost.src i hi r

end IntegerMultBounds.MathlibTM2.Routing
