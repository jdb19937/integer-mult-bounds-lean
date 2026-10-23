module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderData

/-! Placement shares only the record stream with header-generated repair.
The complete header workspace is separate from placement metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev headerPlacementT (t₀ : ℕ) := sharedScheduleT repairHeaderT t₀

def headerPlacementEmbed {t₀ : ℕ} : Fin repairHeaderT → Fin (headerPlacementT t₀) := sharedCoreEmbed

def headerPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (headerPlacementT t₀) :=
  sharedScheduleSlot (repairHeaderRawCore repairHost.src)

theorem headerPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (headerPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem headerPlacementSlot_injective {t₀ : ℕ} : Function.Injective (headerPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (repairHeaderRawCore repairHost.src)

@[simp] theorem headerPlacementSlot_str {t₀ : ℕ} :
    headerPlacementSlot (t₀ := t₀) .str = headerPlacementEmbed (repairHeaderRawCore repairHost.src) :=
  sharedScheduleSlot_str _

theorem headerPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin repairHeaderT) : headerPlacementSlot r ≠ headerPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem headerPlacementWork_separate {t₀ : ℕ} (r : HeaderWorkRole) (j : BinaryScheduleReg t₀ 3) :
    headerPlacementEmbed (sharedHeaderWork r) ≠ headerPlacementSlot j := by
  apply sharedCoreEmbed_separate
  exact (sharedHeaderCore_work (classifierCore (repairConfigurationCore repairHost.src)) r).symm

theorem headerPlacementRaw_separate {t₀ : ℕ} (i : Fin repairT) (hi : i ≠ repairHost.src)
    (r : BinaryScheduleReg t₀ 3) :
    headerPlacementEmbed (repairHeaderRawCore i) ≠ headerPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact repairHeaderRawCore_injective.ne hi

end
end IntegerMultBounds.MathlibTM2.Routing
