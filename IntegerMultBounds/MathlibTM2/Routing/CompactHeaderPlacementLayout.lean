module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderData

/-! Placement shares only the record stream with header-generated repair.
The complete header workspace is separate from placement metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev compactHeaderPlacementT (t₀ : ℕ) := sharedScheduleT repairCompactHeaderT t₀

def compactHeaderPlacementEmbed {t₀ : ℕ} : Fin repairCompactHeaderT → Fin (compactHeaderPlacementT t₀) := sharedCoreEmbed

def compactHeaderPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (compactHeaderPlacementT t₀) :=
  sharedScheduleSlot (repairCompactHeaderRawCore repairHost.src)

theorem compactHeaderPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (compactHeaderPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem compactHeaderPlacementSlot_injective {t₀ : ℕ} : Function.Injective (compactHeaderPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (repairCompactHeaderRawCore repairHost.src)

@[simp] theorem compactHeaderPlacementSlot_str {t₀ : ℕ} :
    compactHeaderPlacementSlot (t₀ := t₀) .str = compactHeaderPlacementEmbed (repairCompactHeaderRawCore repairHost.src) :=
  sharedScheduleSlot_str _

theorem compactHeaderPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin repairCompactHeaderT) : compactHeaderPlacementSlot r ≠ compactHeaderPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem compactHeaderPlacementWork_separate {t₀ : ℕ} (r : HeaderWorkRole) (j : BinaryScheduleReg t₀ 3) :
    compactHeaderPlacementEmbed (sharedHeaderWork r) ≠ compactHeaderPlacementSlot j := by
  apply sharedCoreEmbed_separate
  exact (sharedHeaderCore_work (classifierCore (repairCompactConfigurationCore repairHost.src)) r).symm

theorem compactHeaderPlacementRaw_separate {t₀ : ℕ} (i : Fin repairT) (hi : i ≠ repairHost.src)
    (r : BinaryScheduleReg t₀ 3) :
    compactHeaderPlacementEmbed (repairCompactHeaderRawCore i) ≠ compactHeaderPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact repairCompactHeaderRawCore_injective.ne hi

end
end IntegerMultBounds.MathlibTM2.Routing
