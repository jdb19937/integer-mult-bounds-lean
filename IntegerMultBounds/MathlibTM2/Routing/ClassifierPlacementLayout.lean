module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierBank

/-! Placement and classifier-generated repair share only their record stream.
All sixteen classifier workspace tapes are disjoint from placement metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev classifierPlacementT (t₀ : ℕ) := sharedScheduleT repairClassifierT t₀

def classifierPlacementEmbed {t₀ : ℕ} : Fin repairClassifierT → Fin (classifierPlacementT t₀) := sharedCoreEmbed

def classifierPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (classifierPlacementT t₀) :=
  sharedScheduleSlot (classifierCore (repairConfigurationCore repairHost.src))

theorem classifierPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (classifierPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem classifierPlacementSlot_injective {t₀ : ℕ} : Function.Injective (classifierPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (classifierCore (repairConfigurationCore repairHost.src))

@[simp] theorem classifierPlacementSlot_str {t₀ : ℕ} :
    classifierPlacementSlot (t₀ := t₀) .str = classifierPlacementEmbed (classifierCore (repairConfigurationCore repairHost.src)) :=
  sharedScheduleSlot_str _

theorem classifierPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin repairClassifierT) : classifierPlacementSlot r ≠ classifierPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem classifierPlacementAux_separate {t₀ : ℕ} (i : Fin 16) (r : BinaryScheduleReg t₀ 3) :
    classifierPlacementEmbed (classifierAux i) ≠ classifierPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact (classifierCore_aux (repairConfigurationCore repairHost.src) i).symm

theorem classifierPlacementConfiguration_separate {t₀ : ℕ} (i : Fin repairConfigurationT)
    (hi : i ≠ repairConfigurationCore repairHost.src) (r : BinaryScheduleReg t₀ 3) :
    classifierPlacementEmbed (classifierCore i) ≠ classifierPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact classifierCore_injective.ne hi

end
end IntegerMultBounds.MathlibTM2.Routing
