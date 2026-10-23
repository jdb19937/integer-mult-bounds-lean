module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfigurationEmbedded

/-! Placement and width-generated repair share only their record stream.
The six width-generation tapes belong to the repair core and remain disjoint
from every nonstream placement tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev configurationPlacementT (t₀ : ℕ) := sharedScheduleT repairConfigurationT t₀

def configurationPlacementEmbed {t₀ : ℕ} : Fin repairConfigurationT → Fin (configurationPlacementT t₀) := sharedCoreEmbed

def configurationPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (configurationPlacementT t₀) :=
  sharedScheduleSlot (fieldCore (N := repairDescriptorT) (descriptorCore (J := 11) repairHost.src))

theorem configurationPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (configurationPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem configurationPlacementSlot_injective {t₀ : ℕ} : Function.Injective (configurationPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (fieldCore (N := repairDescriptorT) (descriptorCore (J := 11) repairHost.src))

@[simp] theorem configurationPlacementSlot_str {t₀ : ℕ} :
    configurationPlacementSlot (t₀ := t₀) .str = configurationPlacementEmbed (fieldCore (N := repairDescriptorT) (descriptorCore (J := 11) repairHost.src)) :=
  sharedScheduleSlot_str _

theorem configurationPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin repairConfigurationT) : configurationPlacementSlot r ≠ configurationPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem configurationPlacementAux_separate {t₀ : ℕ} (i : Fin 6) (r : BinaryScheduleReg t₀ 3) :
    configurationPlacementEmbed (fieldAux i) ≠ configurationPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact (fieldCore_aux (descriptorCore (J := 11) repairHost.src) i).symm

end
end IntegerMultBounds.MathlibTM2.Routing
