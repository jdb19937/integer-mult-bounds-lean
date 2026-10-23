module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveWidthEmbedded

/-! Placement and width-generated repair share only their record stream.
The six width-generation tapes belong to the repair core and remain disjoint
from every nonstream placement tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev widthPlacementT (t₀ : ℕ) := sharedScheduleT (repairT + 6) t₀

def widthPlacementEmbed {t₀ : ℕ} : Fin (repairT + 6) → Fin (widthPlacementT t₀) := sharedCoreEmbed

def widthPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (widthPlacementT t₀) :=
  sharedScheduleSlot (fieldCore repairHost.src)

theorem widthPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (widthPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem widthPlacementSlot_injective {t₀ : ℕ} : Function.Injective (widthPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (fieldCore repairHost.src)

@[simp] theorem widthPlacementSlot_str {t₀ : ℕ} :
    widthPlacementSlot (t₀ := t₀) .str = widthPlacementEmbed (fieldCore repairHost.src) :=
  sharedScheduleSlot_str _

theorem widthPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin (repairT + 6)) : widthPlacementSlot r ≠ widthPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem widthPlacementAux_separate {t₀ : ℕ} (i : Fin 6) (r : BinaryScheduleReg t₀ 3) :
    widthPlacementEmbed (fieldAux i) ≠ widthPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact (fieldCore_aux repairHost.src i).symm

end
end IntegerMultBounds.MathlibTM2.Routing
