module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorScratch
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Generated descriptor tables do not touch any scratch, installed target or
record-stream tape needed by actual exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairCompactBank_core_keep (Lw Lg L : Fin 11 → ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4))) (j : Fin repairT)
    (hj : ∀ d, j ≠ repairDescriptorSource d) :
    compactDescriptorBankGenerated bank (repairCompactJobs p X hG hK active s Lw Lg L) (compactDescriptorCore j) =
      bank (compactDescriptorCore j) := by
  apply compactDescriptorBankGenerated_keep
  intro job hjob
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hjob
  exact compactDescriptorCore_injective.ne (hj (repairDescriptorKey k))

theorem repairCompactBank_blank (Lw Lg L : Fin 11 → ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4)))
    (hblank : ∀ j, RepairBlank j → bank (compactDescriptorCore j) = []) :
    ∀ j, RepairBlank j →
      compactDescriptorBankGenerated bank (repairCompactJobs p X hG hK active s Lw Lg L) (compactDescriptorCore j) = [] := by
  intro j hj
  rw [repairCompactBank_core_keep p X hG hK active s Lw Lg L bank j (repairBlank_descriptorSource j hj)]
  exact hblank j hj

theorem repairCompactBank_targets (Lw Lg L : Fin 11 → ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4)))
    (hempty : ∀ key, bank (compactDescriptorCore (repairSetupTarget key)) = []) :
    ∀ key, compactDescriptorBankGenerated bank (repairCompactJobs p X hG hK active s Lw Lg L)
      (compactDescriptorCore (repairSetupTarget key)) = [] := by
  intro key
  rw [repairCompactBank_core_keep p X hG hK active s Lw Lg L bank _ (fun d => ?_)]
  · exact hempty key
  · rw [repairDescriptorSource_eq]
    exact (repairSetup_sources _ _).symm

end
end IntegerMultBounds.MathlibTM2.Routing
