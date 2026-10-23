module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactBank
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorFrame

/-! The compiled bank covers every descriptor and preserves every other raw
configuration input needed by R2. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairCompactBank_at (Lw Lg L : Fin 11 → ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4)))
    (hblank : ∀ d, bank (compactDescriptorCore (repairDescriptorSource d)) = []) (d : RepairDescriptorKey) :
    compactDescriptorBankGenerated bank (repairCompactJobs p X hG hK active s Lw Lg L) (compactDescriptorCore (repairDescriptorSource d)) =
      repairDescriptorWord p X hG hK active s d := by
  obtain ⟨j, rfl⟩ := repairDescriptorKey_covers d
  rw [repairCompactBank_contents, hblank, List.append_nil]

theorem repairCompactBank_keep (Lw Lg L : Fin 11 → ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4)))
    (key : RepairSetupKey) (hk : RepairNonDescriptor key) :
    compactDescriptorBankGenerated bank (repairCompactJobs p X hG hK active s Lw Lg L) (compactDescriptorCore (repairSetupSource key)) =
      bank (compactDescriptorCore (repairSetupSource key)) := by
  apply compactDescriptorBankGenerated_keep
  intro job hj
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  exact compactDescriptorCore_injective.ne (repairNonDescriptor_source key hk (repairDescriptorKey j))

end
end IntegerMultBounds.MathlibTM2.Routing
