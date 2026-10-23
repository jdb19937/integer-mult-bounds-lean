module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorContents

/-! The compiled bank covers every descriptor and preserves every other raw
configuration input needed by R2. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem repairDescriptorKey_covers (key : RepairDescriptorKey) :
    ∃ j : Fin 11, repairDescriptorKey j = key := by
  cases key with
  | none => exact ⟨0, rfl⟩
  | some key =>
    rcases key with ⟨off, k⟩
    cases off <;> fin_cases k <;> decide +kernel

def RepairNonDescriptor : RepairSetupKey → Prop
  | .inl (.desc _ _) | .inr .keyDescriptor => False
  | _ => True

theorem repairNonDescriptor_source (key : RepairSetupKey) (hk : RepairNonDescriptor key)
    (d : RepairDescriptorKey) : repairSetupSource key ≠ repairDescriptorSource d := by
  cases key with
  | inl key =>
    cases key <;> cases d with
    | none => first | exact hk.elim | simp [repairSetupSource, repairDescriptorSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
    | some d =>
      rcases d with ⟨off, k⟩
      first | exact hk.elim | simp [repairSetupSource, repairDescriptorSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  | inr key =>
    cases key <;> cases d with
    | none => first | exact hk.elim | simp [repairSetupSource, repairDescriptorSource]
    | some d =>
      rcases d with ⟨off, k⟩
      first | exact hk.elim | simp [repairSetupSource, repairDescriptorSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

variable {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairDescriptorBank_at (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4)))
    (hblank : ∀ d, bank (descriptorCore (repairDescriptorSource d)) = []) (d : RepairDescriptorKey) :
    descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L) (descriptorCore (repairDescriptorSource d)) =
      repairDescriptorWord p X hG hK active s d := by
  obtain ⟨j, rfl⟩ := repairDescriptorKey_covers d
  rw [repairDescriptorBankContents, hblank, List.append_nil]

theorem repairDescriptorBank_keep (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4)))
    (key : RepairSetupKey) (hk : RepairNonDescriptor key) :
    descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L) (descriptorCore (repairSetupSource key)) =
      bank (descriptorCore (repairSetupSource key)) := by
  apply descriptorBankGenerated_keep
  intro job hj
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  exact descriptorCore_injective.ne (repairNonDescriptor_source key hk (repairDescriptorKey j))

end
end IntegerMultBounds.MathlibTM2.Routing
