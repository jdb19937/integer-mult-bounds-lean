module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorBank
public import IntegerMultBounds.MathlibTM2.Routing.DescriptorBankContents

/-! Every actual R2 descriptor register receives exactly its intended table.
No generated table overwrites another, and every auxiliary tape is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem repairDescriptorSource_injective :
    Function.Injective (fun j : Fin 11 => repairDescriptorSource (repairDescriptorKey j)) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (simp [repairDescriptorSource, repairDescriptorKey, repairSetupSource,
        repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at he)

variable {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairDescriptorBankContents (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))) (j : Fin 11) :
    descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L)
      (descriptorCore (repairDescriptorSource (repairDescriptorKey j))) =
      repairDescriptorWord p X hG hK active s (repairDescriptorKey j) ++
        bank (descriptorCore (repairDescriptorSource (repairDescriptorKey j))) := by
  rw [← repairDescriptorIndices_word p X hG hK active s]
  exact descriptorBankContents _ repairDescriptorSource_injective _ _ _ bank j

theorem repairDescriptorBankAux_keep (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))) (i : Fin (2 * 11 + 12)) :
    descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L) (descriptorAux i) =
      bank (descriptorAux i) :=
  descriptorBankAux_keep _ _ _ _ bank i

end
end IntegerMultBounds.MathlibTM2.Routing
