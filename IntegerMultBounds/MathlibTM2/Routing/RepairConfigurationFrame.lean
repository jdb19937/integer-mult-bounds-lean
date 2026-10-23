module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Width generation preserves descriptor inputs and every invariant needed
by the descriptor-generated exact repair program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ}

theorem repairConfigurationWidthBank_keep (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (j : Fin repairDescriptorT)
    (hr : j ≠ descriptorCore (J := 11) (repairSetupSource (.inr .row)))
    (hm : j ≠ descriptorCore (J := 11) (repairSetupSource (.inr .keyMask))) :
    repairConfigurationWidthBank rb wy bank ((fieldCore (N := repairDescriptorT)) j) = bank ((fieldCore (N := repairDescriptorT)) j) := by
  simp [repairConfigurationWidthBank, fieldPairGenerated, fieldCore_injective.eq_iff, hr, hm]

theorem repairConfigurationWidthBank_aux (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (i : Fin (2 * 11 + 12)) :
    repairConfigurationWidthBank rb wy bank ((fieldCore (N := repairDescriptorT)) ((descriptorAux (N := repairT) (J := 11)) i)) = bank ((fieldCore (N := repairDescriptorT)) ((descriptorAux (N := repairT) (J := 11)) i)) :=
  repairConfigurationWidthBank_keep rb wy bank _ (descriptorCore_aux _ i).symm (descriptorCore_aux _ i).symm

theorem repairConfigurationWidthBank_core (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (j : Fin repairT)
    (hr : j ≠ repairSetupSource (.inr .row)) (hm : j ≠ repairSetupSource (.inr .keyMask)) :
    repairConfigurationWidthBank rb wy bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) j)) = bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) j)) :=
  repairConfigurationWidthBank_keep rb wy bank _ ((descriptorCore_injective (J := 11)).ne hr) ((descriptorCore_injective (J := 11)).ne hm)

theorem repairConfigurationWidthBank_descriptors (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    repairConfigurationWidthBank rb wy bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) (repairDescriptorSource d))) =
      bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) (repairDescriptorSource d))) :=
  repairConfigurationWidthBank_core rb wy bank _
    (repairNonDescriptor_source (.inr .row) trivial d).symm
    (repairNonDescriptor_source (.inr .keyMask) trivial d).symm

theorem repairConfigurationWidthBank_targets (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairConfigurationWidthBank rb wy bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) (repairSetupTarget key))) =
      bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) (repairSetupTarget key))) :=
  repairConfigurationWidthBank_core rb wy bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem repairConfigurationWidthBank_blank (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    repairConfigurationWidthBank rb wy bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) j)) = bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) j)) :=
  repairConfigurationWidthBank_core rb wy bank j (repairBlank_extraSource j hj .row)
    (repairBlank_extraSource j hj .keyMask)

variable (p : Par) (X rb : ℕ)

theorem RepairPendingConfigurationData.widthBank_data {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin repairConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) i)))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => repairConfigurationWidthBank rb p.wy bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) i))) := by
  have hp : (fun i => repairConfigurationWidthBank rb p.wy bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) i))) =
      repairWidthBank rb p.wy (fun i => bank ((fieldCore (N := repairDescriptorT)) (descriptorCore (J := 11) i))) := by
    funext i
    simp only [repairConfigurationWidthBank, fieldPairGenerated, repairWidthBank,
      Function.update_apply, fieldCore_injective.eq_iff, (descriptorCore_injective (J := 11)).eq_iff]
  rw [hp]
  exact data.widthsGenerated p X rb

end
end IntegerMultBounds.MathlibTM2.Routing
