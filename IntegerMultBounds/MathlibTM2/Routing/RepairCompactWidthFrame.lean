module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Width generation preserves descriptor inputs and every invariant needed
by the descriptor-generated exact repair program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ}

theorem repairCompactWidthBank_keep (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (j : Fin repairCompactT)
    (hr : j ≠ compactDescriptorCore (J := 11) (repairSetupSource (.inr .row)))
    (hm : j ≠ compactDescriptorCore (J := 11) (repairSetupSource (.inr .keyMask))) :
    repairCompactWidthBank rb wy bank ((fieldCore (N := repairCompactT)) j) = bank ((fieldCore (N := repairCompactT)) j) := by
  simp [repairCompactWidthBank, fieldPairGenerated, fieldCore_injective.eq_iff, hr, hm]

theorem repairCompactWidthBank_aux (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (i : CompactDescriptorRole 11) :
    repairCompactWidthBank rb wy bank ((fieldCore (N := repairCompactT)) ((compactDescriptorAux (N := repairT) (J := 11)) i)) = bank ((fieldCore (N := repairCompactT)) ((compactDescriptorAux (N := repairT) (J := 11)) i)) :=
  repairCompactWidthBank_keep rb wy bank _ (compactDescriptorCore_aux _ i).symm (compactDescriptorCore_aux _ i).symm

theorem repairCompactWidthBank_core (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (j : Fin repairT)
    (hr : j ≠ repairSetupSource (.inr .row)) (hm : j ≠ repairSetupSource (.inr .keyMask)) :
    repairCompactWidthBank rb wy bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) j)) = bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) j)) :=
  repairCompactWidthBank_keep rb wy bank _ ((compactDescriptorCore_injective (J := 11)).ne hr) ((compactDescriptorCore_injective (J := 11)).ne hm)

theorem repairCompactWidthBank_descriptors (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    repairCompactWidthBank rb wy bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) (repairDescriptorSource d))) =
      bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) (repairDescriptorSource d))) :=
  repairCompactWidthBank_core rb wy bank _
    (repairNonDescriptor_source (.inr .row) trivial d).symm
    (repairNonDescriptor_source (.inr .keyMask) trivial d).symm

theorem repairCompactWidthBank_targets (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairCompactWidthBank rb wy bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) (repairSetupTarget key))) =
      bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) (repairSetupTarget key))) :=
  repairCompactWidthBank_core rb wy bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem repairCompactWidthBank_blank (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    repairCompactWidthBank rb wy bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) j)) = bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) j)) :=
  repairCompactWidthBank_core rb wy bank j (repairBlank_extraSource j hj .row)
    (repairBlank_extraSource j hj .keyMask)

variable (p : Par) (X rb : ℕ)

theorem RepairPendingConfigurationData.compactWidthBank_data {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin repairCompactConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) i)))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => repairCompactWidthBank rb p.wy bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) i))) := by
  have hp : (fun i => repairCompactWidthBank rb p.wy bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) i))) =
      repairWidthBank rb p.wy (fun i => bank ((fieldCore (N := repairCompactT)) (compactDescriptorCore (J := 11) i))) := by
    funext i
    simp only [repairCompactWidthBank, fieldPairGenerated, repairWidthBank,
      Function.update_apply, fieldCore_injective.eq_iff, (compactDescriptorCore_injective (J := 11)).eq_iff]
  rw [hp]
  exact data.widthsGenerated p X rb

end
end IntegerMultBounds.MathlibTM2.Routing
