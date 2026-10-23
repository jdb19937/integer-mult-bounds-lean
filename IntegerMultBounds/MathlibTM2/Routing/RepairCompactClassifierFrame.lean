module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierPair
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactWidthFrame

/-! Generated classifiers preserve every other exact-repair input: descriptors,
widths, scratch, installation destinations and the original record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par)

def repairCompactConfigurationClassifierBank (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) :=
  repairClassifierGenerated p repairCompactConfigurationCore bank

theorem repairCompactConfigurationClassifierBank_keep
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (i : Fin repairCompactConfigurationT)
    (ht : i ≠ repairCompactConfigurationCore (repairSetupSource (.inr .badMask)))
    (hp : i ≠ repairCompactConfigurationCore (repairSetupSource (.inr .badPhase))) :
    repairCompactConfigurationClassifierBank p bank i = bank i := by
  simp [repairCompactConfigurationClassifierBank, repairClassifierGenerated, ht, hp]

theorem repairCompactConfigurationClassifierBank_core
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (i : Fin repairT)
    (ht : i ≠ repairSetupSource (.inr .badMask)) (hp : i ≠ repairSetupSource (.inr .badPhase)) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore i) = bank (repairCompactConfigurationCore i) :=
  repairCompactConfigurationClassifierBank_keep p bank _ (repairCompactConfigurationCore_injective.ne ht)
    (repairCompactConfigurationCore_injective.ne hp)

theorem repairCompactConfigurationClassifierBank_widthAux
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (i : Fin 6) :
    repairCompactConfigurationClassifierBank p bank (fieldAux i) = bank (fieldAux i) :=
  repairCompactConfigurationClassifierBank_keep p bank _ (fieldCore_aux _ i).symm (fieldCore_aux _ i).symm

theorem repairCompactConfigurationClassifierBank_compactDescriptorAux
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (i : CompactDescriptorRole 11) :
    repairCompactConfigurationClassifierBank p bank (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) i)) =
      bank (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) i)) :=
  repairCompactConfigurationClassifierBank_keep p bank _
    (fieldCore_injective.ne (compactDescriptorCore_aux _ i).symm)
    (fieldCore_injective.ne (compactDescriptorCore_aux _ i).symm)

theorem repairCompactConfigurationClassifierBank_targets
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore (repairSetupTarget key)) =
      bank (repairCompactConfigurationCore (repairSetupTarget key)) :=
  repairCompactConfigurationClassifierBank_core p bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem repairCompactConfigurationClassifierBank_blank
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (i : Fin repairT) (hi : RepairBlank i) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore i) = bank (repairCompactConfigurationCore i) :=
  repairCompactConfigurationClassifierBank_core p bank i (repairBlank_extraSource i hi .badMask)
    (repairBlank_extraSource i hi .badPhase)

theorem repairCompactConfigurationClassifierBank_descriptors
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore (repairDescriptorSource d)) =
      bank (repairCompactConfigurationCore (repairDescriptorSource d)) :=
  repairCompactConfigurationClassifierBank_core p bank _
    (repairNonDescriptor_source (.inr .badMask) trivial d).symm
    (repairNonDescriptor_source (.inr .badPhase) trivial d).symm

theorem repairCompactConfigurationClassifierBank_src
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore repairHost.src) =
      bank (repairCompactConfigurationCore repairHost.src) :=
  repairCompactConfigurationClassifierBank_core p bank _ (repairSetup_source_src _).symm (repairSetup_source_src _).symm

theorem repairCompactConfigurationClassifierBank_row
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore (repairSetupSource (.inr .row))) =
      bank (repairCompactConfigurationCore (repairSetupSource (.inr .row))) := by
  apply repairCompactConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem repairCompactConfigurationClassifierBank_keyMask
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) :
    repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore (repairSetupSource (.inr .keyMask))) =
      bank (repairCompactConfigurationCore (repairSetupSource (.inr .keyMask))) := by
  apply repairCompactConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem RepairPendingMaskData.compactConfigurationGenerated (X rb : ℕ) {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairCompactConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (repairCompactConfigurationCore i))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => repairCompactConfigurationClassifierBank p bank (repairCompactConfigurationCore i)) :=
  data.generated p X rb repairCompactConfigurationCore repairCompactConfigurationCore_injective

end
end IntegerMultBounds.MathlibTM2.Routing
