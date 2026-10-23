module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierPair
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationFrame

/-! Generated classifiers preserve every other exact-repair input: descriptors,
widths, scratch, installation destinations and the original record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par)

def repairConfigurationClassifierBank (bank : Fin repairConfigurationT → List (Fin (A + 4))) :=
  repairClassifierGenerated p repairConfigurationCore bank

theorem repairConfigurationClassifierBank_keep
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (i : Fin repairConfigurationT)
    (ht : i ≠ repairConfigurationCore (repairSetupSource (.inr .badMask)))
    (hp : i ≠ repairConfigurationCore (repairSetupSource (.inr .badPhase))) :
    repairConfigurationClassifierBank p bank i = bank i := by
  simp [repairConfigurationClassifierBank, repairClassifierGenerated, ht, hp]

theorem repairConfigurationClassifierBank_core
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (i : Fin repairT)
    (ht : i ≠ repairSetupSource (.inr .badMask)) (hp : i ≠ repairSetupSource (.inr .badPhase)) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore i) = bank (repairConfigurationCore i) :=
  repairConfigurationClassifierBank_keep p bank _ (repairConfigurationCore_injective.ne ht)
    (repairConfigurationCore_injective.ne hp)

theorem repairConfigurationClassifierBank_widthAux
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (i : Fin 6) :
    repairConfigurationClassifierBank p bank (fieldAux i) = bank (fieldAux i) :=
  repairConfigurationClassifierBank_keep p bank _ (fieldCore_aux _ i).symm (fieldCore_aux _ i).symm

theorem repairConfigurationClassifierBank_descriptorAux
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (i : Fin (2 * 11 + 12)) :
    repairConfigurationClassifierBank p bank (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i)) =
      bank (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i)) :=
  repairConfigurationClassifierBank_keep p bank _
    (fieldCore_injective.ne (descriptorCore_aux _ i).symm)
    (fieldCore_injective.ne (descriptorCore_aux _ i).symm)

theorem repairConfigurationClassifierBank_descriptorReg
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (j : Fin 11) (r : BinaryMaskReg) :
    repairConfigurationClassifierBank p bank (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j r)) =
      bank (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j r)) :=
  repairConfigurationClassifierBank_keep p bank _
    (fieldCore_injective.ne (descriptorCore_reg _ j r).symm)
    (fieldCore_injective.ne (descriptorCore_reg _ j r).symm)

theorem repairConfigurationClassifierBank_selectors
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (j : Fin 11) :
    repairConfigurationClassifierBank p bank (fieldCore (N := repairDescriptorT) (descriptorBankSelectors (N := repairT) (J := 11) j)) =
      bank (fieldCore (N := repairDescriptorT) (descriptorBankSelectors (N := repairT) (J := 11) j)) :=
  repairConfigurationClassifierBank_descriptorAux p bank ⟨11 + j.val, by omega⟩

theorem repairConfigurationClassifierBank_targets
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore (repairSetupTarget key)) =
      bank (repairConfigurationCore (repairSetupTarget key)) :=
  repairConfigurationClassifierBank_core p bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem repairConfigurationClassifierBank_blank
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (i : Fin repairT) (hi : RepairBlank i) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore i) = bank (repairConfigurationCore i) :=
  repairConfigurationClassifierBank_core p bank i (repairBlank_extraSource i hi .badMask)
    (repairBlank_extraSource i hi .badPhase)

theorem repairConfigurationClassifierBank_descriptors
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore (repairDescriptorSource d)) =
      bank (repairConfigurationCore (repairDescriptorSource d)) :=
  repairConfigurationClassifierBank_core p bank _
    (repairNonDescriptor_source (.inr .badMask) trivial d).symm
    (repairNonDescriptor_source (.inr .badPhase) trivial d).symm

theorem repairConfigurationClassifierBank_src
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore repairHost.src) =
      bank (repairConfigurationCore repairHost.src) :=
  repairConfigurationClassifierBank_core p bank _ (repairSetup_source_src _).symm (repairSetup_source_src _).symm

theorem repairConfigurationClassifierBank_row
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore (repairSetupSource (.inr .row))) =
      bank (repairConfigurationCore (repairSetupSource (.inr .row))) := by
  apply repairConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem repairConfigurationClassifierBank_keyMask
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) :
    repairConfigurationClassifierBank p bank (repairConfigurationCore (repairSetupSource (.inr .keyMask))) =
      bank (repairConfigurationCore (repairSetupSource (.inr .keyMask))) := by
  apply repairConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem RepairPendingMaskData.configurationGenerated (X rb : ℕ) {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (repairConfigurationCore i))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => repairConfigurationClassifierBank p bank (repairConfigurationCore i)) :=
  data.generated p X rb repairConfigurationCore repairConfigurationCore_injective

end
end IntegerMultBounds.MathlibTM2.Routing
