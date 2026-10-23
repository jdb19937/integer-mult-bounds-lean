module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationInputFrame

/-! Core and auxiliary embeddings for compact configuration generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable section

def repairCompactConfigurationCore (i : Fin repairT) : Fin repairCompactConfigurationT :=
  fieldCore (N := repairCompactT) (compactDescriptorCore (J := 11) i)

theorem repairCompactConfigurationCore_injective : Function.Injective repairCompactConfigurationCore :=
  fieldCore_injective.comp (compactDescriptorCore_injective (J := 11))

theorem repairCompactConfigurationSource_src (key : RepairSetupKey) :
    repairCompactConfigurationCore (repairSetupSource key) ≠ repairCompactConfigurationCore repairHost.src :=
  repairCompactConfigurationCore_injective.ne (repairSetup_source_src key)

theorem repairCompactConfigurationAux_src (i : Fin 6) :
    fieldAux i ≠ repairCompactConfigurationCore repairHost.src :=
  (fieldCore_aux (compactDescriptorCore (J := 11) repairHost.src) i).symm

theorem repairCompactConfigurationDescriptorAux_src (i : CompactDescriptorRole 11) :
    fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) i) ≠
      repairCompactConfigurationCore repairHost.src :=
  fieldCore_injective.ne (compactDescriptorCore_aux repairHost.src i).symm


end
end IntegerMultBounds.MathlibTM2.Routing
