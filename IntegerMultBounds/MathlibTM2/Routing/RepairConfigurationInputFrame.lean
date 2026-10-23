module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationData
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationWidths

/-! Placement changes only the stream. All binary compiler inputs, scratch and
remaining raw configuration for combined exact repair are independent of it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairConfigurationCore (i : Fin repairT) : Fin repairConfigurationT :=
  fieldCore (N := repairDescriptorT) (descriptorCore (J := 11) i)

theorem repairConfigurationCore_injective : Function.Injective repairConfigurationCore :=
  fieldCore_injective.comp (descriptorCore_injective (J := 11))

theorem repairConfigurationSource_src (key : RepairSetupKey) :
    repairConfigurationCore (repairSetupSource key) ≠ repairConfigurationCore repairHost.src :=
  repairConfigurationCore_injective.ne (repairSetup_source_src key)

theorem repairConfigurationAux_src (i : Fin 6) :
    fieldAux i ≠ repairConfigurationCore repairHost.src :=
  (fieldCore_aux (descriptorCore (J := 11) repairHost.src) i).symm

theorem repairConfigurationDescriptorAux_src (i : Fin (2 * 11 + 12)) :
    fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i) ≠
      repairConfigurationCore repairHost.src :=
  fieldCore_injective.ne (descriptorCore_aux repairHost.src i).symm

theorem repairConfigurationDescriptorReg_src (j : Fin 11) (r : BinaryMaskReg) :
    fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) j r) ≠
      repairConfigurationCore repairHost.src :=
  fieldCore_injective.ne (descriptorCore_reg repairHost.src j r).symm

theorem repairConfigurationSelectors_src (j : Fin 11) :
    fieldCore (N := repairDescriptorT) (descriptorBankSelectors (N := repairT) j) ≠
      repairConfigurationCore repairHost.src :=
  repairConfigurationDescriptorAux_src ⟨11 + j.val, by omega⟩

variable {A : ℕ} (p : Par) (X rb : ℕ)

theorem RepairPendingConfigurationData.congr {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank bank' : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers bank)
    (hkeep : ∀ key, bank' (repairSetupSource key) = bank (repairSetupSource key)) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers bank' := by
  constructor
  · intro f; rw [show bank' (repairRoutingConfig (.field f)) = bank (repairRoutingConfig (.field f)) from hkeep (.inl (.field f))]; exact data.widths f
  · rw [show bank' (repairRoutingConfig .block) = bank (repairRoutingConfig .block) from hkeep (.inl .block)]; exact data.block
  · rw [show bank' (repairRoutingConfig .records) = bank (repairRoutingConfig .records) from hkeep (.inl .records)]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; rw [show bank' (repairRoutingConfig (.header c k)) = bank (repairRoutingConfig (.header c k)) from hkeep (.inl (.header c k))]; exact data.headers c k
  · rw [hkeep]; exact data.badMask
  · rw [hkeep]; exact data.badPhase
  · rw [hkeep]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep]; exact data.keyLength
  · exact data.keyLength_lt

theorem RepairPendingConfigurationData.updateConfigurationStream {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers (fun i => bank (repairConfigurationCore i)))
    (out : List (Fin (A + 4))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => Function.update bank (repairConfigurationCore repairHost.src) out (repairConfigurationCore i)) := by
  apply data.congr p X rb
  intro key
  exact Function.update_of_ne (repairConfigurationSource_src key) _ _

end
end IntegerMultBounds.MathlibTM2.Routing
