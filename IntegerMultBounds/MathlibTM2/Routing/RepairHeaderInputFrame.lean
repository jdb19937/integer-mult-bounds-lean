module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderData

/-! Header-free configuration and generator inputs survive stream placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

theorem RepairPendingHeaderData.congr {wb wm wp wk R B : ℕ}
    {bank bank' : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingHeaderData p X rb wb wm wp wk R B bank)
    (hkeep : ∀ key, bank' (repairSetupSource key) = bank (repairSetupSource key)) :
    RepairPendingHeaderData p X rb wb wm wp wk R B bank' := by
  constructor
  · intro f; rw [show bank' (repairRoutingConfig (.field f)) = bank (repairRoutingConfig (.field f)) from hkeep (.inl (.field f))]; exact data.widths f
  · rw [show bank' (repairRoutingConfig .block) = bank (repairRoutingConfig .block) from hkeep (.inl .block)]; exact data.block
  · rw [show bank' (repairRoutingConfig .records) = bank (repairRoutingConfig .records) from hkeep (.inl .records)]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · rw [hkeep]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep]; exact data.keyLength
  · exact data.keyLength_lt

theorem RepairPendingHeaderData.updateHeaderStream {wb wm wp wk R B : ℕ}
    {bank : Fin repairHeaderT → List (Fin (A + 4))}
    (data : RepairPendingHeaderData p X rb wb wm wp wk R B (fun i => bank (repairHeaderRawCore i)))
    (out : List (Fin (A + 4))) :
    RepairPendingHeaderData p X rb wb wm wp wk R B
      (fun i => Function.update bank (repairHeaderRawCore repairHost.src) out (repairHeaderRawCore i)) := by
  apply data.congr p X rb
  intro key
  have hraw : repairSetupSource key ≠ repairHost.src := by
    intro he
    exact repairConfigurationSource_src key (congrArg repairConfigurationCore he)
  have hne : repairHeaderRawCore (repairSetupSource key) ≠ repairHeaderRawCore repairHost.src :=
    repairHeaderRawCore_injective.ne hraw
  exact Function.update_of_ne hne _ _

theorem headerWork_updateStream (bank : Fin repairHeaderT → List (Fin (A + 4)))
    (out : List (Fin (A + 4))) (r : HeaderWorkRole) :
    Function.update bank (repairHeaderRawCore repairHost.src) out (sharedHeaderWork r) =
      bank (sharedHeaderWork r) :=
  Function.update_of_ne (sharedHeaderCore_work _ r).symm _ _

end
end IntegerMultBounds.MathlibTM2.Routing
