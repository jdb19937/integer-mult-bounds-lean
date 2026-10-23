module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierBank

/-! Placement may change the record stream while all mask-free configuration
inputs remain ready. Binary classifier dimensions are also independent of it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

theorem RepairPendingMaskData.congr {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank bank' : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers bank)
    (hkeep : ∀ key, bank' (repairSetupSource key) = bank (repairSetupSource key)) :
    RepairPendingMaskData p X rb wb wm wp wk R B headers bank' := by
  constructor
  · intro f; rw [show bank' (repairRoutingConfig (.field f)) = bank (repairRoutingConfig (.field f)) from hkeep (.inl (.field f))]; exact data.widths f
  · rw [show bank' (repairRoutingConfig .block) = bank (repairRoutingConfig .block) from hkeep (.inl .block)]; exact data.block
  · rw [show bank' (repairRoutingConfig .records) = bank (repairRoutingConfig .records) from hkeep (.inl .records)]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; rw [show bank' (repairRoutingConfig (.header c k)) = bank (repairRoutingConfig (.header c k)) from hkeep (.inl (.header c k))]; exact data.headers c k
  · rw [hkeep]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep]; exact data.keyLength
  · exact data.keyLength_lt

theorem RepairPendingMaskData.updateClassifierStream {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairClassifierT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (classifierCore (repairConfigurationCore i))))
    (out : List (Fin (A + 4))) :
    RepairPendingMaskData p X rb wb wm wp wk R B headers
      (fun i => Function.update bank (classifierCore (repairConfigurationCore repairHost.src)) out (classifierCore (repairConfigurationCore i))) := by
  apply data.congr p X rb
  intro key
  exact Function.update_of_ne (classifierCore_injective.ne (repairConfigurationSource_src key)) _ _

theorem classifierDimension_updateStream (bank : Fin repairClassifierT → List (Fin (A + 4)))
    (out : List (Fin (A + 4))) (i : Fin 16) :
    Function.update bank (classifierCore (repairConfigurationCore repairHost.src)) out (classifierAux i) =
      bank (classifierAux i) :=
  Function.update_of_ne (classifierCore_aux _ i).symm _ _

end
end IntegerMultBounds.MathlibTM2.Routing
