module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorData
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthData

/-! Initial configuration omitting both the eleven descriptors and the raw
row/key mask. Width generation establishes the descriptor-free contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

structure RepairPendingConfigurationData (wb wm wp wk R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4))) : Prop where
  widths : ∀ f, (bank (repairRoutingConfig (.field f))).length = selectiveLen p X f
  block : bank (repairRoutingConfig .block) = binSyms wb (fieldsLen (selectiveKeyLen p X rb) + B)
  records : bank (repairRoutingConfig .records) = binSyms wm (R * 2 ^ fieldsLen (selectiveLen p X))
  block_lt : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb
  records_lt : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm
  headers : ∀ c k, bank (repairRoutingConfig (.header c k)) = (headers c k).map bitSymbol
  badMask : bank (repairSetupSource (.inr .badMask)) = binSyms (p.wy + 1) (mAV p)
  badPhase : bank (repairSetupSource (.inr .badPhase)) = binSyms (p.wy + 1) (mkV p)
  payload : bank (repairSetupSource (.inr .payload)) = binSyms wp B
  payload_lt : B < 2 ^ wp
  keyLength : bank (repairSetupSource (.inr .keyLength)) = binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  keyLength_lt : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk

theorem RepairPendingConfigurationData.widthsGenerated {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers bank) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers (repairWidthBank rb p.wy bank) := by
  constructor
  · intro f; rw [repairWidthBank_routing]; exact data.widths f
  · rw [repairWidthBank_routing]; exact data.block
  · rw [repairWidthBank_routing]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; rw [repairWidthBank_routing]; exact data.headers c k
  · simp [repairWidthBank, repairSetupSource]
  · simp [repairWidthBank]
  · simpa [repairWidthBank, repairSetupSource] using data.badMask
  · simpa [repairWidthBank, repairSetupSource] using data.badPhase
  · simpa [repairWidthBank, repairSetupSource] using data.payload
  · exact data.payload_lt
  · simpa [repairWidthBank, repairSetupSource] using data.keyLength
  · exact data.keyLength_lt

/-- The row and mask updates inside the concrete descriptor bank. -/
def repairConfigurationWidths (rb wy : ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))) :=
  Function.update (Function.update bank (descriptorCore (repairSetupSource (.inr .row))) (binSyms rb 0))
    (descriptorCore (repairSetupSource (.inr .keyMask))) (binSyms wy (maskVal wy id))

theorem repairConfigurationWidths_project (rb wy : ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))) :
    (fun i => repairConfigurationWidths rb wy bank (descriptorCore i)) =
      repairWidthBank rb wy (fun i => bank (descriptorCore i)) := by
  funext i
  simp only [repairConfigurationWidths, repairWidthBank, Function.update_apply, descriptorCore_injective.eq_iff]

theorem RepairPendingConfigurationData.descriptorsGenerated {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} (L : Fin 11 → ℕ)
    {bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank (descriptorCore i)))
    (hblank : ∀ d, bank (descriptorCore (J := 11) (repairDescriptorSource d)) = []) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => descriptorBankGenerated (repairConfigurationWidths rb p.wy bank)
        (repairDescriptorJobs p X hG hK active s L) (descriptorCore i)) := by
  have hw : RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => repairConfigurationWidths rb p.wy bank (descriptorCore i)) := by
    rw [repairConfigurationWidths_project]
    exact data.widthsGenerated p X rb
  apply hw.generated p X rb hG hK active s L
  intro d
  have hr : descriptorCore (J := 11) (repairDescriptorSource d) ≠ descriptorCore (repairSetupSource (.inr .row)) :=
    (descriptorCore_injective (J := 11)).ne (repairNonDescriptor_source (.inr .row) trivial d).symm
  have hm : descriptorCore (J := 11) (repairDescriptorSource d) ≠ descriptorCore (repairSetupSource (.inr .keyMask)) :=
    (descriptorCore_injective (J := 11)).ne (repairNonDescriptor_source (.inr .keyMask) trivial d).symm
  simpa only [repairConfigurationWidths, Function.update_of_ne hr, Function.update_of_ne hm] using hblank d

end
end IntegerMultBounds.MathlibTM2.Routing
