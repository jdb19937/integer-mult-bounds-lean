module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorFrame

/-! The initial R2 contract omits all eleven raw descriptors. Actual descriptor
compilation establishes the complete existing setup-data contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

structure RepairPendingDescriptorData (wb wm wp wk R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4))) : Prop where
  widths : ∀ f, (bank (repairRoutingConfig (.field f))).length = selectiveLen p X f
  block : bank (repairRoutingConfig .block) = binSyms wb (fieldsLen (selectiveKeyLen p X rb) + B)
  records : bank (repairRoutingConfig .records) = binSyms wm (R * 2 ^ fieldsLen (selectiveLen p X))
  block_lt : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb
  records_lt : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm
  headers : ∀ c k, bank (repairRoutingConfig (.header c k)) = (headers c k).map bitSymbol
  row : (bank (repairSetupSource (.inr .row))).length = rb
  keyMask : bank (repairSetupSource (.inr .keyMask)) = binSyms p.wy (maskVal p.wy id)
  badMask : bank (repairSetupSource (.inr .badMask)) = binSyms (p.wy + 1) (mAV p)
  badPhase : bank (repairSetupSource (.inr .badPhase)) = binSyms (p.wy + 1) (mkV p)
  payload : bank (repairSetupSource (.inr .payload)) = binSyms wp B
  payload_lt : B < 2 ^ wp
  keyLength : bank (repairSetupSource (.inr .keyLength)) = binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  keyLength_lt : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk

theorem RepairPendingDescriptorData.generated {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} (L : Fin 11 → ℕ)
    {bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))}
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => bank (descriptorCore i)))
    (hblank : ∀ d, bank (descriptorCore (repairDescriptorSource d)) = []) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L) (descriptorCore i)) := by
  have hkeep := repairDescriptorBank_keep p X hG hK active s L bank
  constructor
  · constructor
    · intro f
      change (descriptorBankGenerated _ _ (descriptorCore (repairSetupSource (.inl (.field f))))).length = _
      rw [hkeep (.inl (.field f)) trivial]; exact data.widths f
    · intro off k
      exact repairDescriptorBank_at p X hG hK active s L bank hblank (some (off, k))
    · change descriptorBankGenerated _ _ (descriptorCore (repairSetupSource (.inl .block))) = _
      rw [hkeep (.inl .block) trivial]; exact data.block
    · change descriptorBankGenerated _ _ (descriptorCore (repairSetupSource (.inl .records))) = _
      rw [hkeep (.inl .records) trivial]; exact data.records
    · exact data.block_lt
    · exact data.records_lt
    · intro c k
      change descriptorBankGenerated _ _ (descriptorCore (repairSetupSource (.inl (.header c k)))) = _
      rw [hkeep (.inl (.header c k)) trivial]; exact data.headers c k
  · rw [hkeep (.inr .row) trivial]; exact data.row
  · exact repairDescriptorBank_at p X hG hK active s L bank hblank none
  · rw [hkeep (.inr .keyMask) trivial]; exact data.keyMask
  · rw [hkeep (.inr .badMask) trivial]; exact data.badMask
  · rw [hkeep (.inr .badPhase) trivial]; exact data.badPhase
  · rw [hkeep (.inr .payload) trivial]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep (.inr .keyLength) trivial]; exact data.keyLength
  · exact data.keyLength_lt

end
end IntegerMultBounds.MathlibTM2.Routing
