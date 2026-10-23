module

public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFields
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame

/-! R2 input data with the row and key mask omitted. Executed width generation
supplies exactly these two missing fields, rather than assuming their raw words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

structure RepairPendingWidthData (wb wm wp wk R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4))) : Prop where
  routing : SetupData p X hG hK active s repairRoutingConfig wb wm
    (fieldsLen (selectiveKeyLen p X rb) + B) (R * 2 ^ fieldsLen (selectiveLen p X)) headers bank
  descriptor : bank (repairSetupSource (.inr .keyDescriptor)) =
    (patternTable (selectiveKeyPattern p X active s)).flatten.map bitSymbol
  badMask : bank (repairSetupSource (.inr .badMask)) = binSyms (p.wy + 1) (mAV p)
  badPhase : bank (repairSetupSource (.inr .badPhase)) = binSyms (p.wy + 1) (mkV p)
  payload : bank (repairSetupSource (.inr .payload)) = binSyms wp B
  payload_lt : B < 2 ^ wp
  keyLength : bank (repairSetupSource (.inr .keyLength)) = binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  keyLength_lt : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk

theorem RepairPendingWidthData.congr {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank bank' : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingWidthData p X rb hG hK active s wb wm wp wk R B headers bank)
    (hkeep : ∀ key, bank' (repairSetupSource key) = bank (repairSetupSource key)) :
    RepairPendingWidthData p X rb hG hK active s wb wm wp wk R B headers bank' := by
  constructor
  · exact data.routing.congr p X hG hK active s (fun key => hkeep (.inl key))
  · rw [hkeep]; exact data.descriptor
  · rw [hkeep]; exact data.badMask
  · rw [hkeep]; exact data.badPhase
  · rw [hkeep]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep]; exact data.keyLength
  · exact data.keyLength_lt

def repairWidthBank (rb wy : ℕ) (bank : Fin repairT → List (Fin (A + 4))) :=
  Function.update (Function.update bank (repairSetupSource (.inr .row)) (binSyms rb 0))
    (repairSetupSource (.inr .keyMask)) (binSyms wy (maskVal wy id))

theorem repairWidthBank_routing (rb wy : ℕ) (bank : Fin repairT → List (Fin (A + 4)))
    (key : SetupKey) : repairWidthBank rb wy bank (repairRoutingConfig key) = bank (repairRoutingConfig key) := by
  simp [repairWidthBank, repairRoutingConfig, placedSelectiveConfig, repairSetupSource, repairRoutingRole]

theorem RepairPendingWidthData.complete {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingWidthData p X rb hG hK active s wb wm wp wk R B headers bank) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers (repairWidthBank rb p.wy bank) := by
  constructor
  · exact data.routing.congr p X hG hK active s (repairWidthBank_routing rb p.wy bank)
  · simp [repairWidthBank, repairSetupSource]
  · simpa [repairWidthBank, repairSetupSource] using data.descriptor
  · simp [repairWidthBank]
  · simpa [repairWidthBank, repairSetupSource] using data.badMask
  · simpa [repairWidthBank, repairSetupSource] using data.badPhase
  · simpa [repairWidthBank, repairSetupSource] using data.payload
  · exact data.payload_lt
  · simpa [repairWidthBank, repairSetupSource] using data.keyLength
  · exact data.keyLength_lt

/-- Restrict the literal generated host bank to R2's core registers. -/
theorem repairWidthBank_project (rb wy : ℕ)
    (bank : Fin (repairT + 6) → List (Fin (A + 4))) :
    (fun i => (Function.update (Function.update bank (fieldCore (repairSetupSource (.inr .row)))
      (binSyms rb 0)) (fieldCore (repairSetupSource (.inr .keyMask)))
      (binSyms wy (maskVal wy id))) (fieldCore i)) =
      repairWidthBank rb wy (fun i => bank (fieldCore i)) := by
  funext i
  simp only [repairWidthBank, Function.update_apply, fieldCore_injective.eq_iff]

theorem RepairPendingWidthData.generated {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin (repairT + 6) → List (Fin (A + 4))}
    (data : RepairPendingWidthData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => bank (fieldCore i))) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => (Function.update (Function.update bank (fieldCore (repairSetupSource (.inr .row)))
        (binSyms rb 0)) (fieldCore (repairSetupSource (.inr .keyMask)))
        (binSyms p.wy (maskVal p.wy id))) (fieldCore i)) := by
  rw [repairWidthBank_project]
  exact data.complete p X rb hG hK active s

end
end IntegerMultBounds.MathlibTM2.Routing
