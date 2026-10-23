module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSharedHeaders

/-! Initial repair configuration omitting all ten headers as well as masks,
width-generated fields and descriptors. Executed header generation fills it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

structure RepairPendingHeaderData (wb wm wp wk R B : ℕ)
    (bank : Fin repairT → List (Fin (A + 4))) : Prop where
  widths : ∀ f, (bank (repairRoutingConfig (.field f))).length = selectiveLen p X f
  block : bank (repairRoutingConfig .block) = binSyms wb (fieldsLen (selectiveKeyLen p X rb) + B)
  records : bank (repairRoutingConfig .records) = binSyms wm (R * 2 ^ fieldsLen (selectiveLen p X))
  block_lt : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb
  records_lt : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm
  payload : bank (repairSetupSource (.inr .payload)) = binSyms wp B
  payload_lt : B < 2 ^ wp
  keyLength : bank (repairSetupSource (.inr .keyLength)) = binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  keyLength_lt : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk

def repairHeaderRawCore (i : Fin repairT) : Fin repairHeaderT :=
  sharedHeaderCore (classifierCore (repairConfigurationCore i))

theorem repairHeaderRawCore_injective : Function.Injective repairHeaderRawCore :=
  sharedHeaderCore_injective.comp (classifierCore_injective.comp repairConfigurationCore_injective)

theorem repairHeaderPairBank_raw_keep (R B : ℕ)
    (tapes : Fin repairHeaderT → List (Fin (A + 4))) (j : Fin repairT)
    (hj : ∀ c k, j ≠ repairRoutingConfig (.header c k)) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore j) = tapes (repairHeaderRawCore j) := by
  apply repairHeaderPairBank_keep
  intro c k
  rw [repairSharedHeaderBank_header]
  exact repairHeaderRawCore_injective.ne (hj c k)

theorem repairHeaderPairBank_raw_header (R B : ℕ)
    (tapes : Fin repairHeaderT → List (Fin (A + 4))) (c : Fin 2) (k : Fin 5) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore (repairRoutingConfig (.header c k))) =
      (repairCanonicalHeaders p X rb R B c k).map bitSymbol := by
  exact repairHeaderPairBank_contents p X rb R B repairSharedHeaderBank repairSharedHeaderBank_injective
    repairSharedHeaderBank_cross tapes c k

theorem RepairPendingHeaderData.generated {wb wm wp wk R B : ℕ}
    {tapes : Fin repairHeaderT → List (Fin (A + 4))}
    (data : RepairPendingHeaderData p X rb wb wm wp wk R B (fun i => tapes (repairHeaderRawCore i))) :
    RepairPendingMaskData p X rb wb wm wp wk R B (repairCanonicalHeaders p X rb R B)
      (fun i => repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore i)) := by
  constructor
  · intro f
    rw [repairHeaderPairBank_raw_keep]
    · exact data.widths f
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [repairHeaderPairBank_raw_keep]
    · exact data.block
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [repairHeaderPairBank_raw_keep]
    · exact data.records
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; exact repairHeaderPairBank_raw_header p X rb R B tapes c k
  · rw [repairHeaderPairBank_raw_keep]
    · exact data.payload
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.payload_lt
  · rw [repairHeaderPairBank_raw_keep]
    · exact data.keyLength
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.keyLength_lt

end
end IntegerMultBounds.MathlibTM2.Routing
