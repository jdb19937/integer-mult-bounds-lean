module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactSharedHeaders
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderData

/-! Initial repair configuration omitting all ten headers as well as masks,
width-generated fields and descriptors. Executed header generation fills it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

def repairCompactHeaderRawCore (i : Fin repairT) : Fin repairCompactHeaderT :=
  sharedHeaderCore (classifierCore (repairCompactConfigurationCore i))

theorem repairCompactHeaderRawCore_injective : Function.Injective repairCompactHeaderRawCore :=
  sharedHeaderCore_injective.comp (classifierCore_injective.comp repairCompactConfigurationCore_injective)

theorem repairCompactHeaderPairBank_raw_keep (R B : ℕ)
    (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (j : Fin repairT)
    (hj : ∀ c k, j ≠ repairRoutingConfig (.header c k)) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore j) = tapes (repairCompactHeaderRawCore j) := by
  apply repairHeaderPairBank_keep
  intro c k
  rw [repairCompactSharedHeaderBank_header]
  exact repairCompactHeaderRawCore_injective.ne (hj c k)

theorem repairCompactHeaderPairBank_raw_header (R B : ℕ)
    (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (c : Fin 2) (k : Fin 5) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore (repairRoutingConfig (.header c k))) =
      (repairCanonicalHeaders p X rb R B c k).map bitSymbol := by
  exact repairHeaderPairBank_contents p X rb R B repairCompactSharedHeaderBank repairCompactSharedHeaderBank_injective
    repairCompactSharedHeaderBank_cross tapes c k

theorem RepairPendingHeaderData.compactGenerated {wb wm wp wk R B : ℕ}
    {tapes : Fin repairCompactHeaderT → List (Fin (A + 4))}
    (data : RepairPendingHeaderData p X rb wb wm wp wk R B (fun i => tapes (repairCompactHeaderRawCore i))) :
    RepairPendingMaskData p X rb wb wm wp wk R B (repairCanonicalHeaders p X rb R B)
      (fun i => repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore i)) := by
  constructor
  · intro f
    rw [repairCompactHeaderPairBank_raw_keep]
    · exact data.widths f
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [repairCompactHeaderPairBank_raw_keep]
    · exact data.block
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [repairCompactHeaderPairBank_raw_keep]
    · exact data.records
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; exact repairCompactHeaderPairBank_raw_header p X rb R B tapes c k
  · rw [repairCompactHeaderPairBank_raw_keep]
    · exact data.payload
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.payload_lt
  · rw [repairCompactHeaderPairBank_raw_keep]
    · exact data.keyLength
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.keyLength_lt

end
end IntegerMultBounds.MathlibTM2.Routing
