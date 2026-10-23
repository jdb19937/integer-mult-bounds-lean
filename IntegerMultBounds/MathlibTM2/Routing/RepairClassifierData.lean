module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationData

/-! Configuration input with both classifier masks omitted in addition to the
row, key mask and descriptors. Executed mask generation fills this contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

structure RepairPendingMaskData (wb wm wp wk R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4))) : Prop where
  widths : ∀ f, (bank (repairRoutingConfig (.field f))).length = selectiveLen p X f
  block : bank (repairRoutingConfig .block) = binSyms wb (fieldsLen (selectiveKeyLen p X rb) + B)
  records : bank (repairRoutingConfig .records) = binSyms wm (R * 2 ^ fieldsLen (selectiveLen p X))
  block_lt : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb
  records_lt : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm
  headers : ∀ c k, bank (repairRoutingConfig (.header c k)) = (headers c k).map bitSymbol
  payload : bank (repairSetupSource (.inr .payload)) = binSyms wp B
  payload_lt : B < 2 ^ wp
  keyLength : bank (repairSetupSource (.inr .keyLength)) = binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  keyLength_lt : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk


def repairClassifierBank (bank : Fin repairT → List (Fin (A + 4))) :=
  Function.update (Function.update bank (repairSetupSource (.inr .badMask)) (binSyms (p.wy + 1) (mAV p)))
    (repairSetupSource (.inr .badPhase)) (binSyms (p.wy + 1) (mkV p))

theorem repairClassifierBank_routing (bank : Fin repairT → List (Fin (A + 4))) (key : SetupKey) :
    repairClassifierBank p bank (repairRoutingConfig key) = bank (repairRoutingConfig key) := by
  simp [repairClassifierBank, repairRoutingConfig, placedSelectiveConfig, repairSetupSource, repairRoutingRole]

theorem RepairPendingMaskData.complete {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers bank) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers (repairClassifierBank p bank) := by
  constructor
  · intro f; rw [repairClassifierBank_routing]; exact data.widths f
  · rw [repairClassifierBank_routing]; exact data.block
  · rw [repairClassifierBank_routing]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; rw [repairClassifierBank_routing]; exact data.headers c k
  · simp [repairClassifierBank, repairSetupSource]
  · simp [repairClassifierBank]
  · simpa [repairClassifierBank, repairSetupSource] using data.payload
  · exact data.payload_lt
  · simpa [repairClassifierBank, repairSetupSource] using data.keyLength
  · exact data.keyLength_lt

/-- Generating the two raw masks preserves every other physical tape. -/
def repairClassifierGenerated {N : ℕ} (core : Fin repairT → Fin N)
    (bank : Fin N → List (Fin (A + 4))) :=
  Function.update (Function.update bank (core (repairSetupSource (.inr .badMask))) (binSyms (p.wy + 1) (mAV p)))
    (core (repairSetupSource (.inr .badPhase))) (binSyms (p.wy + 1) (mkV p))

theorem repairClassifierGenerated_project {N : ℕ} (core : Fin repairT → Fin N)
    (hcore : Function.Injective core) (bank : Fin N → List (Fin (A + 4))) :
    (fun i => repairClassifierGenerated p core bank (core i)) =
      repairClassifierBank p (fun i => bank (core i)) := by
  funext i
  simp only [repairClassifierGenerated, repairClassifierBank, Function.update_apply, hcore.eq_iff]

theorem RepairPendingMaskData.generated {N : ℕ} (core : Fin repairT → Fin N)
    (hcore : Function.Injective core) {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin N → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (core i))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => repairClassifierGenerated p core bank (core i)) := by
  rw [repairClassifierGenerated_project p core hcore]
  exact data.complete p X rb

end
end IntegerMultBounds.MathlibTM2.Routing
