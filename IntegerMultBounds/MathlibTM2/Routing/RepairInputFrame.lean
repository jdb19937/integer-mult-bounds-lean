module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupData

/-! R2 raw configuration depends only on its source tapes. Stream permutations
therefore preserve the input contract needed by the exact primitive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {A T : ℕ} (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem SetupData.congr {cfg : SetupKey → Fin T} {wb wm B M : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {R R' : Fin T → List (Fin (A + 4))}
    (data : SetupData p X hG hK active s cfg wb wm B M headers R)
    (hkeep : ∀ key, R' (cfg key) = R (cfg key)) :
    SetupData p X hG hK active s cfg wb wm B M headers R' := by
  constructor
  · intro f; rw [hkeep]; exact data.widths f
  · intro off k; rw [hkeep]; exact data.desc off k
  · rw [hkeep]; exact data.block
  · rw [hkeep]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; rw [hkeep]; exact data.headers c k

theorem RepairSetupData.congr {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank bank' : Fin repairT → List (Fin (A + 4))}
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank)
    (hkeep : ∀ key, bank' (repairSetupSource key) = bank (repairSetupSource key)) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank' := by
  constructor
  · exact data.routing.congr p X hG hK active s (fun key => hkeep (.inl key))
  · rw [hkeep]; exact data.row
  · rw [hkeep]; exact data.descriptor
  · rw [hkeep]; exact data.keyMask
  · rw [hkeep]; exact data.badMask
  · rw [hkeep]; exact data.badPhase
  · rw [hkeep]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep]; exact data.keyLength
  · exact data.keyLength_lt

theorem repairSetup_source_src (key : RepairSetupKey) : repairSetupSource key ≠ repairHost.src := by
  cases key with
  | inl key => exact repairHost_setup.stream key
  | inr key => simp [repairSetupSource]

theorem RepairSetupData.updateStream {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairT → List (Fin (A + 4))}
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank)
    (out : List (Fin (A + 4))) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers (Function.update bank repairHost.src out) := by
  apply data.congr p X rb hG hK active s
  intro key
  exact Function.update_of_ne (repairSetup_source_src key) _ _

end IntegerMultBounds.MathlibTM2.Routing
