module

public import IntegerMultBounds.Machine.NativeEndpointCharacterCopy
public import IntegerMultBounds.Machine.NativeHadamardNormalizationFactor
public import IntegerMultBounds.Machine.NativeEndpointCharacterCanonical

/-! Normalize using original runtime descriptors, without a supplied count,
normalization factor or target denominator. The retained native geometry
constructs the exact coefficient count, (slots*span+1)/2, and live plus that
increase. Shared header arithmetic reclaims every temporary descriptor. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put bank)
variable {shape : Shape}

def count (rows bits ell : ℕ) := rows*(2^bits*2^ell)
def increase (stage : Stage shape) := NativeHadamardNormalizationFactor.denominatorIncrease (stage.slots*stage.f)

def original (stage : Stage shape) (rows ell metadataPrecision live : ℕ) : State :=
  put (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision) 19 live

def counted (stage : Stage shape) (rows ell metadataPrecision live : ℕ) : State :=
  put (original stage rows ell metadataPrecision live) 20 (count rows shape.bits ell)

def scaled (stage : Stage shape) (rows ell metadataPrecision live : ℕ) : State :=
  put (counted stage rows ell metadataPrecision live) 21 (increase stage)

def targeted (stage : Stage shape) (rows ell metadataPrecision live : ℕ) : State :=
  put (scaled stage rows ell metadataPrecision live) 22 (live+increase stage)

def geometryReady (stage : Stage shape) (rows ell metadataPrecision live : ℕ) : State :=
  put (CompactSpectatorLeafSetup.state 0 shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
    stage.right stage.source.val stage.target.val) 19 live

def countSchedule : List Op :=
  [.power ![16,23] (by decide),.power ![17,24] (by decide),product ![23,24,25] (by decide),
    product ![25,4,20] (by decide),cmd (.erase 13),cmd (.erase 14),cmd (.erase 15),cmd (.erase 16),
    cmd (.erase 23),cmd (.erase 24),cmd (.erase 25)]

def increaseSchedule : List Op :=
  [product ![6,7,23] (by decide),.base (.constant 24 1),cmd (.add 23 24 (by decide)),
    .base (.constant 25 2),.base (.quotient ![23,25,21] (by decide)),
    cmd (.erase 23),cmd (.erase 24),cmd (.erase 25)]

def targetSchedule : List Op := [cmd (.copy 19 22 (by decide)),cmd (.add 22 21 (by decide))]
def cleanupSchedule : List Op := [cmd (.erase 20),cmd (.erase 21),cmd (.erase 22),cmd (.erase 19)]

theorem count_valid (stage : Stage shape) (rows ell metadataPrecision live : ℕ) (chunkPositive : 0<shape.chunk) :
    validSchedule countSchedule (geometryReady stage rows ell metadataPrecision live) := by
  simp [countSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,original,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,
    geometryReady,CompactSpectatorLeafSetup.state,put,Function.update,chunkPositive]

theorem count_eval (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    execute countSchedule (geometryReady stage rows ell metadataPrecision live)=counted stage rows ell metadataPrecision live := by
  funext port
  fin_cases port
  all_goals simp [countSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,original,counted,count,
    geometryReady,CompactSpectatorLeafSetup.state,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,put,Function.update]
  rw [Nat.mul_comm]
  simp

theorem increase_valid (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    validSchedule increaseSchedule (counted stage rows ell metadataPrecision live) := by
  have slotsPositive : 0<stage.slots := by have := stage.source.isLt; omega
  simp [increaseSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,original,counted,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,
    put,Function.update,slotsPositive]

theorem increase_eval (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    execute increaseSchedule (counted stage rows ell metadataPrecision live)=scaled stage rows ell metadataPrecision live := by
  funext port
  fin_cases port
  all_goals simp [increaseSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,original,counted,scaled,increase,
    NativeHadamardNormalizationFactor.denominatorIncrease,NativeEndpointCharacterPrepare.raw,
    CompactSpectatorLeafSetup.raw,put,Function.update]
  rw [Nat.mul_comm]

theorem target_valid (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    validSchedule targetSchedule (scaled stage rows ell metadataPrecision live) := by
  simp [targetSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,original,counted,scaled,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,
    put,Function.update]

theorem target_eval (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    execute targetSchedule (scaled stage rows ell metadataPrecision live)=targeted stage rows ell metadataPrecision live := by
  funext port
  fin_cases port
  all_goals simp [targetSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,original,counted,scaled,targeted,
    NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,put,Function.update]

def prepareProgram := seq (seq (compile (a:=2) countSchedule).2 (compile (a:=2) increaseSchedule).2)
  (compile (a:=2) targetSchedule).2

def prepareCost (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :=
  scheduleCost countSchedule (geometryReady stage rows ell metadataPrecision live)+1+
    scheduleCost increaseSchedule (counted stage rows ell metadataPrecision live)+1+
    scheduleCost targetSchedule (scaled stage rows ell metadataPrecision live)

/-- The same fixed program constructs all three normalization descriptors from
original native geometry and the true live denominator, clearing all temporary
arithmetic tapes. No descriptor-value or execution callback is supplied. -/
theorem prepare_runs (stage : Stage shape) (rows ell metadataPrecision live : ℕ) (chunkPositive : 0<shape.chunk) :
    HoareTime prepareProgram (fun storage => storage=bank (geometryReady stage rows ell metadataPrecision live))
      (fun storage => storage=bank (targeted stage rows ell metadataPrecision live))
      (prepareCost stage rows ell metadataPrecision live) := by
  have countRun := schedule_runs (a:=2) countSchedule _ (count_valid stage rows ell metadataPrecision live chunkPositive)
  have increaseRun := schedule_runs (a:=2) increaseSchedule _ (increase_valid stage rows ell metadataPrecision live)
  have targetRun := schedule_runs (a:=2) targetSchedule _ (target_valid stage rows ell metadataPrecision live)
  rw [count_eval] at countRun
  rw [increase_eval] at increaseRun
  rw [target_eval] at targetRun
  exact (countRun.seq increaseRun).seq targetRun

theorem cleanup_eval (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    execute cleanupSchedule (targeted stage rows ell metadataPrecision live)=NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision := by
  funext port
  fin_cases port
  all_goals simp [cleanupSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,original,counted,scaled,targeted,
    NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,put,Function.update]

theorem cleanup_runs (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    HoareTime (compile (a:=2) cleanupSchedule).2 (fun storage => storage=bank (targeted stage rows ell metadataPrecision live))
      (fun storage => storage=bank (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision))
      (scheduleCost cleanupSchedule (targeted stage rows ell metadataPrecision live)) := by
  have cleanupValid : validSchedule cleanupSchedule (targeted stage rows ell metadataPrecision live) := by
    simp [cleanupSchedule,validSchedule,valid,CompactChildHeadersArithmetic.valid,ActivePrefixStageHeadersOps.valid,
      ActiveRepairRankHeadersCommands.valid,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,original,counted,scaled,targeted,put,Function.update]
  have execution := schedule_runs (a:=2) cleanupSchedule _ cleanupValid
  rwa [cleanup_eval] at execution


open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)

def liveBank (live : ℕ) : Tapes 1 2 := MarkedWordCleanup.one (RadixZeroFill.encodedBinary (bits live)) 1

def input (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :=
  (bank (a:=2) (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)).append (liveBank live)

def output (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :=
  (bank (a:=2) (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)).append (liveBank (live+increase stage))

def geometry := extend (compile (a:=2) CompactSpectatorLeafSetup.geometry).2 1
def copyLive := BinaryDescriptorInstall.program 2 (43 : Fin 44) 19 (by decide)
def setup := seq geometry copyLive

def commit := seq (BinaryDescriptorCleanupList.oneProgram (a:=2) (43 : Fin 44))
  (BinaryDescriptorInstall.program 2 (22 : Fin 44) 43 (by decide))

def program := seq (seq (seq setup (extend prepareProgram 1)) commit)
  (extend (compile (a:=2) cleanupSchedule).2 1)

def setupCost (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :=
  scheduleCost CompactSpectatorLeafSetup.geometry (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)+
    1+(2*(bits live).length+5)

def cost (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :=
  setupCost stage rows ell metadataPrecision live+1+prepareCost stage rows ell metadataPrecision live+1+
    (2*(bits live).length+2*(bits (live+increase stage)).length+10)+1+
    scheduleCost cleanupSchedule (targeted stage rows ell metadataPrecision live)

theorem setup_runs (stage : Stage shape) (rows ell metadataPrecision live : ℕ)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) :
    HoareTime setup (fun storage => storage=input stage rows ell metadataPrecision live)
      (fun storage => storage=(bank (geometryReady stage rows ell metadataPrecision live)).append (liveBank live))
      (setupCost stage rows ell metadataPrecision live) := by
  have capacityPositive : 0<shape.H := by unfold Shape.H CompactGadgetReservationCapacity.capacity; positivity
  have geometryRun := schedule_runs (a:=2) CompactSpectatorLeafSetup.geometry
    (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)
    (CompactSpectatorLeafSetup.geometry_valid shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
      stage.right stage.source.val stage.target.val guardPositive axesPositive chunkPositive)
  unfold NativeEndpointCharacterPrepare.raw at geometryRun
  rw [CompactSpectatorLeafSetup.geometry_eval shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
    stage.right stage.source.val stage.target.val capacityPositive chunkPositive] at geometryRun
  let geometryState := CompactSpectatorLeafSetup.state 0 shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
    stage.right stage.source.val stage.target.val
  let geometryBank := (bank (a:=2) geometryState).append (liveBank live)
  have copyRun := BinaryDescriptorInstall.install_hoare (43 : Fin 44) 19 (by decide) geometryBank (bits live)
    (by rfl) (by rfl) (by rfl) (by rfl)
  have copyEndpoint : setTape geometryBank (19 : Fin 44) (RadixZeroFill.encodedBinary (bits live)) 1=
      (bank (geometryReady stage rows ell metadataPrecision live)).append (liveBank live) := by
    change setTape ((bank geometryState).append (liveBank live)) (Fin.castAdd 1 (Fin.castAdd 15 (19 : Fin 28))) _ _ = _
    rw [SharedPlacementAlphabet.setTape_append_left]
    change (setTape ((ActiveRepairRankHeadersCommands.caller geometryState).append (SharedBank.empty 15 2))
      (Fin.castAdd 15 (19 : Fin 28)) _ _).append _ = _
    rw [SharedPlacementAlphabet.setTape_append_left,←ActiveRepairRankHeadersCommands.put_caller]
    rfl
  rw [copyEndpoint] at copyRun
  exact (hoare_extend_eq geometryRun (liveBank live)).seq copyRun

theorem commit_runs (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    HoareTime commit
      (fun storage => storage=(bank (targeted stage rows ell metadataPrecision live)).append (liveBank live))
      (fun storage => storage=(bank (targeted stage rows ell metadataPrecision live)).append (liveBank (live+increase stage)))
      (2*(bits live).length+2*(bits (live+increase stage)).length+10) := by
  let initialBank := (bank (a:=2) (targeted stage rows ell metadataPrecision live)).append (liveBank live)
  let clearedBank := setTape initialBank (43 : Fin 44) (fun _ => blank) 0
  have clearRun := BinaryDescriptorCleanupList.one_hoare (a:=2) (43 : Fin 44) initialBank (bits live)
    (by change RadixZeroFill.encodedBinary _=BinaryDescriptorStack.descriptor _; exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)
    (by rfl)
  have copyRun := BinaryDescriptorInstall.install_hoare (22 : Fin 44) 43 (by decide) clearedBank
    (bits (live+increase stage))
    (by change (setTape initialBank (43 : Fin 44) (fun _ => blank) 0).tape 22=_
        simp only [setTape,Function.update_of_ne (by decide : (22 : Fin 44)≠43)]
        rfl)
    (by change (setTape initialBank (43 : Fin 44) (fun _ => blank) 0).head 22=_
        simp only [setTape,Function.update_of_ne (by decide : (22 : Fin 44)≠43)]
        rfl)
    (by simp [clearedBank,setTape]) (by simp [clearedBank,setTape])
  apply (clearRun.seq copyRun).consequence (fun _ equality => equality) _ (by omega)
  intro storage equality
  rw [equality]
  change setTape (setTape ((bank _).append (liveBank live)) (Fin.natAdd 43 (0 : Fin 1)) _ _) (Fin.natAdd 43 (0 : Fin 1)) _ _ = _
  rw [SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_append_right]
  congr 1
  apply Placement.Tapes.ext'
  all_goals intro port; fin_cases port; rfl

/-- Actual original native geometry and the live descriptor construct count,
normalization increase and target; the live word is physically advanced once.
All copied/generated descriptors and shared arithmetic workspace are reclaimed.
This is descriptor execution, to be joined to the coefficient normalization pass. -/
theorem runs (stage : Stage shape) (rows ell metadataPrecision live : ℕ)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) :
    HoareTime program (fun storage => storage=input stage rows ell metadataPrecision live)
      (fun storage => storage=output stage rows ell metadataPrecision live)
      (cost stage rows ell metadataPrecision live) := by
  have setupRun := setup_runs stage rows ell metadataPrecision live guardPositive axesPositive chunkPositive
  have prepareRun := hoare_extend_eq (prepare_runs stage rows ell metadataPrecision live chunkPositive) (liveBank live)
  have commitRun := commit_runs stage rows ell metadataPrecision live
  have cleanupRun := hoare_extend_eq (cleanup_runs stage rows ell metadataPrecision live) (liveBank (live+increase stage))
  exact ((setupRun.seq prepareRun).seq commitRun).seq cleanupRun

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationHeaders
