module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledFrames

/-! Reusable event boundaries retain the actual entry target and settled
saved stacks. These invariants support local event constructors without
assuming existence of a complete recursive execution. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventFrameState
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexSourceReadyReachedEventTrace (State)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots)
open Networks.ComplexRecursiveCallSchema (Call)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount

section Node
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume entryReturned childExponent : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Call}

local notation "NodeState" => State (stage:=stage) (rowCount:=rowCount)
  (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
  (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant)
  (completedAxes:=completedAxes) (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels)
  (frameVolume:=frameVolume) (entryReturned:=entryReturned) (childExponent:=childExponent)
  (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)

/-- The target is the literal value captured at entry; the snapshot refers to
actual protected stack ports, not a supplied completed execution. -/
structure FrameState (snapshot : Snapshot stackCount) (savedTarget eventIndex live : ℕ) where
  state : NodeState eventIndex live
  targetRetained : state.reached.targetValue=savedTarget
  settled : Settled snapshot state.reached.storage state.reached.aux

local notation "NodeBoundary" => FrameState (stage:=stage) (rowCount:=rowCount)
  (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
  (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant)
  (completedAxes:=completedAxes) (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels)
  (frameVolume:=frameVolume) (entryReturned:=entryReturned) (childExponent:=childExponent)
  (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)

/-- Capture the actual current bank and the fixed stack ports. -/
def capture {eventIndex live : ℕ} (state : NodeState eventIndex live)
    (headerStack liveStack : Fin stackCount) : Snapshot stackCount :=
  ⟨headerStack,liveStack,pcStack,state.reached.storage,state.reached.aux⟩

/-- Genuine clean current tails initialize the reusable boundary. Auxiliary
cleanliness comes from Reached's real blank-after invariant. -/
def captured {eventIndex live : ℕ} (state : NodeState eventIndex live)
    (headerStack liveStack : Fin stackCount)
    (protectedTails : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,state.reached.storage.head storagePort≤cell → state.reached.storage.tape storagePort cell=blank) :
    NodeBoundary (capture state headerStack liveStack) state.reached.targetValue eventIndex live :=
  ⟨state,rfl,CompactComplexSourceReadySettledFrames.captured_settled
    (capture state headerStack liveStack) protectedTails state.reached.aux_free⟩

/-- Settled gives the exact clean tails at the current physical heads. -/
theorem FrameState.protected_tails {snapshot : Snapshot stackCount} {savedTarget eventIndex live : ℕ}
    (boundary : FrameState (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      snapshot savedTarget eventIndex live) :
    ∀ storagePort,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack storagePort →
      ∀ cell,boundary.state.reached.storage.head storagePort≤cell →
        boundary.state.reached.storage.tape storagePort cell=blank :=
  CompactComplexSourceReadySettledFrames.storage_clean_current boundary.settled

/-- A genuine output with restored stacks and retained target advances the
same reusable boundary; the numerical target never follows the live cursor. -/
def advance {snapshot : Snapshot stackCount} {savedTarget eventIndex sourceLive targetLive : ℕ}
    (before : FrameState (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      snapshot savedTarget eventIndex sourceLive)
    (after : NodeState (eventIndex+1) targetLive)
    (targetRetained : after.reached.targetValue=before.state.reached.targetValue)
    (settled : Settled snapshot after.reached.storage after.reached.aux) :
    NodeBoundary snapshot savedTarget (eventIndex+1) targetLive :=
  ⟨after,targetRetained.trans before.targetRetained,settled⟩

/-- The original saved-target certificate is reusable at every reached event,
without constructing a fictitious dependency Path at its advanced counter. -/
def FrameState.saved_ledger {snapshot : Snapshot stackCount} {savedTarget eventIndex live ledgerLive ledgerLeft ledgerExponent : ℕ}
    (boundary : FrameState (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      snapshot savedTarget eventIndex live)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      savedTarget ledgerLeft ledgerExponent) :
    CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      boundary.state.reached.targetValue ledgerLeft ledgerExponent := by
  rw [boundary.targetRetained]
  exact ledger

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventFrameState
