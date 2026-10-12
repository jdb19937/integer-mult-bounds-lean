module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant

/-! Genuine initial event states are constructed from original corrected
node-entry coefficients and literal input ports. The emitted arrays and bank
are computed by corrected source entry; no Reached or semantic oracle is an
input. Saving target8 retains every designated dormant stack's clean tail. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNodeEntry
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedEventTrace (State)
open CompactComplexSourceReadyReachedDormantFrameInvariant (protectedSlots)
variable {stackTapeCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  Networks.ComplexFramedExecution.rows CompactComplexDenominatorCapacity.scalarRows

private theorem cursor_zero (entryReturned childVolume : ℕ) :
    CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned 0 childVolume=entryReturned := by
  simp only [CompactComplexSourceReadySiblingGuards.returnedCursor,List.take_zero,
    CompactComplexCompletedLiveLower.childNames,List.length_nil,Nat.zero_mul,Nat.add_zero]

private theorem scalar_cursor_zero :
    (CompactComplexActualScalarOrdinal.scalarGroups (CompactComplexCompletedLiveLower.schedule.take 0)).length=0 := by
  simp only [List.take_zero,CompactComplexActualScalarOrdinal.scalarGroups,
    CompactComplexScheduledPCLayout.scalarGroups,List.length_nil]

/-- Cursor-index transport retains actual coefficient and physical fields;
proofs are checked over symbolic indices before concrete schedule cursors. -/
private theorem reindex_cursors
    {stage : ActivePrefixStageParameters.Stage shape}
    {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      dependencyLevels frameVolume originalReturned originalPrefix initialLive : ℕ}
    {pcStack : Fin stackTapeCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {inputBank : Tapes (nodeTapes stackTapeCount roles) 2}
    (originalReached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume originalReturned originalPrefix initialLive pcStack stackOrigin savedCalls inputBank)
    (nextReturned nextPrefix : ℕ) (returnedEquation : nextReturned=originalReturned) (prefixEquation : nextPrefix=originalPrefix) :
    ∃ nextReached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume nextReturned nextPrefix initialLive pcStack stackOrigin savedCalls inputBank,
      nextReached.data=originalReached.data ∧ nextReached.storage=originalReached.storage ∧ nextReached.aux=originalReached.aux := by
  subst nextReturned
  subst nextPrefix
  exact ⟨originalReached,rfl,rfl,rfl⟩

private theorem protected_not_target (headerStack liveStack pcStack : Fin stackTapeCount)
    (storagePort : Fin (10+stackTapeCount))
    (portProtected : protectedSlots headerStack liveStack pcStack storagePort) : storagePort.val≠8 := by
  rcases portProtected with rfl|rfl|rfl|rfl <;> simp only [Fin.val_natAdd] <;> omega

/-- Literal corrected source entry supplies the zero-cursor Reached witness,
its actual emitted arrays and canonical bank, and inherited clean stack tails. -/
theorem initial_state {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
    (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=CompactComplexRecursiveGeometry.arity)
    (rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ)
    (rolesDivideRows : roles∣rowCount) (originalCoefficients : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+1) dependencyLevels frameVolume entryReturned)
    (precisionFits : baselinePrecision ≤ inputPrecision)
    (dependencyFitsChunk : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant ≤ shape.chunk)
    (originalWidth : CompactSpectatorInheritedGrid.Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (originalGrid : CompactSpectatorInheritedGrid.Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)) originalCoefficients)
    (controlBank : Tapes 43 2) (queueBank : Tapes 1 2) (scalarHeaders : ActiveRepairRankHeadersCommands.State)
    (tailBank : Tapes 22 2) (originalStorage : Tapes (10+stackTapeCount) 2) (auxiliaryBank : Tapes 2 2)
    (countBlank : originalStorage.head ⟨0,by omega⟩=0 ∧ originalStorage.tape ⟨0,by omega⟩=(fun _ => blank))
    (currentReady : originalStorage.head ⟨7,by omega⟩=1 ∧ originalStorage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits initialLive))
    (clockBlank : auxiliaryBank.head 1=0 ∧ auxiliaryBank.tape 1=(fun _ => blank))
    (auxiliaryFree : CompactComplexSourceReadyPrefixReadiness.BlankAfter auxiliaryBank 0)
    (exponentReady : controlBank.head 1=1 ∧ controlBank.tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (childExponent+1)))
    (control28Blank : controlBank.head 28=0 ∧ controlBank.tape 28=(fun _ => blank))
    (control29Blank : controlBank.head 29=0 ∧ controlBank.tape 29=(fun _ => blank))
    (initialLedger : initialLive ≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (pcStack : Fin stackTapeCount) (stackOrigin : ℤ) (savedCalls : List Networks.ComplexRecursiveCallSchema.Call)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls
      (originalStorage.tape (Fin.natAdd 10 pcStack)) (originalStorage.head (Fin.natAdd 10 pcStack)))
    (headerStack liveStack : Fin stackTapeCount)
    (originalProtectedTails : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,originalStorage.head storagePort ≤ cell → originalStorage.tape storagePort cell=blank) :
    let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
    let permanentBank := CompactComplexCorrectedEntryGeometryReadiness.permanent stage stageSlots rowCount polynomialExponent
      metadataPrecision initialLive childExponent rolesDivideRows originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage
    ∃ initialState : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant)
      (completedAxes:=0) (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent) (pcStack:=pcStack) (origin:=stackOrigin) (savedCalls:=savedCalls)
      0 initialLive,
      initialState.bank=canonical permanentBank auxiliaryBank ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array stage stageSlots rowCount
        polynomialExponent metadataPrecision rolesDivideRows originalCoefficients (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
      (∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
        ∀ cell,initialState.reached.storage.head storagePort ≤ cell → initialState.reached.storage.tape storagePort cell=blank) := by
  dsimp only
  obtain ⟨initialReached,emittedData⟩ := CompactComplexSourceReadyReachedEventInvariant.initial stage stageSlots
    rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive rolesDivideRows originalCoefficients
    entryPath precisionFits dependencyFitsChunk originalWidth originalGrid controlBank queueBank scalarHeaders tailBank originalStorage
    auxiliaryBank countBlank currentReady clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger pcStack stackOrigin
    savedCalls savedAssociated
  obtain ⟨cursorReached,dataRetained,storageRetained,_⟩ := reindex_cursors initialReached
    (CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned 0 (CompactComplexRecursiveGeometry.arity^childExponent))
    (CompactComplexActualScalarOrdinal.scalarGroups (CompactComplexCompletedLiveLower.schedule.take 0)).length
    (cursor_zero entryReturned _) scalar_cursor_zero
  let initialState : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=stackOrigin) (savedCalls:=savedCalls) 0 initialLive := {
    inRange := Nat.zero_le _
    bank := canonical (CompactComplexCorrectedEntryGeometryReadiness.permanent stage stageSlots rowCount polynomialExponent
      (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) initialLive childExponent rolesDivideRows originalCoefficients
      controlBank queueBank scalarHeaders tailBank originalStorage) auxiliaryBank
    reached := cursorReached }
  obtain ⟨storageFields,_⟩ := CompactComplexSourceReadySettledEventInvariant.canonical_fields initialReached _ auxiliaryBank rfl
  simp only [CompactComplexCorrectedEntryGeometryReadiness.permanent,
    CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at storageFields
  refine ⟨initialState,rfl,?_,?_⟩
  · exact dataRetained.trans emittedData
  · intro storagePort portProtected cell beyondHead
    change cursorReached.storage.tape storagePort cell=blank
    change cursorReached.storage.head storagePort ≤ cell at beyondHead
    rw [storageRetained,storageFields] at beyondHead ⊢
    have retainedPort := CompactComplexCorrectedEntryGeometryReadiness.storage_other originalStorage
      (initialLive+2*CompactComplexRecursiveGeometry.arity^(childExponent+1)) storagePort
      (protected_not_target headerStack liveStack pcStack storagePort portProtected)
    rw [retainedPort.1] at beyondHead
    rw [retainedPort.2]
    exact originalProtectedTails storagePort portProtected cell beyondHead

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNodeEntry
