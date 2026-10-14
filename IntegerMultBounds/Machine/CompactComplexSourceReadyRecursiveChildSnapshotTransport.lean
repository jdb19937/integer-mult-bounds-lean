module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildReadiness
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant

/-! The actual corrected child entry changes only target eight. Its saved
stack and parked-payload references therefore transport a completed child
Settled invariant back to the original physical child-entry snapshot. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildSnapshotTransport
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyRecursiveChildCleanTails (childStorage childAuxiliary)
open CompactComplexSourceReadySiblingChildInvariant (childPublic)
open CompactComplexSourceReadyRecursiveChildReadiness (childControl childQueue childTail)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

private theorem protected_not_target {stackCount : ℕ} (headerStack liveStack pcStack : Fin stackCount)
    (storagePort : Fin (10+stackCount)) (protectedPort : protectedSlots headerStack liveStack pcStack storagePort) :
    storagePort.val≠8 := by
  rcases protectedPort with headerPort|livePort|pcPort|targetStackPort
  all_goals subst storagePort
  all_goals simp only [Fin.val_natAdd]
  all_goals omega

/-- The literal corrected entry's real saved ports and auxiliary bank agree
with the actual original storage; only unprotected target eight was installed. -/
theorem corrected_entry_reference_ports
    {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {rows ell metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      levels frames returned scalarPrefix live : ℕ}
    {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {actualBank : Tapes (nodeTapes stackCount roles) 2}
    (initialReached : Reached stage rows ell metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes
      baselineLive levels frames returned scalarPrefix live pcStack origin savedCalls actualBank)
    (headerStack liveStack : Fin stackCount) (stageSlots : stage.slots=arity)
    (initialLive childExponent : ℕ) (rolesDivide : roles∣rows)
    (original : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (oldStorage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2)
    (entryBank : actualBank=canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent stage stageSlots rows ell metadataPrecision
        initialLive childExponent rolesDivide original control queue scalar tail oldStorage) auxiliary) :
    (∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      initialReached.storage.head storagePort=oldStorage.head storagePort ∧
      initialReached.storage.tape storagePort=oldStorage.tape storagePort) ∧ initialReached.aux=auxiliary := by
  obtain ⟨storageFields,auxiliaryFields⟩ :=
    CompactComplexSourceReadySettledEventInvariant.canonical_fields initialReached _ auxiliary entryBank
  simp only [CompactComplexCorrectedEntryGeometryReadiness.permanent,
    CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at storageFields
  refine ⟨?_,auxiliaryFields⟩
  intro storagePort protectedPort
  rw [storageFields]
  exact CompactComplexCorrectedEntryGeometryReadiness.storage_other oldStorage
    (initialLive+2*arity^(childExponent+1)) storagePort
    (protected_not_target headerStack liveStack pcStack storagePort protectedPort)

/-- Transport reference snapshots using exact protected ports and the parked
payload tape. Cleanliness of the actual destination reference is supplied by
its own genuine captured Settled invariant. -/
theorem settled_reference_transfer {stackCount : ℕ}
    (correctedSnapshot originalSnapshot : Snapshot stackCount)
    (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2)
    (completedSettled : Settled correctedSnapshot storage auxiliary)
    (originalSettled : Settled originalSnapshot originalSnapshot.storage originalSnapshot.aux)
    (headerStackEqual : correctedSnapshot.headerStack=originalSnapshot.headerStack)
    (liveStackEqual : correctedSnapshot.liveStack=originalSnapshot.liveStack)
    (pcStackEqual : correctedSnapshot.pcStack=originalSnapshot.pcStack)
    (referencePorts : ∀ storagePort,protectedSlots originalSnapshot.headerStack originalSnapshot.liveStack
      originalSnapshot.pcStack storagePort →
      correctedSnapshot.storage.head storagePort=originalSnapshot.storage.head storagePort ∧
      correctedSnapshot.storage.tape storagePort=originalSnapshot.storage.tape storagePort)
    (auxiliaryPorts : correctedSnapshot.aux.head 0=originalSnapshot.aux.head 0 ∧
      correctedSnapshot.aux.tape 0=originalSnapshot.aux.tape 0) :
    Settled originalSnapshot storage auxiliary := by
  apply CompactComplexSourceReadySettledFrames.settled_of_port_eq originalSettled
  · intro storagePort protectedPort
    have correctedProtected : protectedSlots correctedSnapshot.headerStack correctedSnapshot.liveStack
        correctedSnapshot.pcStack storagePort := by
      rw [headerStackEqual,liveStackEqual,pcStackEqual]
      exact protectedPort
    have completedPorts := CompactComplexSourceReadyReachedDormantFrameInvariant.settled_storage
      completedSettled storagePort correctedProtected
    exact ⟨completedPorts.1.trans (referencePorts storagePort protectedPort).1,
      completedPorts.2.trans (referencePorts storagePort protectedPort).2⟩
  · have completedPorts := CompactComplexSourceReadyReachedDormantFrameInvariant.settled_aux completedSettled
    exact ⟨completedPorts.1.trans auxiliaryPorts.1,completedPorts.2.trans auxiliaryPorts.2⟩

section Child
variable {stackCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex parentRows polynomialExponent
    metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
    metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) scalarPrefix parentLive pcStack origin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- Actual-child specialization: the completed corrected-node witness settles
against the original physically saved child bank, with no captured-bank oracle. -/
theorem settled_on_actual_child_snapshot
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack)
    (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack) (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    {initialChildBank : Tapes (nodeTapes stackCount roles) 2}
    {childLevels childFrames childReturned childPrefix childLive : ℕ}
    (initialReached : Reached (child phaseCoordinate parentPath.visit activeFits pair call.slot)
      (parentRows/roles) polynomialExponent metadataPrecision (childExponent+1) baselinePrecision growthConstant 0
      baselineLive childLevels childFrames childReturned childPrefix childLive pcStack origin (call::savedCalls) initialChildBank)
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=arity)
    (childRolesDivide : roles∣parentRows/roles)
    (entryBank : initialChildBank=canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent
        (child phaseCoordinate parentPath.visit activeFits pair call.slot) childSlots (parentRows/roles) polynomialExponent
        metadataPrecision parentLive childExponent childRolesDivide
        (CompactComplexSourceReadyOrientationInvariants.oriented call
          (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call))
        (childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) parentReached.scalar
        (childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
      (childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
    (finalStorage : Tapes (10+stackCount) 2) (finalAuxiliary : Tapes 2 2)
    (finalSettled : Settled
      (⟨headerStack,liveStack,pcStack,initialReached.storage,initialReached.aux⟩ : Snapshot stackCount)
      finalStorage finalAuxiliary) :
    Settled
      (CompactComplexSourceReadyCapturedChildFrames.capture headerStack pcStack liveStack
        (childPublic phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
      finalStorage finalAuxiliary := by
  obtain ⟨referencePorts,auxiliaryEqual⟩ := corrected_entry_reference_ports initialReached headerStack liveStack childSlots
    parentLive childExponent childRolesDivide
    (CompactComplexSourceReadyOrientationInvariants.oriented call
      (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call))
    (childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) parentReached.scalar
    (childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack) entryBank
  have actualChildSettled := CompactComplexSourceReadyRecursiveChildCleanTails.child_settled
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerDistinctLive pcDistinctHeader pcDistinctLive
  exact settled_reference_transfer _ _ finalStorage finalAuxiliary finalSettled actualChildSettled rfl rfl rfl referencePorts
    ⟨congrArg (fun bank : Tapes 2 2 => bank.head 0) auxiliaryEqual,
      congrArg (fun bank : Tapes 2 2 => bank.tape 0) auxiliaryEqual⟩

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildSnapshotTransport
