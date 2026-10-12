module

public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames

/-! The literal saved child-entry snapshot has clean upper stack tails.
Descriptor pushes derive header/live/target cleanliness, genuine saved-PC
association derives the PC tail, and payload parking retains the reached
parent's free auxiliary suffix. No recursive execution assumption is used. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedSettledFrames
noncomputable section
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots descriptor_push_clean)
open CompactComplexSourceReadyCapturedChildFrames (snapshot childOutput)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexChildHeadersData (parent)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyChildEntryPath (selected)
open RecursiveChildQuotientsConstant (bits)
variable {stackTapeCount : ℕ} {shape : CompactGadgetReservationShape.Shape} {leftBoundary childExponent : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

/-- Three chronological descriptor pushes leave a clean upper tail at their
actual computed new header-stack head. -/
theorem headers_push_clean (olderStackWord : ℤ → Fin 6) (olderStackHead : ℤ) (headerDescriptors : Fin 3 → List Bool)
    (olderTailClean : ∀ cell,olderStackHead≤cell → olderStackWord cell=blank) :
    ∀ cell,CompactChildHeadersStack.top olderStackHead headerDescriptors≤cell → CompactChildHeadersStack.frames olderStackWord olderStackHead headerDescriptors cell=blank := by
  have firstPushClean := descriptor_push_clean olderStackWord olderStackHead (headerDescriptors 0) olderTailClean
  have secondPushClean := descriptor_push_clean (BinaryDescriptorStack.frame olderStackWord olderStackHead (headerDescriptors 0))
    (CompactChildHeadersStack.next olderStackHead (headerDescriptors 0)) (headerDescriptors 1) firstPushClean
  have thirdPushClean := descriptor_push_clean
    (BinaryDescriptorStack.frame (BinaryDescriptorStack.frame olderStackWord olderStackHead (headerDescriptors 0))
      (CompactChildHeadersStack.next olderStackHead (headerDescriptors 0)) (headerDescriptors 1))
    (CompactChildHeadersStack.next (CompactChildHeadersStack.next olderStackHead (headerDescriptors 0)) (headerDescriptors 1)) (headerDescriptors 2) secondPushClean
  exact thirdPushClean

/-- Actual master and inactive-role parking preserves the clean tail above
its computed stack head, independently of the parked role contents. -/
theorem parked_clean {roleCount : ℕ} (selectedRole : Fin roleCount) (shape : CompactGadgetReservationShape.Shape)
    (rowCount logColumns metadataP rowCoordinate leftBoundary blockCount slotCount rightBoundary sourceRow targetRow : ℕ)
    (inputBank : Tapes (CompactComplexNonleafRoleEntry.tapes stackTapeCount roleCount) 2)
    (inputTailClean : CompactComplexSourceReadyPrefixReadiness.BlankAfter inputBank CompactComplexNonleafRoleEntry.stack) :
    CompactComplexSourceReadyPrefixReadiness.BlankAfter
      (CompactComplexNonleafRoleEntry.output selectedRole shape rowCount logColumns metadataP rowCoordinate leftBoundary blockCount slotCount rightBoundary sourceRow targetRow inputBank)
      CompactComplexNonleafRoleEntry.stack := by
  intro cell beyondNewStackHead
  have newStackHead := CompactComplexNonleafRoleEntry.output_stack_head selectedRole shape rowCount logColumns metadataP
    rowCoordinate leftBoundary blockCount slotCount rightBoundary sourceRow targetRow inputBank
  rw [newStackHead] at beyondNewStackHead
  rw [CompactComplexNonleafRoleEntry.output_stack_outside selectedRole shape rowCount logColumns metadataP
    rowCoordinate leftBoundary blockCount slotCount rightBoundary sourceRow targetRow inputBank cell (Or.inr beyondNewStackHead)]
  exact inputTailClean cell (by omega)

section Reached
variable {levelCount frameCount returnedVolume rowCount logColumns metadataPrecision basePrecision growthConstant axesUsed baselinePrecision scalarPrefix parentLive : ℕ}
    (rowCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+2))
    (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackTapeCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackTapeCount roles) 2}
    (parentReached : Reached (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision (childExponent+2) basePrecision growthConstant axesUsed
      baselinePrecision levelCount frameCount returnedVolume scalarPrefix parentLive pcStack stackOrigin savedCalls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackTapeCount)

private theorem caller_storage (storagePort : Fin (10+stackTapeCount)) :
    (caller parentReached).head (CompactComplexNonleafRoleReturnFrame.oldSlot storagePort)=parentReached.storage.head storagePort ∧
    (caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot storagePort)=parentReached.storage.tape storagePort := by
  have callerPrefix := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux (CompactComplexSpectatorTargetBank.oldSlot storagePort)
  have storageBankPort := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload storagePort
  exact ⟨callerPrefix.1.trans storageBankPort.1,callerPrefix.2.trans storageBankPort.2⟩

/-- The actual captured PC tail is clean because the fixed origin and pushed
original call code give its genuine physical stack history. -/
theorem snapshot_pc_clean (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    ∀ cell,(snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).storage.head (Fin.natAdd 10 pcStack)≤cell →
      (snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).storage.tape (Fin.natAdd 10 pcStack) cell=blank := by
  have parentPcHistory := CompactComplexAlignedReturnedDormantFrames.parent_saved_associated parentReached
  have callerPort := caller_storage rowCoordinate visit activeFitsAxes pair parentReached (Fin.natAdd 10 pcStack)
  rw [←callerPort.1,←callerPort.2] at parentPcHistory
  have pushed := CompactComplexSourceReadySavedCallHistory.child_entry_push call rowCoordinate visit activeFitsAxes pair
    rowCount logColumns metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack pcDistinctHeader pcDistinctLive stackOrigin savedCalls parentPcHistory
  exact CompactComplexSavedStackTailInvariant.history_tail
    (CompactComplexSourceReadySavedCallHistory.physical pushed)

/-- Actual payload parking has a clean suffix at the captured auxiliary newStackHead,
derived from the reached parent's reusable stack rather than newly assumed. -/
theorem snapshot_aux_clean :
    ∀ cell,(snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).aux.head 0≤cell →
      (snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).aux.tape 0 cell=blank := by
  have callerPort := CompactComplexSourceReadyScalarChildReadiness.entry_aux
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux 0
  change (caller parentReached).head CompactComplexNonleafRoleEntry.stack=parentReached.aux.head 0 ∧
    (caller parentReached).tape CompactComplexNonleafRoleEntry.stack=parentReached.aux.tape 0 at callerPort
  have callerStackFree : CompactComplexSourceReadyPrefixReadiness.BlankAfter (caller parentReached)
      CompactComplexNonleafRoleEntry.stack := by
    intro cell beyondStackHead
    rw [callerPort.2]
    exact parentReached.aux_free cell (by rwa [callerPort.1] at beyondStackHead)
  have parkedTailClean := parked_clean (selected call) shape rowCount logColumns metadataPrecision
    (parent rowCoordinate visit activeFitsAxes pair).rho (parent rowCoordinate visit activeFitsAxes pair).left
    (parent rowCoordinate visit activeFitsAxes pair).f (parent rowCoordinate visit activeFitsAxes pair).slots
    (parent rowCoordinate visit activeFitsAxes pair).right (parent rowCoordinate visit activeFitsAxes pair).source.val
    (parent rowCoordinate visit activeFitsAxes pair).target.val (caller parentReached) callerStackFree
  have capturedPayloadPorts := CompactComplexSourceReadyCapturedChildFrames.snapshot_payload
    rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
  intro cell beyondStackHead
  rw [capturedPayloadPorts.2]
  exact parkedTailClean cell (by rwa [capturedPayloadPorts.1] at beyondStackHead)

/-- Every protected upper tail in the actual post-save snapshot is clean.
Only the parent's header/live/target clean tails are required; saved-PC
cleanliness follows from genuine chronological history. -/
theorem snapshot_storage_clean
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    (parentProtectedTailsClean : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,parentReached.storage.head storagePort≤cell → parentReached.storage.tape storagePort cell=blank) :
    ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,(snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).storage.head storagePort≤cell →
        (snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).storage.tape storagePort cell=blank := by
  intro storagePort portProtected cell beyondStackHead
  rcases portProtected with rfl|rfl|rfl|rfl
  · have capturedHeaderPorts := CompactComplexSourceReadyCapturedChildFrames.snapshot_headers
      rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack pcDistinctHeader.symm headerDistinctLive
    rw [capturedHeaderPorts.2]
    exact headers_push_clean _ _ _ (parentProtectedTailsClean _ (Or.inl rfl)) cell (by rwa [capturedHeaderPorts.1] at beyondStackHead)
  · have capturedLivePorts := CompactComplexSourceReadyCapturedChildFrames.snapshot_live
      rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack headerDistinctLive.symm pcDistinctLive.symm
    rw [capturedLivePorts.2]
    exact descriptor_push_clean _ _ _ (parentProtectedTailsClean _ (Or.inr (Or.inl rfl))) cell (by rwa [capturedLivePorts.1] at beyondStackHead)
  · exact snapshot_pc_clean rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack pcDistinctHeader pcDistinctLive cell beyondStackHead
  · have capturedTargetPorts := CompactComplexSourceReadyCapturedChildFrames.snapshot_target
      rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
    rw [capturedTargetPorts.2]
    exact descriptor_push_clean _ _ _ (parentProtectedTailsClean _ (Or.inr (Or.inr (Or.inr rfl)))) cell (by rwa [capturedTargetPorts.1] at beyondStackHead)

/-- The actual child-entry snapshot starts Settled, including derived clean
reference tails for all saved descriptors, PC code and parked payload. -/
theorem snapshot_settled
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    (parentProtectedTailsClean : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,parentReached.storage.head storagePort≤cell → parentReached.storage.tape storagePort cell=blank) :
    let capturedSnapshot := snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
    Settled capturedSnapshot capturedSnapshot.storage capturedSnapshot.aux := by
  dsimp only
  apply CompactComplexSourceReadySettledFrames.captured_settled
  · exact snapshot_storage_clean rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack headerDistinctLive pcDistinctHeader pcDistinctLive parentProtectedTailsClean
  · exact snapshot_aux_clean rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack

/-- An ancestor Settled invariant provides exactly the clean parent tails
needed to initialize the next actual saved child snapshot. -/
theorem snapshot_settled_from_parent
    (ancestorSnapshot : Snapshot stackTapeCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    let capturedSnapshot := snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
    Settled capturedSnapshot capturedSnapshot.storage capturedSnapshot.aux := by
  apply snapshot_settled rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack headerDistinctLive pcDistinctHeader pcDistinctLive
  intro storagePort portProtected cell beyondStackHead
  have ancestorPortProtected : protectedSlots ancestorSnapshot.headerStack ancestorSnapshot.liveStack ancestorSnapshot.pcStack storagePort := by
    rwa [snapshotHeaderStack,snapshotLiveStack,snapshotPcStack]
  exact parentSettled.storage_clean storagePort ancestorPortProtected cell (by rwa [←parentSettled.storage_heads storagePort ancestorPortProtected])

end Reached

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedSettledFrames
