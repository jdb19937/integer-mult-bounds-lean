module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedSettledFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCount
public import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsFrame

/-! Source orientation and actual stopped-leaf return retain every captured
stack port and payload-stack auxiliary cell before the saved-PC pop. The
advanced current word and erased target are unprotected numeric ports. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedSettledFrames
noncomputable section
open CompactComplexNonleafRoleChildBank (tapes storage current target)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots)
open CompactComplexSourceReadyOrientedControlsFrame (output)
open CompactComplexSourceReadyStoppedLeafCount (returned)
variable {stackTapeCount roleCount coefficientCount : ℕ}

private theorem storage_ne_source (port : Fin (10+stackTapeCount)) :
    storage (s:=stackTapeCount) (c:=roleCount) port≠CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro portsEqual
  have portIndicesEqual := congrArg Fin.val portsEqual
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at portIndicesEqual
  omega

private theorem extra_ne_source (port : Fin 2) :
    extra (s:=stackTapeCount) (c:=roleCount) port≠CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro portsEqual
  have portIndicesEqual := congrArg Fin.val portsEqual
  simp only [extra,CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at portIndicesEqual
  unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at portIndicesEqual
  omega

private theorem extra_ne_storage (port : Fin 2) (storagePort : Fin (10+stackTapeCount)) :
    extra (s:=stackTapeCount) (c:=roleCount) port≠storage storagePort := by
  intro portsEqual
  have portIndicesEqual := congrArg Fin.val portsEqual
  have storagePortBound := storagePort.isLt
  simp only [extra,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portIndicesEqual
  unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at portIndicesEqual
  omega

private theorem storage_injective : Function.Injective (storage (s:=stackTapeCount) (c:=roleCount)) := by
  intro port storagePort portsEqual
  apply Fin.ext
  have portIndicesEqual := congrArg Fin.val portsEqual
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portIndicesEqual
  omega

private theorem protected_ne_target (snapshot : Snapshot stackTapeCount) (port : Fin (10+stackTapeCount))
    (portProtected : protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack port) :
    port≠⟨8,by omega⟩ := by
  rcases portProtected with rfl|rfl|rfl|rfl <;>
    intro portsEqual <;> have portIndicesEqual := congrArg Fin.val portsEqual <;> simp only [Fin.val_natAdd] at portIndicesEqual <;> omega

/-- Pre-leaf orientation only touches source, preserving complete protected
storage ports and the older payload-stack auxiliary pair. -/
theorem oriented_settled (snapshot : Snapshot stackTapeCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (tapes stackTapeCount roleCount) 2) (payloadData : Fin coefficientCount → ButterflyStreamData.Coefficient)
    (framesSettled : Settled snapshot (SharedBank.payload inputBank storage) (SharedBank.payload inputBank extra)) :
    Settled snapshot (SharedBank.payload (output call inputBank payloadData) storage)
      (SharedBank.payload (output call inputBank payloadData) extra) := by
  apply CompactComplexSourceReadySettledFrames.settled_of_port_eq framesSettled
  · intro port _
    exact CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank payloadData (storage port) (storage_ne_source port)
  · exact CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank payloadData (extra 0) (extra_ne_source 0)

/-- A literal stopped return only writes source, current7 and target8. -/
theorem returned_frame (inputBank : Tapes (tapes stackTapeCount roleCount) 2) (payloadData : ℤ → Fin 6) (returnedLive : ℕ)
    (port : Fin (tapes stackTapeCount roleCount)) (portDistinctSource : port≠CompactComplexSourceReadyOrientedControlsFrame.source)
    (portDistinctCurrent : port≠current) (portDistinctTarget : port≠target) :
    (returned inputBank payloadData returnedLive).head port=inputBank.head port ∧ (returned inputBank payloadData returnedLive).tape port=inputBank.tape port := by
  change port≠CompactComplexSourceReadyLeafPhase.source (s:=10+stackTapeCount) at portDistinctSource
  simp only [returned,SharedPlacementAlphabet.setTape,Function.update_of_ne portDistinctSource,
    Function.update_of_ne portDistinctCurrent,Function.update_of_ne portDistinctTarget,and_self]

/-- Captured frameCount stay Settled through actual leaf termination, before the
subsequent saved-PC pop consumes that captured caller'stackTapeCount own PC code. -/
theorem returned_settled (snapshot : Snapshot stackTapeCount) (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (payloadData : ℤ → Fin 6) (returnedLive : ℕ)
    (framesSettled : Settled snapshot (SharedBank.payload inputBank storage) (SharedBank.payload inputBank extra)) :
    Settled snapshot (SharedBank.payload (returned inputBank payloadData returnedLive) storage)
      (SharedBank.payload (returned inputBank payloadData returnedLive) extra) := by
  apply CompactComplexSourceReadySettledFrames.settled_of_port_eq framesSettled
  · intro port portProtected
    exact returned_frame inputBank payloadData returnedLive (storage port) (storage_ne_source port)
      (fun portsEqual => CompactComplexSourceReadyReachedDormantFrameInvariant.protected_ne_live
        _ _ _ port portProtected (storage_injective portsEqual))
      (fun portsEqual => protected_ne_target snapshot port portProtected (storage_injective portsEqual))
  · exact returned_frame inputBank payloadData returnedLive (extra 0) (extra_ne_source 0)
      (extra_ne_storage 0 ⟨7,by omega⟩) (extra_ne_storage 0 ⟨8,by omega⟩)

/-- The exact pre-pop endpoint of source orientation followed by a stopped
leaf retains all physically captured stack ports. -/
theorem beforepop_settled (snapshot : Snapshot stackTapeCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (tapes stackTapeCount roleCount) 2) (payloadData : Fin coefficientCount → ButterflyStreamData.Coefficient)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ)
    (framesSettled : Settled snapshot (SharedBank.payload inputBank storage) (SharedBank.payload inputBank extra)) :
    Settled snapshot (SharedBank.payload (returned (output call inputBank payloadData) childResultWord childTarget) storage)
      (SharedBank.payload (returned (output call inputBank payloadData) childResultWord childTarget) extra) :=
  returned_settled snapshot _ childResultWord childTarget (oriented_settled snapshot call inputBank payloadData framesSettled)

section Captured
open CompactComplexSourceReadyCapturedChildFrames (snapshot childOutput)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexChildHeadersData (parent)
open CompactComplexRecursiveGeometry (arity Visit)
variable {shape : CompactGadgetReservationShape.Shape}
  {leftBoundary childExponent levelCount frameCount returnedVolume rowCount logColumns metadataPrecision basePrecision growthConstant axesUsed baselinePrecision scalarPrefix parentLive : ℕ}
  (rowCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+2))
  (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackTapeCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {inputBank : Tapes (nodeTapes stackTapeCount roles) 2}
  (parentReached : Reached (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision (childExponent+2) basePrecision growthConstant axesUsed
    baselinePrecision levelCount frameCount returnedVolume scalarPrefix parentLive pcStack stackOrigin savedCalls inputBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackTapeCount)
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

/-- Real captured source entry and the stopped-leaf endpoint retain the same
Settled snapshot; its initial clean tails follow from the parent invariant. -/
theorem captured_beforepop_settled
    (ancestorSnapshot : Snapshot stackTapeCount) (framesSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    (payloadData : Fin coefficientCount → ButterflyStreamData.Coefficient) (childResultWord : ℤ → Fin 6) (childTarget : ℕ) :
    let capturedSnapshot := snapshot rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
    let capturedInput := childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
    Settled capturedSnapshot (SharedBank.payload (returned (output call capturedInput payloadData) childResultWord childTarget) storage)
      (SharedBank.payload (returned (output call capturedInput payloadData) childResultWord childTarget) extra) := by
  dsimp only
  apply beforepop_settled
  exact CompactComplexSourceReadyCapturedSettledFrames.snapshot_settled_from_parent
    rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack ancestorSnapshot framesSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
    headerDistinctLive pcDistinctHeader pcDistinctLive

end Captured

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedSettledFrames
