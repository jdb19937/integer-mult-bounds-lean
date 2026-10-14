module

public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnPorts
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedChildFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledFrames

/-! Literal parent-restoration premises on the actual popped completed-child
bank. Dormant frames come from the transported child Settled invariant, while
the original parent Settled invariant supplies clean erased descriptor regions.
No recursive execution or output-grid assumption is introduced. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnPorts
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots)
open CompactComplexSourceReadyCompletedChildBoundary (completed result)
open CompactComplexAlignedPoppedReturnReadiness (popped)
open CompactComplexNonleafRoleChildBank (storage control current target)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexSourceReadyChildReturnPath (storagePart controlPart scalarPart)
open RecursiveChildQuotientsConstant (bits)
variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

section Parent
variable {nodeLeft childExponent parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant
    completedAxes baselineLive parentLevels parentFrames parentReturned parentPrefix parentLive : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2))
    (activeFits : shape.active≤ shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackCount roles) 2}
    (parentReached : Reached (parent phaseCoordinate visit activeFits pair) parentRows polynomialExponent metadataPrecision
      (childExponent+2) baselinePrecision growthConstant completedAxes baselineLive parentLevels parentFrames parentReturned
      parentPrefix parentLive pcStack origin savedCalls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- Coherent literal boundary ports consumed by the physical parent return.
The result bank and array are shared by every field. -/
structure Ports (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (resultArray : CompactSpectatorVisitGeometry.Array shape (parentRows/roles) polynomialExponent)
    (returnScalar : ActiveRepairRankHeadersCommands.State) (returnedLive : ℕ) : Prop where
  rawSource : Placement.active CompactComplexNonleafRoleParentContinuation.placement returnedBank=
    CompactNativeRoleOriginal.bank
      (CompactComplexNativeCodec.raw (child phaseCoordinate visit activeFits pair call.slot)
        (parentRows/roles) polynomialExponent metadataPrecision)
      (CompactNativeRoleReservedBridge.sourcePayload shape (parentRows/roles) polynomialExponent resultArray roles)
  savedHeaders : returnedBank.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=
      CompactChildHeadersStack.top (parentReached.storage.head (Fin.natAdd 10 headerStack))
        (CompactComplexControllerChildPrefix.data (parent phaseCoordinate visit activeFits pair)) ∧
    returnedBank.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=
      CompactChildHeadersStack.frames (parentReached.storage.tape (Fin.natAdd 10 headerStack))
        (parentReached.storage.head (Fin.natAdd 10 headerStack))
        (CompactComplexControllerChildPrefix.data (parent phaseCoordinate visit activeFits pair))
  savedLive : returnedBank.head (storage (Fin.natAdd 10 liveStack))=
      parentReached.storage.head (Fin.natAdd 10 liveStack)+1+(bits parentLive).length ∧
    returnedBank.tape (storage (Fin.natAdd 10 liveStack))=
      BinaryDescriptorStack.frame (parentReached.storage.tape (Fin.natAdd 10 liveStack))
        (parentReached.storage.head (Fin.natAdd 10 liveStack)) (bits parentLive)
  savedTarget : (storagePart returnedBank).head ⟨9,by omega⟩=
      parentReached.storage.head ⟨9,by omega⟩+1+(bits parentReached.targetValue).length ∧
    (storagePart returnedBank).tape ⟨9,by omega⟩=
      BinaryDescriptorStack.frame (parentReached.storage.tape ⟨9,by omega⟩)
        (parentReached.storage.head ⟨9,by omega⟩) (bits parentReached.targetValue)
  payloadStack : returnedBank.head (extra 0)=
      (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape parentRows polynomialExponent metadataPrecision
        (parent phaseCoordinate visit activeFits pair).rho (parent phaseCoordinate visit activeFits pair).left
        (parent phaseCoordinate visit activeFits pair).f (parent phaseCoordinate visit activeFits pair).slots
        (parent phaseCoordinate visit activeFits pair).right (parent phaseCoordinate visit activeFits pair).source.val
        (parent phaseCoordinate visit activeFits pair).target.val (caller parentReached)).head CompactComplexNonleafRoleEntry.stack ∧
    returnedBank.tape (extra 0)=
      (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape parentRows polynomialExponent metadataPrecision
        (parent phaseCoordinate visit activeFits pair).rho (parent phaseCoordinate visit activeFits pair).left
        (parent phaseCoordinate visit activeFits pair).f (parent phaseCoordinate visit activeFits pair).slots
        (parent phaseCoordinate visit activeFits pair).right (parent phaseCoordinate visit activeFits pair).source.val
        (parent phaseCoordinate visit activeFits pair).target.val (caller parentReached)).tape CompactComplexNonleafRoleEntry.stack
  clock : returnedBank.head (extra 1)=0 ∧ returnedBank.tape (extra 1)=(fun _ => blank)
  scalar : scalarPart returnedBank=ActiveRepairRankHeadersCommands.bank returnScalar
  exponent : returnedBank.head (control 1)=1 ∧ returnedBank.tape (control 1)=BinaryDescriptorStack.descriptor (bits (childExponent+1))
  live : returnedBank.head current=1 ∧ returnedBank.tape current=BinaryDescriptorStack.descriptor (bits returnedLive)
  targetBlank : returnedBank.head target=0 ∧ returnedBank.tape target=(fun _ => blank)
  countBlank : (storagePart returnedBank).head ⟨0,by omega⟩=0 ∧ (storagePart returnedBank).tape ⟨0,by omega⟩=(fun _ => blank)
  control28Blank : (controlPart returnedBank).head 28=0 ∧ (controlPart returnedBank).tape 28=(fun _ => blank)
  control29Blank : (controlPart returnedBank).head 29=0 ∧ (controlPart returnedBank).tape 29=(fun _ => blank)
  olderHistory : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls
    ((storagePart returnedBank).tape (Fin.natAdd 10 pcStack)) ((storagePart returnedBank).head (Fin.natAdd 10 pcStack))
  headerTailClean : ∀ cell,parentReached.storage.head (Fin.natAdd 10 headerStack)≤ cell →
    parentReached.storage.tape (Fin.natAdd 10 headerStack) cell=blank
  liveFrameClean : ∀ cell,parentReached.storage.head (Fin.natAdd 10 liveStack)≤ cell →
    cell<parentReached.storage.head (Fin.natAdd 10 liveStack)+1+(bits parentLive).length →
    parentReached.storage.tape (Fin.natAdd 10 liveStack) cell=blank
  targetFrameClean : ∀ cell,parentReached.storage.head ⟨9,by omega⟩≤ cell →
    cell<parentReached.storage.head ⟨9,by omega⟩+1+(bits parentReached.targetValue).length →
    parentReached.storage.tape ⟨9,by omega⟩ cell=blank

section Terminal
variable {childLevels childFrames childReturned childPrefix terminalLive : ℕ}
    {terminalBank : Tapes (nodeTapes stackCount roles) 2}
    (terminalReached : Reached (child phaseCoordinate visit activeFits pair call.slot) (parentRows/roles) polynomialExponent
      metadataPrecision (childExponent+1) baselinePrecision growthConstant 0 baselineLive childLevels childFrames childReturned
      childPrefix terminalLive pcStack origin (call::savedCalls) terminalBank)
    (childSlots : (child phaseCoordinate visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (older : ℤ → Fin 6) (top : ℤ)

/-- Every physical restored-frame premise is derived on the same genuine
popped completed bank from the actual parent and transported child frames. -/
theorem ready_ports
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (completedSettled : Settled
      (CompactComplexSourceReadyCapturedChildFrames.snapshot phaseCoordinate visit activeFits pair parentReached call headerStack liveStack)
      terminalReached.storage terminalReached.aux)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls older top) :
    Ports phaseCoordinate visit activeFits pair parentReached call headerStack liveStack
      (popped (completed terminalReached childSlots childRowsDivisible call) pcStack older top)
      (result terminalReached childSlots childRowsDivisible call) terminalReached.scalar terminalReached.targetValue := by
  let capturedSnapshot := CompactComplexSourceReadyCapturedChildFrames.snapshot
    phaseCoordinate visit activeFits pair parentReached call headerStack liveStack
  let returnedBank := popped (completed terminalReached childSlots childRowsDivisible call) pcStack older top
  have capturedHeaders := CompactComplexSourceReadyCapturedChildFrames.snapshot_headers
    phaseCoordinate visit activeFits pair parentReached call headerStack liveStack pcHeaderDistinct.symm headerLiveDistinct
  have capturedLive := CompactComplexSourceReadyCapturedChildFrames.snapshot_live
    phaseCoordinate visit activeFits pair parentReached call headerStack liveStack headerLiveDistinct.symm pcLiveDistinct.symm
  have capturedTarget := CompactComplexSourceReadyCapturedChildFrames.snapshot_target
    phaseCoordinate visit activeFits pair parentReached call headerStack liveStack
  have capturedPayload := CompactComplexSourceReadyCapturedChildFrames.snapshot_payload
    phaseCoordinate visit activeFits pair parentReached call headerStack liveStack
  have poppedHeaders := CompactComplexAlignedPoppedReturnReadiness.popped_header_stack
    terminalReached childSlots childRowsDivisible call older top capturedSnapshot completedSettled pcHeaderDistinct
  have poppedLive := CompactComplexAlignedPoppedReturnReadiness.popped_live_stack
    terminalReached childSlots childRowsDivisible call older top capturedSnapshot completedSettled pcLiveDistinct
  have poppedTarget := CompactComplexAlignedPoppedReturnReadiness.popped_target_stack
    terminalReached childSlots childRowsDivisible call older top capturedSnapshot completedSettled
  have poppedPayload := CompactComplexAlignedPoppedReturnReadiness.popped_payload_stack
    terminalReached childSlots childRowsDivisible call older top capturedSnapshot completedSettled
  have targetPorts := CompactComplexAlignedReachedChildReturnPath.storage_read returnedBank (⟨9,by omega⟩ : Fin (10+stackCount))
  have exponentPorts := CompactComplexAlignedReachedChildReturnPath.control_read returnedBank 1
  have currentPorts := CompactComplexAlignedReachedChildReturnPath.storage_read returnedBank (⟨7,by omega⟩ : Fin (10+stackCount))
  have blankTargetPorts := CompactComplexAlignedReachedChildReturnPath.storage_read returnedBank (⟨8,by omega⟩ : Fin (10+stackCount))
  have actualExponent := CompactComplexAlignedPoppedReturnPorts.popped_exponent call terminalReached childSlots childRowsDivisible older top
  have actualCurrent := CompactComplexAlignedPoppedReturnPorts.popped_current call terminalReached childSlots childRowsDivisible older top
  have actualBlankTarget := CompactComplexAlignedPoppedReturnPorts.popped_target call terminalReached childSlots childRowsDivisible older top
  have oldSavedPorts := CompactComplexAlignedReachedChildReturnPath.storage_read returnedBank (Fin.natAdd 10 pcStack)
  have actualSavedHistory := CompactComplexAlignedPoppedReturnPorts.popped_saved_associated
    (completed terminalReached childSlots childRowsDivisible call) pcStack older top origin savedCalls olderAssociated
  have parentCleanTails := CompactComplexSourceReadySettledFrames.storage_clean_current parentSettled
  refine {
    rawSource := CompactComplexAlignedPoppedReturnPorts.popped_raw_source call terminalReached childSlots childRowsDivisible older top
    savedHeaders := ⟨poppedHeaders.1.trans capturedHeaders.1,poppedHeaders.2.trans capturedHeaders.2⟩
    savedLive := ⟨poppedLive.1.trans capturedLive.1,poppedLive.2.trans capturedLive.2⟩
    savedTarget := ⟨targetPorts.1.trans (poppedTarget.1.trans capturedTarget.1),targetPorts.2.trans (poppedTarget.2.trans capturedTarget.2)⟩
    payloadStack := ⟨poppedPayload.1.trans capturedPayload.1,poppedPayload.2.trans capturedPayload.2⟩
    clock := CompactComplexAlignedPoppedReturnReadiness.popped_clock terminalReached childSlots childRowsDivisible call older top
    scalar := CompactComplexAlignedPoppedReturnPorts.popped_scalar call terminalReached childSlots childRowsDivisible older top
    exponent := ⟨exponentPorts.1.symm.trans actualExponent.1,exponentPorts.2.symm.trans actualExponent.2⟩
    live := ⟨currentPorts.1.symm.trans actualCurrent.1,currentPorts.2.symm.trans (actualCurrent.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)⟩
    targetBlank := ⟨blankTargetPorts.1.symm.trans actualBlankTarget.1,blankTargetPorts.2.symm.trans actualBlankTarget.2⟩
    countBlank := CompactComplexAlignedPoppedReturnPorts.popped_count call terminalReached childSlots childRowsDivisible older top
    control28Blank := CompactComplexAlignedPoppedReturnPorts.popped_control28 call terminalReached childSlots childRowsDivisible older top
    control29Blank := CompactComplexAlignedPoppedReturnPorts.popped_control29 call terminalReached childSlots childRowsDivisible older top
    olderHistory := ?_
    headerTailClean := ?_
    liveFrameClean := ?_
    targetFrameClean := ?_
  }
  · rw [oldSavedPorts.1,oldSavedPorts.2]
    exact actualSavedHistory
  · intro cell aboveHeader
    apply parentCleanTails (Fin.natAdd 10 headerStack) _ cell aboveHeader
    rw [snapshotHeaderStack,snapshotLiveStack,snapshotPcStack]
    exact Or.inl rfl
  · intro cell aboveLive _belowFrameEnd
    apply parentCleanTails (Fin.natAdd 10 liveStack) _ cell aboveLive
    rw [snapshotHeaderStack,snapshotLiveStack,snapshotPcStack]
    exact Or.inr (Or.inl rfl)
  · intro cell aboveTarget _belowFrameEnd
    apply parentCleanTails ⟨9,by omega⟩ _ cell aboveTarget
    exact Or.inr (Or.inr (Or.inr rfl))

end Terminal
end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnPorts
