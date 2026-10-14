module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildCleanTails
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildEntryPorts
public import IntegerMultBounds.Machine.CompactComplexAlignedNonleafClassifierPrefix
public import IntegerMultBounds.Machine.CompactComplexAlignedReachedNodeEntryPath

/-! Reconstruct the actual recursive child-entry bank from its real projected
ports. Source, geometry, scalar metadata and reusable workspaces are derived
from the physical child-entry endpoint, without a prepared-bank oracle. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildReadiness
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadySiblingChildInvariant (childPublic)
open CompactComplexSourceReadyRecursiveChildCleanTails (childStorage childAuxiliary)
open CompactComplexSourceReadyChildReturnPath (controlPart queuePart tailPart storagePart rawPart payloadPart scalarPart frame)
open CompactComplexNonleafRoleChildBank (control storage)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

private theorem raw_projection {stackCount roleCount : ℕ}
    (bank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roleCount) 2) :
    rawPart bank=Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (CompactComplexNonleafRoleSourceReturn.base bank) := by
  apply congrArg₂ Tapes.mk <;> funext index
  all_goals simp only [rawPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
    Tapes.reindex,Placement.active,CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_slot,
    CompactComplexNonleafRoleSourceReturn.base]
  all_goals rfl

private theorem payload_source_slot {stackCount roleCount : ℕ} :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackCount roleCount).symm
      (Fin.castAdd 9 (CompactComplexNativeRoleBridge.sourceSlot (s:=10+stackCount+43) (c:=roleCount)))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roleCount)) := Fin.ext rfl

private theorem payload_role_slot {stackCount roleCount : ℕ} (role : Fin roleCount) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackCount roleCount).symm
      (Fin.castAdd 9 (CompactComplexNativeRoleBridge.roleSlot (s:=10+stackCount+43) role))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) role) := Fin.ext rfl

private theorem frame_aux_slot {stackCount roleCount : ℕ} (index : Fin 2) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackCount roleCount).symm
      (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+stackCount) roleCount)
        (Fin.castAdd 7 index))=CompactComplexNonleafRoleParentPayloadContinuation.extra index := Fin.ext rfl

private theorem frame_scratch_slot {stackCount roleCount : ℕ} (index : Fin 7) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackCount roleCount).symm
      (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+stackCount) roleCount)
        (Fin.natAdd 2 index))=CompactComplexSourceReadyGuard.scratch (Fin.natAdd 3 index) := by
  apply Fin.ext
  simp only [CompactComplexSourceReadyGuard.scratch,Fin.val_natAdd]
  rw [dif_neg (by omega)]
  change CompactComplexNativeCodecFrame.permanentTapes (10+stackCount) roleCount+(2+index.val)=
    CompactComplexNonleafRoleEntry.tapes (10+stackCount) roleCount+(3+index.val-3)
  unfold CompactComplexNonleafRoleEntry.tapes
  omega

private theorem frame_eq {stackCount roleCount : ℕ}
    (bank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roleCount) 2)
    (scratchReady : CompactComplexSourceReadyGuard.Ready bank) :
    frame bank=(SharedBank.payload bank CompactComplexNonleafRoleParentPayloadContinuation.extra).append
      (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk <;> funext index
  all_goals induction index using Fin.addCases (m:=2) (n:=7) with
  | left index =>
    simp only [frame,SharedBank.payload,Tapes.reindex,frame_aux_slot,Tapes.append,Fin.addCases_left]
  | right index =>
    have blankPort := scratchReady (Fin.natAdd 3 index)
    first
    | simpa only [frame,SharedBank.payload,Tapes.reindex,frame_scratch_slot,
        Tapes.append,Fin.addCases_right,SharedBank.empty] using blankPort.1
    | simpa only [frame,SharedBank.payload,Tapes.reindex,frame_scratch_slot,
        Tapes.append,Fin.addCases_right,SharedBank.empty] using blankPort.2

private theorem payload_from_ports {stackCount roleCount : ℕ} {shape : Shape} {rows ell : ℕ}
    (bank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roleCount) 2)
    (original : CompactSpectatorVisitGeometry.Array shape rows ell)
    (sourceReady : bank.head (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roleCount)))=0 ∧
      bank.tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roleCount)))=
        CompactSpectatorLeafAxis.word original)
    (rolesBlank : ∀ role,bank.head (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) role))=0 ∧
      bank.tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) role))=(fun _ => blank)) :
    payloadPart bank=CompactNativeRoleReservedBridge.sourcePayload shape rows ell original roleCount := by
  have sourceWord : CompactSpectatorLeafAxis.word original=
      NativeZeroPadding.word (NativeZeroPaddingArray.word original) := rfl
  apply congrArg₂ Tapes.mk <;> funext index
  all_goals induction index using Fin.addCases (m:=1) (n:=roleCount) with
  | left index =>
    have indexZero : index=0 := Subsingleton.elim _ _
    subst index
    first
    | simpa only [payloadPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
        Tapes.reindex,Fin.addCases_left,payload_source_slot,CompactNativeRoleReservedBridge.sourcePayload,
        CyclicRowCopy.payload,Tapes.append,Fin.addCases_left] using sourceReady.1
    | simpa only [payloadPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
        Tapes.reindex,Fin.addCases_left,payload_source_slot,CompactNativeRoleReservedBridge.sourcePayload,
        CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,sourceWord] using sourceReady.2
  | right index =>
    first
    | simpa only [payloadPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
        Tapes.reindex,Fin.addCases_right,payload_role_slot,CompactNativeRoleReservedBridge.sourcePayload,
        CyclicRowCopy.payload,Tapes.append,Fin.addCases_right] using (rolesBlank index).1
    | simpa only [payloadPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
        Tapes.reindex,Fin.addCases_right,payload_role_slot,CompactNativeRoleReservedBridge.sourcePayload,
        CyclicRowCopy.payload,Tapes.append,Fin.addCases_right] using (rolesBlank index).2

section Child
variable {stackCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex rowCount polynomialExponent
    metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent
    metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) scalarPrefix parentLive pcStack origin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- The controller is read from the actual child's physical ports. -/
def childControl := controlPart (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
def childQueue := queuePart (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
def childTail := tailPart (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)

/-- Actual raw child geometry and original selected source reconstruct the
classifier's literal public bank, retaining every saved storage and aux frame. -/
theorem bank_eq_publicInput :
    childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack=
      CompactComplexAlignedNonleafClassifierPrefix.publicInput
        (child phaseCoordinate entryPath.visit activeFits pair call.slot) (rowCount/roles) polynomialExponent metadataPrecision
        (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
        (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
        (childQueue phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) parentReached.scalar
        (childTail phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
        (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
        (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) := by
  let actualChild := childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack
  have rawGeometry := CompactComplexChildInputReadiness.entered_headers call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have rawEqual : rawPart actualChild=ActiveRepairRankHeadersCommands.bank
      (CompactComplexNativeCodec.raw (child phaseCoordinate entryPath.visit activeFits pair call.slot)
        (rowCount/roles) polynomialExponent metadataPrecision) := (raw_projection actualChild).trans rawGeometry
  have sourceReady := CompactComplexChildInputReadiness.entered_source call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have rolesBlank := CompactComplexChildInputReadiness.entered_roles call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have payloadEqual := payload_from_ports actualChild
    (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call) sourceReady
    (fun role => by
      have physical := rolesBlank role
      simpa only [actualChild,childPublic,CompactComplexNonleafRoleSourceReturn.base,Tapes.append,Fin.addCases_left] using physical)
  have scalarEqual := CompactComplexSourceReadyStoppedChildEntryPorts.child_scalarPart phaseCoordinate entryPath.visit activeFits pair
    parentReached call headerStack liveStack
  have scratchReady := CompactComplexChildInputReadiness.entered_stop_ready call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have reconstructed := CompactComplexSourceReadyChildReturnPath.reconstruct actualChild parentReached.scalar
    (CompactComplexNativeCodec.raw (child phaseCoordinate entryPath.visit activeFits pair call.slot)
      (rowCount/roles) polynomialExponent metadataPrecision) _ scalarEqual rawEqual payloadEqual
  rw [frame_eq actualChild scratchReady,CompactComplexSourceReadyNonleafFinalGeometry.entry_append] at reconstructed
  rw [←CompactComplexSourceReadyRecursiveChildCleanTails.childStorage_eq_storagePart
    phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack] at reconstructed
  exact reconstructed

/-- The actual aligned child entry is exactly the classifier's original bank,
with the selected source still unoriented. -/
theorem bank_eq_originalBank :
    CompactComplexAlignedBoundaryPaths.alignedBank
      ((CompactComplexSourceReadyWorkspace.ready
        (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))=
      CompactComplexAlignedReachedNodeEntryPath.originalBank
        (child phaseCoordinate entryPath.visit activeFits pair call.slot) (rowCount/roles) polynomialExponent metadataPrecision
        (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
        (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
        (childQueue phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) parentReached.scalar
        (childTail phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
        (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
        (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) := by
  rw [bank_eq_publicInput]
  unfold CompactComplexAlignedReachedNodeEntryPath.originalBank CompactComplexSourceReadyNonleafContraction.ready
  rw [CompactComplexSourceReadyNonleafFinalGeometry.entry_append]
  rfl

private theorem child_control_read (index : Fin 43) :
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head index=
      (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head (control index) ∧
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape index=
      (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape (control index) := by
  simp only [childControl,controlPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex]
  exact ⟨rfl,rfl⟩

theorem count_blank :
    (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head ⟨0,by omega⟩=0 ∧
    (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape ⟨0,by omega⟩=(fun _ => blank) :=
  CompactComplexSourceReadyStoppedChildEntryPorts.child_count_blank phaseCoordinate entryPath.visit activeFits pair
    parentReached call headerStack liveStack

theorem clock_blank :
    (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head 1=0 ∧
    (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape 1=(fun _ => blank) :=
  CompactComplexSourceReadyStoppedChildEntryPorts.child_clock_blank phaseCoordinate entryPath.visit activeFits pair
    parentReached call headerStack liveStack

theorem auxiliary_free :
    CompactComplexSourceReadyPrefixReadiness.BlankAfter
      (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) 0 :=
  CompactComplexSourceReadyCapturedSettledFrames.snapshot_aux_clean phaseCoordinate entryPath.visit activeFits pair
    parentReached call headerStack liveStack

theorem control28_blank :
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head 28=0 ∧
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape 28=(fun _ => blank) := by
  have physical := CompactComplexSourceReadyStoppedChildEntryPorts.child_control28 phaseCoordinate entryPath.visit activeFits pair
    parentReached call headerStack liveStack
  have projected := child_control_read phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack 28
  exact ⟨projected.1.trans physical.1,projected.2.trans physical.2⟩

theorem control29_blank :
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head 29=0 ∧
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape 29=(fun _ => blank) := by
  have physical := CompactComplexSourceReadyStoppedChildEntryPorts.child_control29 phaseCoordinate entryPath.visit activeFits pair
    parentReached call headerStack liveStack
  have projected := child_control_read phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack 29
  exact ⟨projected.1.trans physical.1,projected.2.trans physical.2⟩

theorem exponent_ready :
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head 1=1 ∧
    (childControl phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (childExponent+1)) := by
  have physical := CompactComplexChildInputReadiness.entered_exponent call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have projected := child_control_read phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack 1
  exact ⟨projected.1.trans physical.1,projected.2.trans (physical.2.trans
    (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)⟩

theorem target_blank :
    (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head ⟨8,by omega⟩=0 ∧
    (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape ⟨8,by omega⟩=(fun _ => blank) :=
  CompactComplexChildInputReadiness.entered_target call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack

theorem current_ready :
    (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head ⟨7,by omega⟩=1 ∧
    (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits parentLive) := by
  have physical := CompactComplexChildInputReadiness.entered_current call phaseCoordinate entryPath.visit activeFits pair
    rowCount polynomialExponent metadataPrecision (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call)
    (CompactComplexSourceReadyReachedEventInvariant.caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have callerPort := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux
    (CompactComplexSpectatorTargetBank.oldSlot (⟨7,by omega⟩ : Fin (10+stackCount)))
  have storagePort := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload (⟨7,by omega⟩ : Fin (10+stackCount))
  exact ⟨physical.1.trans (callerPort.1.trans (storagePort.1.trans parentReached.live.1)),
    physical.2.trans (callerPort.2.trans (storagePort.2.trans parentReached.live.2))⟩

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildReadiness
