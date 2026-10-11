module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildWidth
public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedCallerPayload

/-! Local physical return readiness of the actual completed child. The selected
role is always the actual call's role. Dormant stack equations follow from the
honest Settled completion invariant, rather than a whole-bank restoration
equality. Recursive output grids and execution remain separate obligations. -/
@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnReadiness
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyCompletedChildBoundary (completed result)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots)
open CompactComplexSourceReadyReachedReturnInvariant (roleData)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

section Completed
variable {stage : Stage sh} {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call)

theorem completed_clock :
    (completed h hslots hd call).head (CompactComplexNonleafRoleParentPayloadContinuation.extra 1)=0 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleParentPayloadContinuation.extra 1)=(fun _ => blank) := by
  have ha := CompactComplexSourceReadyCompletedChildBoundary.completed_aux h hslots hd call 1
  exact ⟨ha.1.trans h.clock_blank.1,ha.2.trans h.clock_blank.2⟩

theorem completed_record_width (hmetadata : 2*sh.bits≤metadataP) :
    ∀ i,(result h hslots hd call i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
      (result h hslots hd call i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP := by
  simpa only [CompactNativeRoleHeaders.recordWidth,ButterflyGuard.width] using
    CompactComplexSourceReadyCompletedChildWidth.result_lengths h hslots hd hmetadata call

theorem completed_header_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) :
    (completed h hslots hd call).head
        (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 snapshot.headerStack))=
      snapshot.storage.head (Fin.natAdd 10 snapshot.headerStack) ∧
    (completed h hslots hd call).tape
        (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 snapshot.headerStack))=
      snapshot.storage.tape (Fin.natAdd 10 snapshot.headerStack) :=
  (CompactComplexSourceReadyCompletedChildBoundary.completed_dormant h hslots hd call snapshot settled).1
    _ (Or.inl rfl)

theorem completed_live_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) :
    (completed h hslots hd call).head
        (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 snapshot.liveStack))=
      snapshot.storage.head (Fin.natAdd 10 snapshot.liveStack) ∧
    (completed h hslots hd call).tape
        (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 snapshot.liveStack))=
      snapshot.storage.tape (Fin.natAdd 10 snapshot.liveStack) :=
  (CompactComplexSourceReadyCompletedChildBoundary.completed_dormant h hslots hd call snapshot settled).1
    _ (Or.inr (Or.inl rfl))

theorem completed_target_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.storage ⟨9,by omega⟩)=
      snapshot.storage.head ⟨9,by omega⟩ ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.storage ⟨9,by omega⟩)=
      snapshot.storage.tape ⟨9,by omega⟩ :=
  (CompactComplexSourceReadyCompletedChildBoundary.completed_dormant h hslots hd call snapshot settled).1
    _ (Or.inr (Or.inr (Or.inr rfl)))

theorem completed_payload_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=snapshot.aux.head 0 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=snapshot.aux.tape 0 :=
  (CompactComplexSourceReadyCompletedChildBoundary.completed_dormant h hslots hd call snapshot settled).2

end Completed

section Parent
variable {stage : Stage sh} {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (call : Networks.ComplexRecursiveCallSchema.Call)

/-- The genuine caller's free stack region, selected by the original call. -/
theorem caller_free :
    CompactComplexNonleafRoleReturn.Free (CompactComplexRolePhaseSite.role call.site)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP true) (caller h) :=
  CompactComplexSourceReadyReachedEventInvariant.child_free h _ _ _

theorem caller_source_supported :
    (caller h).head CompactComplexNonleafRoleEntry.source=0 ∧
    RoleArrayStack.Supported ((caller h).tape CompactComplexNonleafRoleEntry.source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP false) := by
  have hs := CompactComplexSourceReadyReachedEventInvariant.child_source h
  refine ⟨hs.1,?_⟩
  intro z hz
  rw [hs.2]

theorem caller_roles_supported :
    ∀ j,(caller h).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported ((caller h).tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP true) := by
  intro j
  have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload)
    h.aux (CompactComplexNativeRoleBridge.roleSlot j)
  have hw := h.role_words (CompactComplexScalarRolePorts.roleIndex.symm j)
  simp only [Equiv.apply_symm_apply] at hw
  refine ⟨he.1.trans hw.1,?_⟩
  simpa only [Equiv.apply_symm_apply] using
    CompactComplexSourceReadyReachedEventInvariant.child_role_supported h
      (CompactComplexScalarRolePorts.roleIndex.symm j)

variable {childStage : Stage sh}
    {ce cp cC caxes cbaseline clevels cframes creturned cpref cn : ℕ}
    {childPcStack : Fin s} {childOrigin : ℤ} {childCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {cv : Tapes (nodeTapes s roles) 2}
    (hc : Reached childStage (rows/roles) ell metadataP ce cp cC caxes cbaseline
      clevels cframes creturned cpref cn childPcStack childOrigin childCalls cv)

/-- Actual child output overwrites exactly the actual call's named role. -/
theorem completed_caller_payload (hslots : childStage.slots=NativeEndpointCharacterRoles.arity)
    (hd : roles∣rows/roles) :
    CompactComplexSourceReadyChildReturnPath.payloadPart
      ((SharedPlacementAlphabet.setTape (caller h)
        (CompactComplexNonleafRoleEntry.roleTape (CompactComplexRolePhaseSite.role call.site))
        (NativeZeroPadding.word (NativeZeroPaddingArray.word (result hc hslots hd call))) 0).append
          (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh (rows/roles) ell
        (CompactComplexRolePhaseSite.role call.site) (fun _ => blank) 0 (roleData h)
        (result hc hslots hd call) :=
  CompactComplexAlignedReturnedCallerPayload.returned_payload h
    (CompactComplexRolePhaseSite.role call.site) (result hc hslots hd call)

end Parent
end
end IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnReadiness
