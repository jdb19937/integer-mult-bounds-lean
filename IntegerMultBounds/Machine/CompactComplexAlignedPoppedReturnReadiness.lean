module

public import IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnReadiness
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedSavedReturnPath

/-! Physical return ports after the literal saved-PC pop. Updating the actual
PC stack leaves the distinct dormant header/live stacks, target stack, payload
stack and blank clock unchanged. No recursive execution premise is introduced. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyCompletedChildBoundary (completed)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadyCorrectedSavedReturnPath (publicSaved)
open CompactComplexNonleafRoleChildBank (storage)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
variable {s : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

private theorem setTape_port {t : ℕ} (u : Tapes t 2) (i j : Fin t)
    (older : ℤ → Fin 6) (top : ℤ) (hne : i≠j) :
    (setTape u j older top).head i=u.head i ∧
      (setTape u j older top).tape i=u.tape i := by
  simp only [setTape,Function.update_of_ne hne,and_self]

private theorem storage_injective : Function.Injective (storage (s:=s) (c:=roles)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem stack_ne_saved (stack pc : Fin s) (hne : pc≠stack) :
    storage (c:=roles) (Fin.natAdd 10 stack)≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val (storage_injective he)
  apply hne
  apply Fin.ext
  simp only [Fin.val_natAdd] at hv
  omega

private theorem target_ne_saved (pc : Fin s) :
    storage (c:=roles) (⟨9,by omega⟩ : Fin (10+s))≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val (storage_injective he)
  simp only [Fin.val_natAdd] at hv
  omega

private theorem extra_ne_saved (i : Fin 2) (pc : Fin s) :
    extra (s:=s) (c:=roles) i≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val he
  have hj := (Fin.natAdd 10 pc).isLt
  simp only [extra,publicSaved,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at hv
  omega

/-- The literal public endpoint after the actual saved-PC stack is popped. -/
def popped (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top : ℤ) :=
  setTape u (publicSaved pc) older top

section Completed
variable {sh : CompactGadgetReservationShape.Shape} {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (older : ℤ → Fin 6) (top : ℤ)

theorem popped_header_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) (hne : pcStack≠snapshot.headerStack) :
    (popped (completed h hslots hd call) pcStack older top).head
        (storage (Fin.natAdd 10 snapshot.headerStack))=
      snapshot.storage.head (Fin.natAdd 10 snapshot.headerStack) ∧
    (popped (completed h hslots hd call) pcStack older top).tape
        (storage (Fin.natAdd 10 snapshot.headerStack))=
      snapshot.storage.tape (Fin.natAdd 10 snapshot.headerStack) := by
  have hp := setTape_port (completed h hslots hd call) _ _ older top
    (stack_ne_saved snapshot.headerStack pcStack hne)
  have hc := CompactComplexAlignedCompletedReturnReadiness.completed_header_stack h hslots hd call snapshot settled
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_live_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) (hne : pcStack≠snapshot.liveStack) :
    (popped (completed h hslots hd call) pcStack older top).head
        (storage (Fin.natAdd 10 snapshot.liveStack))=
      snapshot.storage.head (Fin.natAdd 10 snapshot.liveStack) ∧
    (popped (completed h hslots hd call) pcStack older top).tape
        (storage (Fin.natAdd 10 snapshot.liveStack))=
      snapshot.storage.tape (Fin.natAdd 10 snapshot.liveStack) := by
  have hp := setTape_port (completed h hslots hd call) _ _ older top
    (stack_ne_saved snapshot.liveStack pcStack hne)
  have hc := CompactComplexAlignedCompletedReturnReadiness.completed_live_stack h hslots hd call snapshot settled
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_target_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) :
    (popped (completed h hslots hd call) pcStack older top).head (storage ⟨9,by omega⟩)=
      snapshot.storage.head ⟨9,by omega⟩ ∧
    (popped (completed h hslots hd call) pcStack older top).tape (storage ⟨9,by omega⟩)=
      snapshot.storage.tape ⟨9,by omega⟩ := by
  have hp := setTape_port (completed h hslots hd call) _ _ older top (target_ne_saved pcStack)
  have hc := CompactComplexAlignedCompletedReturnReadiness.completed_target_stack h hslots hd call snapshot settled
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_payload_stack (snapshot : Snapshot s)
    (settled : Settled snapshot h.storage h.aux) :
    (popped (completed h hslots hd call) pcStack older top).head (extra 0)=snapshot.aux.head 0 ∧
    (popped (completed h hslots hd call) pcStack older top).tape (extra 0)=snapshot.aux.tape 0 := by
  have hp := setTape_port (completed h hslots hd call) _ _ older top (extra_ne_saved 0 pcStack)
  have hc := CompactComplexAlignedCompletedReturnReadiness.completed_payload_stack h hslots hd call snapshot settled
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_clock :
    (popped (completed h hslots hd call) pcStack older top).head (extra 1)=0 ∧
    (popped (completed h hslots hd call) pcStack older top).tape (extra 1)=(fun _ => blank) := by
  have hp := setTape_port (completed h hslots hd call) _ _ older top (extra_ne_saved 1 pcStack)
  have hc := CompactComplexAlignedCompletedReturnReadiness.completed_clock h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

end Completed
end
end IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness
