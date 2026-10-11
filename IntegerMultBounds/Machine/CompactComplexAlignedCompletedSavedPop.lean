module

public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness
public import IntegerMultBounds.Machine.CompactComplexAlignedSavedReturnPath

/-! The actual completed child supplies the genuine saved-call association.
The aligned table pops it and preserves every derived physical return port.
Recursive preservation of Settled remains an explicit induction obligation. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedCompletedSavedPop
noncomputable section
open Networks.Shared50ModularControl (prime)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyCompletedChildBoundary (completed)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexAlignedPoppedReturnReadiness (popped)
open CompactComplexNonleafRoleChildBank (storage)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexActualCallFullAlignment (localTapes)
open CompactNativeRoleConjugatedPorts (encoding)
variable {s q : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressWidth

/-- Exact guard/pop execution from the computed completed child, together
with its dormant return stacks and clock, on the original fixed aligned table. -/
theorem runs (P : Program ActivePrefixStageNative.tapes q prime)
    {sh : CompactGadgetReservationShape.Shape} {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    (headerStack pcStack liveStack : Fin s) (origin : ℤ) (calls : List Call) (call : Call)
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n
      pcStack origin (call::calls) v)
    (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roles) prime)
    (snapshot : Snapshot s) (settled : Settled snapshot h.storage h.aux)
    (hpcHeader : pcStack≠snapshot.headerStack) (hpcLive : pcStack≠snapshot.liveStack) :
    ∃ older top,
      CompactComplexSourceReadySavedCallHistory.Associated origin calls older top ∧
      CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack 0
        ((Alphabet.mapTapes encoding ((CompactComplexSourceReadyWorkspace.ready
          (completed h hslots hd call)).append scalar)).append suffix)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)
        (CompactComplexScheduledPCDecode.savedPC call)
        ((Alphabet.mapTapes encoding ((CompactComplexSourceReadyWorkspace.ready
          (popped (completed h hslots hd call) pcStack older top)).append scalar)).append suffix) ∧
      ((popped (completed h hslots hd call) pcStack older top).head
          (storage (Fin.natAdd 10 snapshot.headerStack))=snapshot.storage.head (Fin.natAdd 10 snapshot.headerStack) ∧
        (popped (completed h hslots hd call) pcStack older top).tape
          (storage (Fin.natAdd 10 snapshot.headerStack))=snapshot.storage.tape (Fin.natAdd 10 snapshot.headerStack)) ∧
      ((popped (completed h hslots hd call) pcStack older top).head
          (storage (Fin.natAdd 10 snapshot.liveStack))=snapshot.storage.head (Fin.natAdd 10 snapshot.liveStack) ∧
        (popped (completed h hslots hd call) pcStack older top).tape
          (storage (Fin.natAdd 10 snapshot.liveStack))=snapshot.storage.tape (Fin.natAdd 10 snapshot.liveStack)) ∧
      ((popped (completed h hslots hd call) pcStack older top).head (storage ⟨9,by omega⟩)=snapshot.storage.head ⟨9,by omega⟩ ∧
        (popped (completed h hslots hd call) pcStack older top).tape (storage ⟨9,by omega⟩)=snapshot.storage.tape ⟨9,by omega⟩) ∧
      ((popped (completed h hslots hd call) pcStack older top).head (extra 0)=snapshot.aux.head 0 ∧
        (popped (completed h hslots hd call) pcStack older top).tape (extra 0)=snapshot.aux.tape 0) ∧
      ((popped (completed h hslots hd call) pcStack older top).head (extra 1)=0 ∧
        (popped (completed h hslots hd call) pcStack older top).tape (extra 1)=(fun _ => blank)) := by
  have ha := CompactComplexSourceReadyCompletedChildBoundary.completed_saved h hslots hd call
  obtain ⟨older,top,ho,hpath⟩ := CompactComplexAlignedSavedReturnPath.public_associated_return_path
    P headerStack pcStack liveStack call (completed h hslots hd call) scalar suffix origin calls ha
  exact ⟨older,top,ho,hpath,
    CompactComplexAlignedPoppedReturnReadiness.popped_header_stack h hslots hd call older top snapshot settled hpcHeader,
    CompactComplexAlignedPoppedReturnReadiness.popped_live_stack h hslots hd call older top snapshot settled hpcLive,
    CompactComplexAlignedPoppedReturnReadiness.popped_target_stack h hslots hd call older top snapshot settled,
    CompactComplexAlignedPoppedReturnReadiness.popped_payload_stack h hslots hd call older top snapshot settled,
    CompactComplexAlignedPoppedReturnReadiness.popped_clock h hslots hd call older top⟩

end
end IntegerMultBounds.Machine.CompactComplexAlignedCompletedSavedPop
