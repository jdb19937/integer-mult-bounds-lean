module

public import IntegerMultBounds.Machine.CompactComplexRootWorkspaceClean
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCount

/-! Stopped-root return preserves the initially vacant public role and frame
workspace, and reclaims the entire leaf and work suffix. These are properties
of the actual emitted return bank, not a supplied cleanup execution. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexStoppedRootWorkspaceClean
noncomputable section
open CompactComplexSourceReadyWorkspace (publicTapes leafTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexRootWorkspaceClean (Clean)
variable {stackCount roles : ℕ}

/-- Public root workspace is vacant before a stopped call: all original role
payloads and the seven-tape entry frame have blank tapes and origin heads. -/
def PublicClean (inputBank : Tapes (publicTapes stackCount roles) 2) : Prop :=
  (∀ framePort : Fin 7,
    inputBank.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)=0 ∧
    inputBank.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)=(fun _ => blank)) ∧
  (∀ rolePort : Fin roles,
    inputBank.head (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape rolePort))=0 ∧
    inputBank.tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape rolePort))=(fun _ => blank))

/-- The literal original-source root bank supplies public cleanliness
internally: its source payload has vacant roles and its frame seven is empty.
Controller, raw headers, caller storage and auxiliary prefixes stay arbitrary. -/
theorem initial_public_clean (shape : CompactGadgetReservationShape.Shape) (rows ell : ℕ)
    (sourceArray : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :
    PublicClean (CompactComplexNonleafSpectatorTargetRestore.entry
      (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactNativeRoleReservedBridge.sourcePayload shape rows ell sourceArray roles))
      (auxiliary.append (SharedBank.empty 7 2))) := by
  constructor
  · intro framePort
    have frameSlot : CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackCount roles
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)=
        Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+stackCount) roles) (Fin.natAdd 2 framePort) := by
      apply Fin.ext
      simp only [CompactComplexNonleafSpectatorTargetRestore.entryEquiv,finCongr_apply,
        Fin.val_cast,Fin.val_natAdd,CompactComplexNonleafRoleEntry.tapes]
      omega
    simp only [CompactComplexNonleafSpectatorTargetRestore.entry,Tapes.reindex,Equiv.symm_symm,frameSlot,
      Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]
  · intro rolePort
    have roleSlot : CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackCount roles
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) rolePort))=
        Fin.castAdd 9 (CompactComplexSpectatorTargetBank.roleSlot rolePort) := by
      apply Fin.ext
      rfl
    have roleBlank :
        (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
          (CompactNativeRoleReservedBridge.sourcePayload shape rows ell sourceArray roles)).head
            (CompactComplexSpectatorTargetBank.roleSlot rolePort)=0 ∧
        (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
          (CompactNativeRoleReservedBridge.sourcePayload shape rows ell sourceArray roles)).tape
            (CompactComplexSpectatorTargetBank.roleSlot rolePort)=(fun _ => blank) := by
      simp only [CompactComplexNativeCodecFrame.bank,CompactComplexSpectatorTargetBank.roleSlot,
        CompactComplexNativeRoleBridge.bank,CompactComplexNativeRoleBridge.roleSlot,
        CompactNativeRoleSourcePorts.roles,CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,
        Tapes.append,Fin.addCases_right]
      have payloadSlot : (⟨rolePort.val+1,by omega⟩ : Fin (1+roles))=Fin.natAdd 1 rolePort := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      simp only [payloadSlot,Fin.addCases_right,and_self]
    simpa only [CompactComplexNonleafSpectatorTargetRestore.entry,Tapes.reindex,Equiv.symm_symm,roleSlot,
      Tapes.append,Fin.addCases_left] using roleBlank

private theorem frame_ne_entry (framePort : Fin 7)
    (entryPort : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles)) :
    Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort≠Fin.castAdd 7 entryPort := by
  intro equalPorts
  have equalValues := congrArg Fin.val equalPorts
  have entryBound := entryPort.isLt
  simp only [Fin.val_natAdd,Fin.val_castAdd] at equalValues
  omega

private theorem role_ne_native (rolePort : Fin roles)
    (nativePort : Fin (CompactComplexControllerNativeFrame.tapes ((10+stackCount)+43))) :
    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) rolePort)≠
      Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd roles nativePort)) := by
  intro equalPorts
  have equalValues := congrArg Fin.val equalPorts
  have nativeBound := nativePort.isLt
  simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,Fin.val_castAdd,Fin.val_natAdd] at equalValues
  omega

private theorem returned_retained (inputBank : Tapes (publicTapes stackCount roles) 2)
    (outputWord : ℤ → Fin 6) (outputLive : ℕ) (workspacePort : Fin (publicTapes stackCount roles))
    (sourceDistinct : workspacePort≠CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))
    (liveDistinct : workspacePort≠CompactComplexNonleafRoleChildBank.current)
    (targetDistinct : workspacePort≠CompactComplexNonleafRoleChildBank.target) :
    (returned inputBank outputWord outputLive).head workspacePort=inputBank.head workspacePort ∧
    (returned inputBank outputWord outputLive).tape workspacePort=inputBank.tape workspacePort := by
  simp only [returned,SharedPlacementAlphabet.setTape,Function.update_of_ne sourceDistinct,
    Function.update_of_ne liveDistinct,Function.update_of_ne targetDistinct,and_self]

/-- The actual stopped leaf return changes only source, live and target;
every initially vacant public role and frame tape stays vacant. -/
theorem returned_public_clean (inputBank : Tapes (publicTapes stackCount roles) 2)
    (inputClean : PublicClean inputBank) (outputWord : ℤ → Fin 6) (outputLive : ℕ) :
    PublicClean (returned inputBank outputWord outputLive) := by
  constructor
  · intro framePort
    have retained := returned_retained inputBank outputWord outputLive
      (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)
      (frame_ne_entry framePort _) (frame_ne_entry framePort _) (frame_ne_entry framePort _)
    exact ⟨retained.1.trans (inputClean.1 framePort).1,retained.2.trans (inputClean.1 framePort).2⟩
  · intro rolePort
    have retained := returned_retained inputBank outputWord outputLive
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape rolePort))
      (role_ne_native rolePort _) (role_ne_native rolePort _) (role_ne_native rolePort _)
    exact ⟨retained.1.trans (inputClean.2 rolePort).1,retained.2.trans (inputClean.2 rolePort).2⟩

/-- The literal ready-bank layout clears leaf and work tapes and retains the
vacant public frame and roles, yielding the same full node cleanup predicate. -/
theorem ready_clean (publicBank : Tapes (publicTapes stackCount roles) 2)
    (publicClean : PublicClean publicBank) : Clean (ready publicBank) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro leafPort
    simp only [ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,
      Fin.addCases_left,Fin.addCases_right,SharedBank.empty,and_self]
  · intro workPort
    simp only [ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,
      Fin.addCases_right,SharedBank.empty,and_self]
  · intro framePort
    simpa only [ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left]
      using publicClean.1 framePort
  · intro rolePort
    simpa only [ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left]
      using publicClean.2 rolePort

/-- Cleanup belongs to the actual returned source/live/target bank, with no
separately chosen output or cleanup path. -/
theorem returned_clean (inputBank : Tapes (publicTapes stackCount roles) 2)
    (inputClean : PublicClean inputBank) (outputWord : ℤ → Fin 6) (outputLive : ℕ) :
    Clean (ready (returned inputBank outputWord outputLive)) :=
  ready_clean _ (returned_public_clean inputBank inputClean outputWord outputLive)

end
end IntegerMultBounds.Machine.CompactComplexStoppedRootWorkspaceClean
