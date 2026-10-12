module

public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness

/-! Controller and storage readiness retained by the actual saved-PC pop.
These assertions read the actual projected return bank, rather than supplying
an equality to a presumed restored parent endpoint. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnPorts
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyCompletedChildBoundary (completed)
open CompactComplexSourceReadyCorrectedSavedReturnPath (publicSaved)
open CompactComplexAlignedPoppedReturnReadiness (popped)
open CompactComplexNonleafRoleChildBank (control storage current target)
open CompactComplexSourceReadyChildReturnPath (controlPart storagePart)
variable {s : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

private theorem control_ne_saved (i : Fin 43) (pc : Fin s) :
    control (s:=s) (c:=roles) i≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val=(publicSaved pc).val at hv
  simp only [publicSaved,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem small_storage_ne_saved (i : Fin (10+s)) (hi : i.val<10) (pc : Fin s) :
    storage (c:=roles) i≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val he
  simp only [publicSaved,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_ne_saved (pc : Fin s) :
    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=roles))≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,publicSaved,storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem raw_slot_ne_saved
    (i : Fin (43+CompactNativeRoleInstall.rawCount roles)) (pc : Fin s) :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=roles) i≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val he
  have hp := pc.isLt
  simp only [CompactComplexNonleafRoleSplit.slot,publicSaved,storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  split_ifs at hv <;> omega

/-- Popping the saved-PC stack retains the literal child raw/source bank. -/
theorem popped_raw_active (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top : ℤ) :
    Placement.active CompactComplexNonleafRoleParentContinuation.placement (popped u pc older top)=
      Placement.active CompactComplexNonleafRoleParentContinuation.placement u := by
  change Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=roles)) _=
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=roles)) _
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [popped,setTape,Function.update_of_ne (raw_slot_ne_saved i pc)]

private def scalarSlot {c : ℕ} (i : Fin 43) : Fin (CompactComplexNonleafRoleChildBank.tapes s c) :=
  Fin.castAdd 7 (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+s) (c:=c) i))

private theorem scalar_slot_generic {c : ℕ} (i : Fin 43) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexNativeCodecFrame.originalSlot (s:=10+s) (c:=c) i))=
      scalarSlot (c:=c) i := Fin.ext rfl

private theorem scalar_slot (i : Fin 43) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s roles).symm
      (Fin.castAdd 9 (CompactComplexNativeCodecFrame.originalSlot (s:=10+s) (c:=roles) i))=
      scalarSlot (c:=roles) i := scalar_slot_generic i

private theorem scalar_ne_saved (i : Fin 43) (pc : Fin s) : scalarSlot (c:=roles) i≠publicSaved pc := by
  intro he
  have hv := congrArg Fin.val he
  have hp := pc.isLt
  simp only [scalarSlot,CompactComplexNativeCodecFrame.originalSlot,publicSaved,storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem popped_scalarPart (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top : ℤ) :
    CompactComplexSourceReadyChildReturnPath.scalarPart (popped u pc older top)=
      CompactComplexSourceReadyChildReturnPath.scalarPart u := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,
    scalar_slot,popped,setTape,Function.update_of_ne (scalar_ne_saved i pc)]

/-- A saved-PC pop retains every actual controller projection. -/
theorem popped_control_read (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top : ℤ) (i : Fin 43) :
    (controlPart (popped u pc older top)).head i=u.head (control i) ∧
    (controlPart (popped u pc older top)).tape i=u.tape (control i) := by
  have hr := CompactComplexAlignedReachedChildReturnPath.control_read (popped u pc older top) i
  simpa only [popped,setTape,Function.update_of_ne (control_ne_saved i pc)] using hr

/-- Count/live/target and the target stack lie below all saved-PC stacks. -/
theorem popped_small_storage_read (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top : ℤ) (i : Fin (10+s)) (hi : i.val<10) :
    (storagePart (popped u pc older top)).head i=u.head (storage i) ∧
    (storagePart (popped u pc older top)).tape i=u.tape (storage i) := by
  have hr := CompactComplexAlignedReachedChildReturnPath.storage_read (popped u pc older top) i
  simpa only [popped,setTape,Function.update_of_ne (small_storage_ne_saved i hi pc)] using hr

/-- The saved-PC port itself is the literal older stack after the pop. -/
theorem popped_saved (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top : ℤ) :
    (popped u pc older top).head (publicSaved pc)=top ∧
    (popped u pc older top).tape (publicSaved pc)=older := by
  simp only [popped,setTape,Function.update_self,and_self]

theorem popped_saved_associated (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (pc : Fin s) (older : ℤ → Fin 6) (top origin : ℤ)
    (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (h : CompactComplexSourceReadySavedCallHistory.Associated origin calls older top) :
    CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((popped u pc older top).tape (publicSaved pc))
      ((popped u pc older top).head (publicSaved pc)) := by
  rw [(popped_saved u pc older top).1,(popped_saved u pc older top).2]
  exact h

section Completed
variable {sh : CompactGadgetReservationShape.Shape} {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    (call : Networks.ComplexRecursiveCallSchema.Call)
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n
      pcStack origin (call::calls) v)
    (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (older : ℤ → Fin 6) (top : ℤ)

theorem popped_raw_source :
    Placement.active CompactComplexNonleafRoleParentContinuation.placement
      (popped (completed h hslots hd call) pcStack older top)=
      CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell metadataP)
        (CompactNativeRoleReservedBridge.sourcePayload sh rows ell
          (CompactComplexSourceReadyCompletedChildBoundary.result h hslots hd call) roles) :=
  (popped_raw_active (completed h hslots hd call) pcStack older top).trans
    (CompactComplexSourceReadyCompletedChildBoundary.completed_raw_source h hslots hd call)

theorem popped_scalar :
    CompactComplexSourceReadyChildReturnPath.scalarPart
      (popped (completed h hslots hd call) pcStack older top)=
      ActiveRepairRankHeadersCommands.bank h.scalar :=
  (popped_scalarPart (completed h hslots hd call) pcStack older top).trans
    (CompactComplexSourceReadyCompletedChildBoundary.completed_scalar h hslots hd call)

theorem popped_control28 :
    (controlPart (popped (completed h hslots hd call) pcStack older top)).head 28=0 ∧
    (controlPart (popped (completed h hslots hd call) pcStack older top)).tape 28=(fun _ => blank) := by
  have hp := popped_control_read (completed h hslots hd call) pcStack older top 28
  have hc := CompactComplexSourceReadyCompletedChildBoundary.completed_control28 h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_control29 :
    (controlPart (popped (completed h hslots hd call) pcStack older top)).head 29=0 ∧
    (controlPart (popped (completed h hslots hd call) pcStack older top)).tape 29=(fun _ => blank) := by
  have hp := popped_control_read (completed h hslots hd call) pcStack older top 29
  have hc := CompactComplexSourceReadyCompletedChildBoundary.completed_control29 h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_exponent :
    (controlPart (popped (completed h hslots hd call) pcStack older top)).head 1=1 ∧
    (controlPart (popped (completed h hslots hd call) pcStack older top)).tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits e) := by
  have hp := popped_control_read (completed h hslots hd call) pcStack older top 1
  have hc := CompactComplexSourceReadyCompletedChildBoundary.completed_exponent h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_count :
    (storagePart (popped (completed h hslots hd call) pcStack older top)).head ⟨0,by omega⟩=0 ∧
    (storagePart (popped (completed h hslots hd call) pcStack older top)).tape ⟨0,by omega⟩=(fun _ => blank) := by
  have hp := popped_small_storage_read (completed h hslots hd call) pcStack older top ⟨0,by omega⟩ (by change (0 : ℕ)<10; decide)
  have hc := CompactComplexSourceReadyCompletedChildBoundary.completed_count h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_current :
    (storagePart (popped (completed h hslots hd call) pcStack older top)).head ⟨7,by omega⟩=1 ∧
    (storagePart (popped (completed h hslots hd call) pcStack older top)).tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits h.targetValue) := by
  have hp := popped_small_storage_read (completed h hslots hd call) pcStack older top ⟨7,by omega⟩ (by change (7 : ℕ)<10; decide)
  have hc := CompactComplexSourceReadyCompletedChildBoundary.completed_live h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_target :
    (storagePart (popped (completed h hslots hd call) pcStack older top)).head ⟨8,by omega⟩=0 ∧
    (storagePart (popped (completed h hslots hd call) pcStack older top)).tape ⟨8,by omega⟩=(fun _ => blank) := by
  have hp := popped_small_storage_read (completed h hslots hd call) pcStack older top ⟨8,by omega⟩ (by change (8 : ℕ)<10; decide)
  have hc := CompactComplexSourceReadyCompletedChildBoundary.completed_target_blank h hslots hd call
  exact ⟨hp.1.trans hc.1,hp.2.trans hc.2⟩

theorem popped_source :
    (popped (completed h hslots hd call) pcStack older top).head
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=roles)))=0 ∧
    (popped (completed h hslots hd call) pcStack older top).tape
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=roles)))=
      CompactSpectatorLeafAxis.word (CompactComplexSourceReadyCompletedChildBoundary.result h hslots hd call) := by
  simpa only [popped,setTape,Function.update_of_ne (source_ne_saved pcStack)] using
    CompactComplexSourceReadyCompletedChildBoundary.completed_source h hslots hd call

/-- The actual popped completed-child bank supplies the controller/count and
older-history premises of the computed restored parent ports. -/
theorem restored_parent_ports {left k : ℕ}
    (callerParent : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) roles) 2)
    (headerStack liveStack : Fin s) (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
    (f : ℤ → Fin 6) (head : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (parentExponent parentLive : ℕ) (rho : Fin sh.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (parentRows : ℕ) (payload : Tapes (1+roles) 2) (returnedWord : ℤ → Fin 6)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (parentTarget : ℕ)
    (parentAux : Tapes 2 2)
    (hclock : parentAux.head 1=0 ∧ parentAux.tape 1=(fun _ => blank))
    (hfree : CompactComplexSourceReadyPrefixReadiness.BlankAfter parentAux 0)
    (ho : CompactComplexSourceReadySavedCallHistory.Associated origin calls older top) :
    let middle := CompactComplexAlignedReachedChildReturnPath.mid
      (CompactComplexRolePhaseSite.role call.site) callerParent
      (popped (completed h hslots hd call) pcStack older top) headerStack liveStack f head liveFrame liveHead
      parentExponent parentLive h.targetValue rho visit ha pair parentRows ell metadataP payload returnedWord
    CompactComplexSourceReadyReachedReturnInvariant.Restored parentExponent h.targetValue parentTarget
      pcStack origin calls (controlPart middle)
      (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
        h.targetValue targetFrame targetHead parentTarget) parentAux := by
  have hs := popped_saved_associated (completed h hslots hd call) pcStack older top origin calls ho
  have hp := CompactComplexAlignedReachedChildReturnPath.storage_read
    (popped (completed h hslots hd call) pcStack older top) (Fin.natAdd 10 pcStack)
  have hs' : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart (popped (completed h hslots hd call) pcStack older top)).tape (Fin.natAdd 10 pcStack))
      ((storagePart (popped (completed h hslots hd call) pcStack older top)).head (Fin.natAdd 10 pcStack)) := by
    rw [hp.1,hp.2]
    exact hs
  exact CompactComplexAlignedReachedChildReturnPath.restored_ports
    (CompactComplexRolePhaseSite.role call.site) callerParent
    (popped (completed h hslots hd call) pcStack older top) headerStack pcStack liveStack hpcHeader hpcLive
    f head liveFrame liveHead parentExponent parentLive h.targetValue rho visit ha pair parentRows ell metadataP
    payload returnedWord targetFrame targetHead parentTarget parentAux origin calls
    (popped_count call h hslots hd older top) (popped_control28 call h hslots hd older top)
    (popped_control29 call h hslots hd older top) hclock hfree hs'

end Completed
end
end IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnPorts
