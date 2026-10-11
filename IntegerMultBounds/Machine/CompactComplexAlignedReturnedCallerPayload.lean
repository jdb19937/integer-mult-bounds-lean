import IntegerMultBounds.Machine.CompactComplexAlignedReachedChildReturnPath

namespace IntegerMultBounds.Machine.CompactComplexAlignedReturnedCallerPayload
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyReachedReturnInvariant (roleData)
open CompactComplexSourceReadyChildReturnPath (payloadPart)
open SharedPlacementAlphabet (setTape)
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
variable {s c : ℕ} {sh : CompactGadgetReservationShape.Shape}

private def port : Fin (1+c) → Fin (CompactComplexNonleafRoleEntry.tapes (10+s) c) :=
  Fin.addCases (fun _ : Fin 1 => CompactComplexNonleafRoleEntry.source)
    CompactComplexNonleafRoleEntry.roleTape

private theorem payload_read (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (i : Fin (1+c)) :
    (payloadPart (v.append (SharedBank.empty 7 2))).head i=v.head (port i) ∧
    (payloadPart (v.append (SharedBank.empty 7 2))).tape i=v.tape (port i) := by
  have hp : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (Fin.addCases (fun _ : Fin 1 => CompactComplexNativeRoleBridge.sourceSlot)
        CompactComplexNativeRoleBridge.roleSlot i))=Fin.castAdd 7 (port i) := by
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left,port]
      apply Fin.ext
      rfl
    | right i =>
      simp only [Fin.addCases_right,port]
      apply Fin.ext
      rfl
  simp only [payloadPart,CompactComplexSourceReadyChildReturnPath.permanent,
    SharedBank.payload,Tapes.reindex,hp,Tapes.append,Fin.addCases_left,and_self]

private theorem source_ne_role (j : Fin c) :
    CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c)≠
      CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNonleafRoleEntry.roleTape,
    CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem role_injective : Function.Injective
    (CompactComplexNonleafRoleEntry.roleTape (s:=10+s) (c:=c)) := by
  intro i j he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

private theorem returned_payload_of_words (rows ell : ℕ) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh rows ell)
    (result : CompactSpectatorVisitGeometry.Array sh rows ell)
    (old : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (hs : old.head CompactComplexNonleafRoleEntry.source=0 ∧ old.tape CompactComplexNonleafRoleEntry.source=(fun _ => blank))
    (hw : ∀ j,old.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      old.tape (CompactComplexNonleafRoleEntry.roleTape j)=CompactSpectatorLeafAxis.word (before j)) :
    payloadPart ((setTape old (CompactComplexNonleafRoleEntry.roleTape selected)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh rows ell selected
        (fun _ => blank) 0 before result := by
  let updated := setTape old (CompactComplexNonleafRoleEntry.roleTape selected)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0
  let out := CompactComplexNormalizedSpectatorHandoff.returnedPayload sh rows ell selected
    (fun _ => blank) 0 before result
  have eqs (i : Fin (1+c)) :
      (payloadPart (updated.append (SharedBank.empty 7 2))).head i=out.head i ∧
      (payloadPart (updated.append (SharedBank.empty 7 2))).tape i=out.tape i := by
    have hp := payload_read updated i
    induction i using Fin.addCases (m:=1) (n:=c) with
    | left i =>
      fin_cases i
      have hu : updated.head (port (Fin.castAdd c (0 : Fin 1)))=0 ∧
          updated.tape (port (Fin.castAdd c (0 : Fin 1)))=(fun _ => blank) := by
        simpa only [updated,port,Fin.addCases_left,setTape,
          Function.update_of_ne (source_ne_role selected)] using hs
      exact ⟨hp.1.trans hu.1,hp.2.trans hu.2⟩
    | right j =>
      have hu : updated.head (port (Fin.natAdd 1 j))=0 ∧
          updated.tape (port (Fin.natAdd 1 j))=
            (if j=selected then NativeZeroPadding.word (NativeZeroPaddingArray.word result)
              else CompactSpectatorLeafAxis.word (before j)) := by
        by_cases he : j=selected
        · subst j
          simp only [updated,port,Fin.addCases_right,setTape,Function.update_self,ite_true,and_self]
        · have hn : CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j≠
              CompactComplexNonleafRoleEntry.roleTape selected := fun hh => he (role_injective hh)
          simpa only [updated,port,Fin.addCases_right,setTape,Function.update_of_ne hn,he,ite_false] using hw j
      have ho : out.head (Fin.natAdd 1 j)=0 ∧
          out.tape (Fin.natAdd 1 j)=
            (if j=selected then NativeZeroPadding.word (NativeZeroPaddingArray.word result)
              else CompactSpectatorLeafAxis.word (before j)) := by
        constructor
        · simp only [out,CompactComplexNormalizedSpectatorHandoff.returnedPayload,
            CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right]
        · simp only [out,CompactComplexNormalizedSpectatorHandoff.returnedPayload,
            CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right]
          split_ifs <;> rw [CompactComplexStoppedGridHandoff.words_tape]
          · rfl
          · rfl
      exact ⟨(hp.1.trans hu.1).trans ho.1.symm,(hp.2.trans hu.2).trans ho.2.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (eqs i).1
  · exact (eqs i).2


section Reached
variable {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)

private theorem caller_role (j : Fin roles) :
    (caller h).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
    (caller h).tape (CompactComplexNonleafRoleEntry.roleTape j)=CompactSpectatorLeafAxis.word (roleData h j) := by
  have hr := h.role_words (CompactComplexScalarRolePorts.roleIndex.symm j)
  rw [Equiv.apply_symm_apply] at hr
  have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload)
    h.aux (CompactComplexNativeRoleBridge.roleSlot j)
  exact ⟨he.1.trans hr.1,he.2.trans hr.2⟩

theorem caller_aux : CompactComplexAlignedReachedChildReturnPath.callerAux (caller h)=h.aux := by
  have hh (i : Fin 2) := CompactComplexSourceReadyScalarChildReadiness.entry_aux (s:=10+s) (c:=roles)
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload)
    h.aux i
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (hh i).1
  · exact (hh i).2


theorem returned_payload (selected : Fin roles)
    (result : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell) :
    payloadPart ((setTape (caller h) (CompactComplexNonleafRoleEntry.roleTape selected)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh (rows/roles) ell selected
        (fun _ => blank) 0 (roleData h) result :=
  returned_payload_of_words (s:=s) (rows/roles) ell selected (roleData h) result (caller h)
    (CompactComplexSourceReadyReachedEventInvariant.child_source h) (caller_role h)

end Reached
end
end IntegerMultBounds.Machine.CompactComplexAlignedReturnedCallerPayload
