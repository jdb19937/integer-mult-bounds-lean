module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEntryPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadyGuard
public import IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturn

/-! The actual installed child bank supplies its input headers, source and
reusable stopping workspace. These facts are projections of physical entry,
not independent readiness premises for the recursive call. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexChildInputReadiness
noncomputable section
variable {s c : ℕ}
open CompactComplexNonleafRoleSplit (slot placement)
open CompactComplexNonleafRoleChildBank (tapes)
open CompactComplexNonleafRoleSourceReturn (base)

private theorem active_cell (v : Tapes (tapes s c) 2)
    (w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2)
    (h : Placement.active placement v=w) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    v.head (slot i)=w.head i ∧ v.tape (slot i)=w.tape i := by
  have hh := congrArg (fun z => z.head i) h
  have ht := congrArg (fun z => z.tape i) h
  simpa only [Placement.active,placement,InjectivePlacement.active_slot] using And.intro hh ht

private theorem header_slot (i : Fin 43) :
    slot (s:=10+s) (c:=c) (Fin.castAdd (CompactNativeRoleInstall.rawCount c) i)=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

theorem headers (v : Tapes (tapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2)
    (h : Placement.active placement v=CompactNativeRoleOriginal.bank st payload) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement (base v)=
      ActiveRepairRankHeadersCommands.bank st := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have hh := active_cell v _ h (Fin.castAdd _ i)
    rw [header_slot] at hh
    simp only [CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_left] at hh
  · simpa only [Placement.active,CompactComplexNonleafRoleEntry.headerPlacement,
      InjectivePlacement.active_slot,base,ActiveRepairRankHeadersCommands.bank,
      CleanSubbank.bank,Tapes.append] using hh.1
  · simpa only [Placement.active,CompactComplexNonleafRoleEntry.headerPlacement,
      InjectivePlacement.active_slot,base,ActiveRepairRankHeadersCommands.bank,
      CleanSubbank.bank,Tapes.append] using hh.2

private theorem source_slot :
    slot (s:=10+s) (c:=c) (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c))))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c)) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot]

theorem source (v : Tapes (tapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2)
    (h : Placement.active placement v=CompactNativeRoleOriginal.bank st payload) :
    (base v).head CompactComplexNonleafRoleEntry.source=payload.head 0 ∧
    (base v).tape CompactComplexNonleafRoleEntry.source=payload.tape 0 := by
  have hh := active_cell v _ h (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c))))
  rw [source_slot] at hh
  have he : (Fin.castAdd 7 (0 : Fin (1+c)) : Fin (CompactNativeRoleInstall.rawCount c))=
      Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (0 : Fin (1+c))))) := Fin.ext rfl
  simp only [CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_right] at hh
  rw [he] at hh
  simpa only [base,CompactNativeRoleInstall.blankRaw,Tapes.append,Fin.addCases_left] using hh


private theorem role_slot (j : Fin c) :
    slot (s:=10+s) (c:=c) (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j)))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j) := by
  apply Fin.ext
  simp only [slot,CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd]
  split_ifs <;> omega

theorem role (v : Tapes (tapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2)
    (h : Placement.active placement v=CompactNativeRoleOriginal.bank st payload) (j : Fin c) :
    (base v).head (CompactComplexNonleafRoleEntry.roleTape j)=payload.head (Fin.natAdd 1 j) ∧
    (base v).tape (CompactComplexNonleafRoleEntry.roleTape j)=payload.tape (Fin.natAdd 1 j) := by
  have hh := active_cell v _ h (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j)))
  rw [role_slot] at hh
  have he : (Fin.castAdd 7 (Fin.natAdd 1 j) : Fin (CompactNativeRoleInstall.rawCount c))=
      Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 j)))) := Fin.ext rfl
  simp only [CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_right] at hh
  rw [he] at hh
  simpa only [base,CompactNativeRoleInstall.blankRaw,Tapes.append,Fin.addCases_left] using hh

private theorem blank_scratch (payload : Tapes (1+c) 2) (j : Fin 7) :
    (CompactNativeRoleInstall.blankRaw payload).head (Fin.natAdd (1+c) j)=0 ∧
    (CompactNativeRoleInstall.blankRaw payload).tape (Fin.natAdd (1+c) j)=(fun _ => blank) := by
  fin_cases j <;> simp [CompactNativeRoleInstall.blankRaw,Tapes.append,SharedBank.empty,Fin.addCases]

/-- All ten stopping scratch tapes are installed blank, independently of
caller storage and payload values. -/
theorem stop_ready (v : Tapes (tapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2)
    (h : Placement.active placement v=CompactNativeRoleOriginal.bank st payload) :
    CompactComplexSourceReadyGuard.Ready v := by
  intro i
  by_cases hi : i.val<3
  · let j : Fin 43 := ⟨28+i.val,by omega⟩
    have hh := active_cell v _ h (Fin.castAdd _ j)
    rw [header_slot] at hh
    have he : j=Fin.natAdd 28 (⟨i.val,by omega⟩ : Fin 15) := Fin.ext rfl
    simp only [CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_left] at hh
    rw [he] at hh
    simp only [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,
      Fin.addCases_right,SharedBank.empty] at hh
    rw [←he] at hh
    simpa only [CompactComplexSourceReadyGuard.scratch,dite_eq_left hi] using hh
  · let j : Fin 7 := ⟨i.val-3,by have hx := i.isLt;omega⟩
    have hh := active_cell v _ h (Fin.natAdd 43 (Fin.natAdd (1+c) j))
    have he : slot (s:=10+s) (c:=c) (Fin.natAdd 43 (Fin.natAdd (1+c) j))=
        Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j := by
      apply Fin.ext
      simp only [slot,Fin.val_natAdd]
      split_ifs <;> omega
    rw [he] at hh
    simp only [CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_right] at hh
    have hb := blank_scratch payload j
    exact ⟨by simpa only [CompactComplexSourceReadyGuard.scratch,dite_eq_right hi] using hh.1.trans hb.1,
      by simpa only [CompactComplexSourceReadyGuard.scratch,dite_eq_right hi] using hh.2.trans hb.2⟩


private theorem target_future_ne (j : Fin s) :
    CompactComplexNonleafRoleChildBank.target (s:=s) (c:=c)≠
      CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 j) := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem target_control_ne :
    CompactComplexNonleafRoleChildBank.target (s:=s) (c:=c)≠
      CompactComplexNonleafRoleChildBank.control 1 := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    CompactComplexNonleafRoleChildBank.control,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem control_outside (j : Fin 43) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j≠slot (s:=10+s) i := by
  intro he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  simp only [CompactComplexNonleafRoleChildBank.control,slot] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  split_ifs at hv <;> omega

private theorem replace_control (v : Tapes (tapes s c) 2)
    (w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (j : Fin 43) :
    (Placement.replace placement v w).head (CompactComplexNonleafRoleChildBank.control j)=
      v.head (CompactComplexNonleafRoleChildBank.control j) ∧
    (Placement.replace placement v w).tape (CompactComplexNonleafRoleChildBank.control j)=
      v.tape (CompactComplexNonleafRoleChildBank.control j) := by
  obtain ⟨i,he⟩ := (placement (s:=10+s) (c:=c)).surjective (CompactComplexNonleafRoleChildBank.control j)
  rw [←he]
  induction i using Fin.addCases with
  | left i =>
    have hs : placement (s:=10+s) (c:=c) (Fin.castAdd _ i)=slot i := by
      simp only [placement,InjectivePlacement.active_slot]
    exact (control_outside j i (he.symm.trans hs)).elim
  | right i =>
    simp only [Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

section Actual
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyChildEntryPath (publicOutput)
variable {sh : Shape} {left k : ℕ}
variable (call : Networks.ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) CompactComplexRolePhaseSite.roleCount) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s)
local notation "out" => publicOutput call rho visit hactive pair rows ell p f v parentTarget n
  headerStack pcStack liveStack

/-- Actual child entry derives its canonical raw geometry. -/
theorem entered_headers :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement (base out)=
      ActiveRepairRankHeadersCommands.bank
        (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rho visit hactive pair call.slot)
          (rows/CompactComplexRolePhaseSite.roleCount) ell p) :=
  headers out _ _ (CompactComplexSourceReadyChildEntryPath.public_output_active
    call rho visit hactive pair rows ell p f v parentTarget n headerStack pcStack liveStack)

/-- The exact selected array is installed at the original child source port. -/
theorem entered_source :
    (out).head (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s)))=0 ∧
    (out).tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s)))=
      CompactSpectatorLeafAxis.word f := by
  have h := source out _ _ (CompactComplexSourceReadyChildEntryPath.public_output_active
    call rho visit hactive pair rows ell p f v parentTarget n headerStack pcStack liveStack)
  simpa [base,CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,
    Tapes.append,Fin.addCases,CompactSpectatorLeafAxis.word,NativeZeroPadding.word,
    NativeZeroPaddingArray.word,ButterflyStreamData.full] using h

/-- Every reached child entry supplies the ten clean stop-test tapes. -/
theorem entered_stop_ready : CompactComplexSourceReadyGuard.Ready out :=
  stop_ready out _ _ (CompactComplexSourceReadyChildEntryPath.public_output_active
    call rho visit hactive pair rows ell p f v parentTarget n headerStack pcStack liveStack)

/-- The stopping classifier receives its genuine immutable axis descriptor. -/
theorem entered_dimension :
    (out).head CompactComplexSourceReadyGuard.dimension=1 ∧
    (out).tape CompactComplexSourceReadyGuard.dimension=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits sh.axes) := by
  have h := active_cell out _ (CompactComplexSourceReadyChildEntryPath.public_output_active
    call rho visit hactive pair rows ell p f v parentTarget n headerStack pcStack liveStack)
    (Fin.castAdd _ (1 : Fin 43))
  rw [header_slot] at h
  change (out).head CompactComplexSourceReadyGuard.dimension=1 ∧
    (out).tape CompactComplexSourceReadyGuard.dimension=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits sh.axes) at h
  exact h

/-- The child's live denominator is the parent's actual incoming live word. -/
theorem entered_current :
    (out).head CompactComplexNonleafRoleChildBank.current=
      v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩) ∧
    (out).tape CompactComplexNonleafRoleChildBank.current=
      v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩) := by
  have h := CompactComplexNonleafRoleChildBank.output_current
    (CompactComplexNonleafRolePreparation.sourceReady (CompactComplexSourceReadyChildEntryPath.selected call)
      rho visit hactive pair rows ell p f v)
    parentTarget n (k+2) headerStack pcStack liveStack call.site rho visit hactive pair call.slot
    (rows/CompactComplexRolePhaseSite.roleCount) ell p
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell f
      CompactComplexRolePhaseSite.roleCount)
  have hq := CompactComplexNonleafRolePreparation.quotient_output_storage
    (CompactComplexSourceReadyChildEntryPath.selected call) sh rows ell p
    (CompactComplexChildHeadersData.parent rho visit hactive pair).rho
    (CompactComplexChildHeadersData.parent rho visit hactive pair).left
    (CompactComplexChildHeadersData.parent rho visit hactive pair).f
    (CompactComplexChildHeadersData.parent rho visit hactive pair).slots
    (CompactComplexChildHeadersData.parent rho visit hactive pair).right
    (CompactComplexChildHeadersData.parent rho visit hactive pair).source.val
    (CompactComplexChildHeadersData.parent rho visit hactive pair).target.val f v ⟨7,by omega⟩
  exact ⟨h.1.trans hq.1,h.2.trans hq.2⟩

/-- Saving the parent's target installs a genuinely vacant child target. -/
theorem entered_target :
    (out).head CompactComplexNonleafRoleChildBank.target=0 ∧
    (out).tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank) := by
  let initial := CompactComplexNonleafRolePreparation.sourceReady
    (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v
  let saved := CompactComplexNonleafRoleChildBank.descended
    (CompactComplexNonleafRoleChildBank.pcSaved
      (CompactComplexNonleafRoleChildBank.headersSaved
        (CompactComplexNonleafRoleChildBank.liveSaved
          (CompactComplexNonleafRoleChildBank.targetSaved initial parentTarget) liveStack n)
        headerStack (CompactComplexControllerChildPrefix.data
          (CompactComplexChildHeadersData.parent rho visit hactive pair))) pcStack call.site call.slot) (k+2)
  have h := CompactComplexNonleafRoleChildBank.replace_storage saved
    (CompactNativeRoleOriginal.bank
      (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rho visit hactive pair call.slot)
        (rows/CompactComplexRolePhaseSite.roleCount) ell p)
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell f
        CompactComplexRolePhaseSite.roleCount)) ⟨8,by omega⟩
  have hs : saved.head CompactComplexNonleafRoleChildBank.target=0 ∧
      saved.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank) := by
    simp only [saved,CompactComplexNonleafRoleChildBank.descended,
      CompactComplexNonleafRoleChildBank.pcSaved,FiniteReturnStackAt.pushed,
      CompactComplexNonleafRoleChildBank.headersSaved,CompactComplexNonleafRoleChildBank.liveSaved,
      CompactComplexNonleafRoleChildBank.targetSaved,SharedPlacementAlphabet.setTape]
    rw [Function.update_of_ne target_control_ne,Function.update_of_ne (target_future_ne pcStack),
      Function.update_of_ne (target_future_ne headerStack),Function.update_of_ne (target_future_ne liveStack),
      Function.update_self,Function.update_of_ne target_control_ne,
      Function.update_of_ne (target_future_ne pcStack),Function.update_of_ne (target_future_ne headerStack),
      Function.update_of_ne (target_future_ne liveStack),Function.update_self]
    exact ⟨rfl,rfl⟩
  exact ⟨h.1.trans hs.1,h.2.trans hs.2⟩

/-- The actual child receives the physically decremented exponent descriptor. -/
theorem entered_exponent :
    (out).head (CompactComplexNonleafRoleChildBank.control 1)=1 ∧
    (out).tape (CompactComplexNonleafRoleChildBank.control 1)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (k+1)) := by
  let initial := CompactComplexNonleafRolePreparation.sourceReady
    (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v
  let saved := CompactComplexNonleafRoleChildBank.descended
    (CompactComplexNonleafRoleChildBank.pcSaved
      (CompactComplexNonleafRoleChildBank.headersSaved
        (CompactComplexNonleafRoleChildBank.liveSaved
          (CompactComplexNonleafRoleChildBank.targetSaved initial parentTarget) liveStack n)
        headerStack (CompactComplexControllerChildPrefix.data
          (CompactComplexChildHeadersData.parent rho visit hactive pair))) pcStack call.site call.slot) (k+2)
  have h := replace_control saved
    (CompactNativeRoleOriginal.bank
      (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rho visit hactive pair call.slot)
        (rows/CompactComplexRolePhaseSite.roleCount) ell p)
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell f
        CompactComplexRolePhaseSite.roleCount)) (1 : Fin 43)
  have hs : saved.head (CompactComplexNonleafRoleChildBank.control 1)=1 ∧
      saved.tape (CompactComplexNonleafRoleChildBank.control 1)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (k+1)) := by
    simp only [saved,CompactComplexNonleafRoleChildBank.descended,SharedPlacementAlphabet.setTape,
      Function.update_self]
    rw [show k+2-1=k+1 by omega]
    exact ⟨True.intro,BinaryDescriptorStackRoundtrip.descriptor_encoded _⟩
  exact ⟨h.1.trans hs.1,h.2.trans hs.2⟩

/-- All permanent child roles start vacant at their real original ports. -/
theorem entered_roles (j : Fin CompactComplexRolePhaseSite.roleCount) :
    (base out).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
    (base out).tape (CompactComplexNonleafRoleEntry.roleTape j)=(fun _ => blank) := by
  have h := role out _ _ (CompactComplexSourceReadyChildEntryPath.public_output_active
    call rho visit hactive pair rows ell p f v parentTarget n headerStack pcStack liveStack) j
  simpa only [CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,Tapes.append,
    Fin.addCases_right] using h

/-- Genuine retained coefficient widths pay the literal installed source
support required by the following nonleaf entry. -/
theorem entered_source_supported
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    RoleArrayStack.Supported
      ((out).tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s))))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount
        (rows/CompactComplexRolePhaseSite.roleCount) ell p false) := by
  rw [(entered_source call rho visit hactive pair rows ell p f v parentTarget n headerStack pcStack liveStack).2]
  apply RoleArrayStack.supported_word
  have hh := CyclicRowSplit.prefix_length
    (fun i => ButterflyStreamData.encoded (f i)) (2*(CompactNativeRoleHeaders.recordWidth sh p+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (hw i).1 (hw i).2)
    (ButterflySpectatorGeometry.Size (rows/CompactComplexRolePhaseSite.roleCount) sh.bits (2^ell)) le_rfl
  rw [CyclicRowCycle.prefix_all] at hh
  change (NativeZeroPaddingArray.word f).length≤_
  change (NativeZeroPaddingArray.word f).length=_ at hh
  rw [hh]
  simp only [CompactComplexSpectatorVolumeHeaders.streamVolume,
    CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,ButterflySpectatorGeometry.Size]
  exact le_of_eq (by ring)

end Actual

end
end IntegerMultBounds.Machine.CompactComplexChildInputReadiness
