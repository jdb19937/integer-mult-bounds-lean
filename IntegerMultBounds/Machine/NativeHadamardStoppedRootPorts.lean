module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationRootBank
public import IntegerMultBounds.Machine.CompactComplexPublicStoppedRootExecution

/-! Actual positive stopped-root ports for the shared phase/normalization wrapper.
Raw header readiness is projected from the original leaf-codec certificate;
the literal stopped return retains it and installs the genuine live target.
Source-only phase replacement preserves every required original public field. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardStoppedRootPorts
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyWorkspace (publicTapes ready leafTapes)
open SharedPlacementAlphabet (setTape)
variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount

def source : Fin (publicTapes stackCount roles) := CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount)

def phased (stage : Stage shape) (metadataPrecision : ℕ) {rows ell : ℕ}
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell) (inputBank : Tapes (publicTapes stackCount roles) 2) :=
  setTape inputBank source
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (NativeHadamardPhaseOriginal.result stage metadataPrecision coefficients))) 0

theorem ready_source_update (inputBank : Tapes (publicTapes stackCount roles) 2) (word : ℤ → Fin 6) (head : ℤ) :
    ready (setTape inputBank source word head)=setTape (ready inputBank) CompactComplexSourceReadyOrientation.source word head := by
  change ((setTape inputBank source word head).append (SharedBank.empty leafTapes 2)).append (SharedBank.empty 10 2)=_
  rw [←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left]
  rfl

theorem phased_ready (stage : Stage shape) (metadataPrecision : ℕ) {rows ell : ℕ}
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell) (inputBank : Tapes (publicTapes stackCount roles) 2) :
    ready (phased stage metadataPrecision coefficients inputBank)=
      NativeHadamardPhaseOutputBank.output stage metadataPrecision coefficients (ready inputBank) :=
  ready_source_update inputBank _ 0

private theorem codec_ne_source (header : Fin 43) :
    CompactComplexSourceReadyLeafCodec.slot (s:=10+stackCount) (c:=roles) header≠source (stackCount:=stackCount) := by
  intro equality
  have values := congrArg Fin.val equality
  have headerBound := header.isLt
  simp only [CompactComplexSourceReadyLeafCodec.slot,source,CompactComplexSourceReadyLeafPhase.source,
    CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at values
  omega

theorem raw_source_update (inputBank : Tapes (publicTapes stackCount roles) 2) (word : ℤ → Fin 6) (head : ℤ) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (CompactComplexNonleafRoleSourceReturn.base (setTape inputBank source word head))=
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base inputBank) := by
  rw [←CompactComplexSourceReadyLeafCodec.active,←CompactComplexSourceReadyLeafCodec.active]
  apply Placement.Tapes.ext'
  all_goals intro header
  all_goals simp only [Placement.active,CompactComplexSourceReadyLeafCodec.placement,
    InjectivePlacement.active_slot,setTape,Function.update_of_ne (codec_ne_source header)]

theorem headers_ready (stage : Stage shape) (rows ell metadataPrecision : ℕ)
    (inputBank : Tapes (publicTapes stackCount roles) 2)
    (rawHeaders : Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base inputBank)=
      ActiveRepairRankHeadersCommands.bank (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)) :
    NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision (ready inputBank) := by
  intro header
  have rawActive := (CompactComplexSourceReadyLeafCodec.active inputBank).trans rawHeaders
  have headValue := congrArg (fun raw => raw.head (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))) rawActive
  have tapeValue := congrArg (fun raw => raw.tape (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))) rawActive
  simp only [Placement.active,CompactComplexSourceReadyLeafCodec.placement,InjectivePlacement.active_slot] at headValue tapeValue
  have canonical :
      (ActiveRepairRankHeadersCommands.bank (a:=2) (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)).head
        (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))=1 ∧
      (ActiveRepairRankHeadersCommands.bank (a:=2) (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)).tape
        (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))=RadixZeroFill.encodedBinary
          (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header) := by
    fin_cases header <;> constructor <;> rfl
  constructor
  · simpa only [NativeHadamardPhaseRootHeaders.slot,CompactComplexSourceReadyLeafCodec.slot,
      ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using headValue.trans canonical.1
  · simpa only [NativeHadamardPhaseRootHeaders.slot,CompactComplexSourceReadyLeafCodec.slot,
      ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using tapeValue.trans canonical.2

theorem returned_headers (stage : Stage shape) (rows ell metadataPrecision : ℕ)
    (inputBank : Tapes (publicTapes stackCount roles) 2)
    (rawHeaders : Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base inputBank)=
      ActiveRepairRankHeadersCommands.bank (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision))
    (word : ℤ → Fin 6) (live : ℕ) :
    NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision
      (ready (CompactComplexSourceReadyStoppedLeafCount.returned inputBank word live)) :=
  headers_ready stage rows ell metadataPrecision _ ((CompactComplexSourceReadyStoppedLeafCount.returned_headers _ _ _).trans rawHeaders)

theorem live_ready (live : ℕ) (inputBank : Tapes (publicTapes stackCount roles) 2)
    (liveWord : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live)) :
    NativeHadamardNormalizationRootLive.Ready live (ready inputBank) := by
  simpa only [NativeHadamardNormalizationRootLive.Ready,NativeHadamardNormalizationRootLive.slot,
    CompactComplexNonleafRoleChildBank.current,ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using liveWord

theorem returned_live (inputBank : Tapes (publicTapes stackCount roles) 2) (word : ℤ → Fin 6) (live : ℕ) :
    NativeHadamardNormalizationRootLive.Ready live (ready (CompactComplexSourceReadyStoppedLeafCount.returned inputBank word live)) := by
  apply live_ready live
  simp [CompactComplexSourceReadyStoppedLeafCount.returned,setTape,
    CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
    source,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot]

theorem returned_source (inputBank : Tapes (publicTapes stackCount roles) 2) (word : ℤ → Fin 6) (live : ℕ) :
    (ready (CompactComplexSourceReadyStoppedLeafCount.returned inputBank word live)).tape CompactComplexSourceReadyOrientation.source=word ∧
      (ready (CompactComplexSourceReadyStoppedLeafCount.returned inputBank word live)).head CompactComplexSourceReadyOrientation.source=0 := by
  have publicSource : (CompactComplexSourceReadyStoppedLeafCount.returned inputBank word live).tape source=word ∧
      (CompactComplexSourceReadyStoppedLeafCount.returned inputBank word live).head source=0 := by
    have sourceCurrent : source (stackCount:=stackCount)≠CompactComplexNonleafRoleChildBank.current := by
      intro equality
      have values := congrArg Fin.val equality
      simp only [source,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
        CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.storage,
        CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
        CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
        Fin.val_castAdd,Fin.val_natAdd] at values
      omega
    have sourceTarget : source (stackCount:=stackCount)≠CompactComplexNonleafRoleChildBank.target := by
      intro equality
      have values := congrArg Fin.val equality
      simp only [source,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
        CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
        CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
        CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
        Fin.val_castAdd,Fin.val_natAdd] at values
      omega
    simp only [source,CompactComplexSourceReadyLeafPhase.source] at sourceCurrent sourceTarget
    simp only [CompactComplexSourceReadyStoppedLeafCount.returned,source,CompactComplexSourceReadyLeafPhase.source,
      setTape,Function.update_apply,ite_true,ite_eq_right sourceCurrent,ite_eq_right sourceTarget,and_self]
  simpa only [ready,CompactComplexSourceReadyWorkspace.bank,CompactComplexSourceReadyOrientation.source,
    NativePolynomialConjugationWorkspace.source,source,CompactComplexSourceReadyLeafPhase.source,
    Tapes.append,Fin.addCases_left] using publicSource

theorem public_clean_of_ready (inputBank : Tapes (publicTapes stackCount roles) 2)
    (clean : CompactComplexRootWorkspaceClean.Clean (ready inputBank)) :
    CompactComplexStoppedRootWorkspaceClean.PublicClean inputBank := by
  constructor
  · intro port
    simpa only [ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using clean.2.2.1 port
  · intro port
    simpa only [ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using clean.2.2.2 port

theorem phased_clean (stage : Stage shape) (metadataPrecision : ℕ) {rows ell : ℕ}
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell) (inputBank : Tapes (publicTapes stackCount roles) 2)
    (clean : CompactComplexStoppedRootWorkspaceClean.PublicClean inputBank) :
    CompactComplexStoppedRootWorkspaceClean.PublicClean (phased stage metadataPrecision coefficients inputBank) := by
  apply public_clean_of_ready
  rw [phased_ready]
  exact NativeHadamardPhaseOutputBank.output_clean _ _ _ _ (CompactComplexStoppedRootWorkspaceClean.ready_clean _ clean)


theorem source_update_retained (inputBank : Tapes (publicTapes stackCount roles) 2) (word : ℤ → Fin 6) (head : ℤ)
    (port : Fin (publicTapes stackCount roles)) (outside : port≠source) :
    (setTape inputBank source word head).head port=inputBank.head port ∧
      (setTape inputBank source word head).tape port=inputBank.tape port := by
  simp only [setTape,Function.update_of_ne outside,and_self]

theorem dimension_ne_source : CompactComplexSourceReadyGuard.dimension (s:=stackCount) (c:=roles)≠source :=
  codec_ne_source 1

theorem current_ne_source : CompactComplexNonleafRoleChildBank.current (s:=stackCount) (c:=roles)≠source := by
  intro equality
  have values := congrArg Fin.val equality
  simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.storage,
    source,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at values
  omega

theorem target_ne_source : CompactComplexNonleafRoleChildBank.target (s:=stackCount) (c:=roles)≠source := by
  intro equality
  have values := congrArg Fin.val equality
  simp only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
    source,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at values
  omega

theorem control_ne_source (port : Fin 43) : CompactComplexNonleafRoleChildBank.control (s:=stackCount) (c:=roles) port≠source := by
  intro equality
  have values := congrArg Fin.val equality
  have portBound := port.isLt
  simp only [CompactComplexNonleafRoleChildBank.control,source,CompactComplexSourceReadyLeafPhase.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_mk,Fin.val_castAdd,Fin.val_natAdd] at values
  omega

private theorem guard_ne_source (port : Fin 10) : CompactComplexSourceReadyGuard.scratch (s:=stackCount) (c:=roles) port≠source := by
  intro equality
  have values := congrArg Fin.val equality
  have portBound := port.isLt
  unfold CompactComplexSourceReadyGuard.scratch at values
  split_ifs at values
  all_goals simp only [source,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_mk,Fin.val_castAdd,Fin.val_natAdd] at values
  · omega
  · unfold CompactComplexSourceReadyGuard.permanent CompactComplexNonleafRoleEntry.tapes
      CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
      CompactComplexControllerNativeFrame.tapes at values
    omega

theorem guard_source_update (inputBank : Tapes (publicTapes stackCount roles) 2)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank) (word : ℤ → Fin 6) (head : ℤ) :
    CompactComplexSourceReadyGuard.Ready (setTape inputBank source word head) := by
  intro port
  simpa only [setTape,Function.update_of_ne (guard_ne_source port)] using guardReady port

theorem saved_source_update (inputBank : Tapes (publicTapes stackCount roles) 2) (pcStack : Fin stackCount)
    (word : ℤ → Fin 6) (head : ℤ) :
    (ready (setTape inputBank source word head)).head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)=
        (ready inputBank).head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack) ∧
      (ready (setTape inputBank source word head)).tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)=
        (ready inputBank).tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack) := by
  rw [ready_source_update]
  simp only [setTape,Function.update_of_ne (CompactComplexSourceReadyOrientationInvariants.savedSlot_ne_source pcStack),and_self]

end
end IntegerMultBounds.Machine.NativeHadamardStoppedRootPorts
