module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant

/-! Physical projections of the actual nonroot sink, contraction, merge and
orientation endpoint. The saved call remains on its stack here; its decoded
pop is a separate controller transition. No restored-parent bank equality or
recursive semantic execution is postulated. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildBoundary
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)
open CompactComplexNonleafRoleEntry (source roleTape numeric)
open CompactComplexNativeCodecFrame (permanentTapes)
open CompactComplexSourceReadyOrientationInvariants (oriented)
variable {s c : ℕ} {sh : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

section Generic
variable (stage : Stage sh) (rows ell p : ℕ) (f : Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)

def merge := CompactComplexNonleafRoleMergeCurrent.bank sh rows ell p stage.rho stage.left stage.f
  stage.slots stage.right stage.source.val stage.target.val f v

def finishedEntry (call : Networks.ComplexRecursiveCallSchema.Call) :=
  setTape (merge stage rows ell p f v) source (CompactSpectatorLeafAxis.word (oriented call f)) 0

def finishedPublic (call : Networks.ComplexRecursiveCallSchema.Call) :=
  (finishedEntry stage rows ell p f v call).append (SharedBank.empty 7 2)

theorem numeric_ne_source (i : Fin 43) : (numeric (s:=10+s) (c:=c) i)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [numeric,source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have := i.isLt
  omega

theorem role_ne_source (j : Fin c) : (roleTape (s:=10+s) j)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [roleTape,source,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexControllerNativeFrame.tapes at hv
  omega

theorem source_word (call : Networks.ComplexRecursiveCallSchema.Call) :
    (finishedPublic stage rows ell p f v call).head (Fin.castAdd 7 source)=0 ∧
    (finishedPublic stage rows ell p f v call).tape (Fin.castAdd 7 source)=
      CompactSpectatorLeafAxis.word (oriented call f) := by
  simp only [finishedPublic,finishedEntry,Tapes.append,Fin.addCases_left,setTape,Function.update_self,and_self]

theorem headers (call : Networks.ComplexRecursiveCallSchema.Call) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (finishedEntry stage rows ell p f v call)=
      ActiveRepairRankHeadersCommands.bank (CompactComplexNativeCodec.raw stage rows ell p) := by
  rw [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have hh := CompactComplexNonleafRoleMergeCurrent.output_headers sh rows ell p stage.rho stage.left
      stage.f stage.slots stage.right stage.source.val stage.target.val f v i
  · change (finishedEntry stage rows ell p f v call).head (numeric i)=_
    simpa only [finishedEntry,setTape,Function.update_of_ne (numeric_ne_source i),merge,
      CompactComplexNonleafRoleMergeCurrent.bank,ActiveRepairRankHeadersCommands.bank,
      CompactComplexNativeCodec.raw,CompactNativeRoleConjugatedLifecycle.rawState,
      CleanSubbank.bank,Tapes.append] using hh.1
  · change (finishedEntry stage rows ell p f v call).tape (numeric i)=_
    simpa only [finishedEntry,setTape,Function.update_of_ne (numeric_ne_source i),merge,
      CompactComplexNonleafRoleMergeCurrent.bank,ActiveRepairRankHeadersCommands.bank,
      CompactComplexNativeCodec.raw,CompactNativeRoleConjugatedLifecycle.rawState,
      CleanSubbank.bank,Tapes.append] using hh.2

theorem roles_blank (call : Networks.ComplexRecursiveCallSchema.Call) (j : Fin c) :
    (finishedEntry stage rows ell p f v call).head (roleTape j)=0 ∧
    (finishedEntry stage rows ell p f v call).tape (roleTape j)=(fun _ => blank) := by
  have hh := CompactComplexNonleafRoleMergeCurrent.output_roles_blank sh rows ell p stage.rho stage.left
    stage.f stage.slots stage.right stage.source.val stage.target.val f v j
  simpa only [finishedEntry,setTape,Function.update_of_ne (role_ne_source j),merge,
    CompactComplexNonleafRoleMergeCurrent.bank] using hh

/-- The exact native child bank needed by real decoded parent return. -/
theorem raw_source (call : Networks.ComplexRecursiveCallSchema.Call) :
    Placement.active CompactComplexNonleafRoleParentContinuation.placement
      (finishedPublic stage rows ell p f v call)=
      CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell p)
        (CompactNativeRoleReservedBridge.sourcePayload sh rows ell (oriented call f) c) := by
  exact CompactComplexNonleafRoleMerge.active_input (finishedEntry stage rows ell p f v call)
    (CompactComplexNativeCodec.raw stage rows ell p) (CompactSpectatorLeafAxis.word (oriented call f))
    (fun _ => fun _ => blank) (headers stage rows ell p f v call)
    (by simp only [finishedEntry,setTape,Function.update_self,and_self])
    (roles_blank stage rows ell p f v call)

def controlSlot (i : Fin 43) : Fin (CompactComplexNonleafRoleEntry.tapes (10+s) c) :=
  Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.controllerSlot i))

theorem control_disjoint (i : Fin 43) (j : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (controlSlot (s:=s) (c:=c) i)≠CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [controlSlot,CompactComplexControllerNativeFrame.controllerSlot,Fin.val_castAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  have := i.isLt
  split_ifs at hv <;> omega

theorem control_ne_source (i : Fin 43) : (controlSlot (s:=s) (c:=c) i)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [controlSlot,source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.controllerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have := i.isLt
  omega

theorem control (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin 43) :
    (finishedEntry stage rows ell p f v call).head (controlSlot i)=v.head (controlSlot i) ∧
    (finishedEntry stage rows ell p f v call).tape (controlSlot i)=v.tape (controlSlot i) := by
  have hh := CompactComplexNonleafRoleMergeCurrent.output_frame sh rows ell p stage.rho stage.left
    stage.f stage.slots stage.right stage.source.val stage.target.val f v
    (Fin.castAdd 7 (controlSlot i)) (control_disjoint i)
  simpa only [finishedEntry,setTape,Function.update_of_ne (control_ne_source i),merge,
    CompactComplexNonleafRoleMergeCurrent.bank,Tapes.append,Fin.addCases_left] using hh

def storageSlot (i : Fin (10+s)) : Fin (CompactComplexNonleafRoleEntry.tapes (10+s) c) :=
  Fin.castAdd 2 (CompactComplexSpectatorTargetBank.oldSlot i)

theorem storage_ne_source (i : Fin (10+s)) : (storageSlot (s:=s) (c:=c) i)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [storageSlot,source,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.storageSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem storage (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin (10+s)) :
    (finishedEntry stage rows ell p f v call).head (storageSlot i)=v.head (storageSlot i) ∧
    (finishedEntry stage rows ell p f v call).tape (storageSlot i)=v.tape (storageSlot i) := by
  have hh := CompactComplexNonleafRoleMergeCurrent.output_storage sh rows ell p stage.rho stage.left
    stage.f stage.slots stage.right stage.source.val stage.target.val f v (Fin.castAdd 43 i)
  simp only [finishedEntry,setTape,Function.update_of_ne (storage_ne_source i)]
  simpa only [merge,CompactComplexNonleafRoleMergeCurrent.bank,storageSlot,CompactComplexSpectatorTargetBank.oldSlot] using hh

def auxSlot (i : Fin 2) : Fin (CompactComplexNonleafRoleEntry.tapes (10+s) c) :=
  Fin.natAdd (permanentTapes (10+s) c) i

theorem aux_ne_source (i : Fin 2) : (auxSlot (s:=s) (c:=c) i)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [auxSlot,source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  omega

theorem aux (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin 2) :
    (finishedEntry stage rows ell p f v call).head (auxSlot i)=v.head (auxSlot i) ∧
    (finishedEntry stage rows ell p f v call).tape (auxSlot i)=v.tape (auxSlot i) := by
  have hh := CompactComplexNonleafRoleMergeCurrent.output_extra sh rows ell p stage.rho stage.left
    stage.f stage.slots stage.right stage.source.val stage.target.val f v i
  simp only [finishedEntry,setTape,Function.update_of_ne (aux_ne_source i)]
  simpa only [merge,CompactComplexNonleafRoleMergeCurrent.bank,auxSlot] using hh

/-- This is the literal output used by the proved tag-three path, rewritten
as its public completed-child bank. It is an equality of computed endpoints. -/
theorem actual_endpoint (call : Networks.ComplexRecursiveCallSchema.Call)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    CompactComplexSourceReadyOrientation.output call
      (CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p stage.rho stage.left stage.f
        stage.slots stage.right stage.source.val stage.target.val f v leaf) f=
      CompactComplexSourceReadyWorkspace.bank (finishedPublic stage rows ell p f v call) leaf
        (SharedBank.empty 10 2) := by
  have hs := CompactComplexSourceReadyNonleafFinalPorts.source sh rows ell p stage.rho stage.left stage.f
    stage.slots stage.right stage.source.val stage.target.val f v leaf
  rw [CompactComplexSourceReadyOrientationInvariants.output_eq _ _ _ hs.1 hs.2]
  change setTape ((((merge stage rows ell p f v).append (SharedBank.empty 7 2)).append leaf).append
    (SharedBank.empty 10 2))
    (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes (Fin.castAdd 7 source)))
    (CompactSpectatorLeafAxis.word (oriented call f)) 0=_
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]
  rfl

def inputAux := SharedBank.payload v (auxSlot (s:=s) (c:=c))

theorem frame (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadyChildReturnPath.frame (finishedPublic stage rows ell p f v call)=
      (inputAux v).append (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=2) (n:=7) with
  | left i =>
    have he : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
        (Fin.natAdd (permanentTapes (10+s) c) (Fin.castAdd 7 i))=Fin.castAdd 7 (auxSlot i) := by
      apply Fin.ext
      rfl
    all_goals simp only [Tapes.reindex,
      Tapes.append,Fin.addCases_left,he,finishedPublic]
    first
    | exact (aux stage rows ell p f v call i).1
    | exact (aux stage rows ell p f v call i).2
  | right i =>
    have he : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
        (Fin.natAdd (permanentTapes (10+s) c) (Fin.natAdd 2 i))=
        Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) i := by
      apply Fin.ext
      change permanentTapes (10+s) c+(2+i.val)=(permanentTapes (10+s) c+2)+i.val
      omega
    all_goals simp only [Tapes.reindex,
      Tapes.append,Fin.addCases_right,he,finishedPublic]

theorem public_control_slot (i : Fin 43) : CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) i=
    Fin.castAdd 7 (controlSlot i) := Fin.ext rfl

theorem public_storage_slot (i : Fin (10+s)) : CompactComplexNonleafRoleChildBank.storage (c:=c) i=
    Fin.castAdd 7 (storageSlot i) := Fin.ext rfl

def immutableSlot (i : Fin 43) : Fin (CompactComplexNonleafRoleEntry.tapes (10+s) c) :=
  Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot i)

theorem immutable_ne_source (i : Fin 43) : (immutableSlot (s:=s) (c:=c) i)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [immutableSlot,source,CompactComplexNativeCodecFrame.originalSlot,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.storageSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem immutable (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin 43) :
    (finishedEntry stage rows ell p f v call).head (immutableSlot i)=v.head (immutableSlot i) ∧
    (finishedEntry stage rows ell p f v call).tape (immutableSlot i)=v.tape (immutableSlot i) := by
  have hh := CompactComplexNonleafRoleMergeCurrent.output_storage sh rows ell p stage.rho stage.left
    stage.f stage.slots stage.right stage.source.val stage.target.val f v (Fin.natAdd (10+s) i)
  simp only [finishedEntry,setTape,Function.update_of_ne (immutable_ne_source i)]
  simpa only [merge,CompactComplexNonleafRoleMergeCurrent.bank,immutableSlot,
    CompactComplexNativeCodecFrame.originalSlot] using hh

def inputImmutable := SharedBank.payload v (immutableSlot (s:=s) (c:=c))

theorem scalarPart_finished (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadyChildReturnPath.scalarPart (finishedPublic stage rows ell p f v call)=inputImmutable v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have he : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
        (Fin.castAdd 9 (CompactComplexNativeCodecFrame.originalSlot i))=
        Fin.castAdd 7 (immutableSlot (s:=s) (c:=c) i) := Fin.ext rfl
    have hh := immutable stage rows ell p f v call i
    simp only [CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,he,
      finishedPublic,Tapes.append,Fin.addCases_left]
  · exact hh.1
  · exact hh.2

theorem inputImmutable_append_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar raw : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    inputImmutable ((CompactComplexNativeCodecFrame.bank control queue scalar raw tail storage payload).append aux)=
      ActiveRepairRankHeadersCommands.bank scalar := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [immutableSlot,CompactComplexNativeCodecFrame.originalSlot,
    CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexControllerNativeFrame.bank,CompactComplexControllerNativeFrame.storageSlot,
    ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
    Tapes.append,Fin.addCases_left,Fin.addCases_right]

end Generic

section Reached
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
variable {stage : Stage sh} {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)

def before := fun wire : CompactComplexEndpointRoleExchange.Wire =>
  h.data (CompactComplexScalarIntegerRows.wireIndex wire)

def sinkFamily (hslots : stage.slots=NativeEndpointCharacterRoles.arity) :=
  CompactComplexSourceReadyCorrectedFinal.family stage hslots ell metadataP (before h)

def joined (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows) :=
  CompactNativeRoleRecombine.recombine sh rows roles ell hd
    (fun j => CompactComplexControllerExactReturn.contracted (n-h.targetValue) (sinkFamily h hslots j))

def returnedPayload (hslots : stage.slots=NativeEndpointCharacterRoles.arity) :=
  CompactComplexControllerExactReturn.returned
    (fun j => CompactComplexStoppedGridHandoff.words (sinkFamily h hslots j)) n h.targetValue
    (CompactComplexSourceReadyCorrectedRoleRejoin.payload (sinkFamily h hslots))

def returnEntry (hslots : stage.slots=NativeEndpointCharacterRoles.arity) :=
  (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail
    (CompactComplexControllerExactReturn.committed h.storage h.targetValue) (returnedPayload h hslots)).append h.aux

def completed (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :=
  finishedPublic stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call

def result (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) := oriented call (joined h hslots hd)

theorem completed_raw_source (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    Placement.active CompactComplexNonleafRoleParentContinuation.placement (completed h hslots hd call)=
      CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell metadataP)
        (CompactNativeRoleReservedBridge.sourcePayload sh rows ell (result h hslots hd call) roles) :=
  raw_source stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call

theorem completed_source (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head (Fin.castAdd 7 (source (s:=10+s) (c:=roles)))=0 ∧
    (completed h hslots hd call).tape (Fin.castAdd 7 (source (s:=10+s) (c:=roles)))=
      CompactSpectatorLeafAxis.word (result h hslots hd call) :=
  source_word stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call

theorem completed_scalar (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadyChildReturnPath.scalarPart (completed h hslots hd call)=
      ActiveRepairRankHeadersCommands.bank h.scalar := by
  exact (scalarPart_finished stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call).trans
    (inputImmutable_append_bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail
      (CompactComplexControllerExactReturn.committed h.storage h.targetValue) (returnedPayload h hslots) h.aux)

theorem completed_control (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin 43) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.control i)=h.control.head i ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.control i)=h.control.tape i := by
  rw [public_control_slot]
  simp only [completed,finishedPublic,Tapes.append,Fin.addCases_left]
  have hh := control stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call i
  simpa only [returnEntry,controlSlot,
    CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexControllerNativeFrame.bank,CompactComplexControllerNativeFrame.controllerSlot,
    Tapes.append,Fin.addCases_left] using hh

theorem completed_storage (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin (10+s)) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.storage i)=
      (CompactComplexControllerExactReturn.committed h.storage h.targetValue).head i ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.storage i)=
      (CompactComplexControllerExactReturn.committed h.storage h.targetValue).tape i := by
  rw [public_storage_slot]
  simp only [completed,finishedPublic,Tapes.append,Fin.addCases_left]
  have hh := storage stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call i
  have hb := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail
    (CompactComplexControllerExactReturn.committed h.storage h.targetValue) (returnedPayload h hslots) i
  simp only [returnEntry,storageSlot,Tapes.append,Fin.addCases_left] at hh
  exact ⟨hh.1.trans hb.1,hh.2.trans hb.2⟩

theorem completed_aux (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) (i : Fin 2) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleParentPayloadContinuation.extra i)=h.aux.head i ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleParentPayloadContinuation.extra i)=h.aux.tape i := by
  have hh := aux stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call i
  simpa only [completed,finishedPublic,returnEntry,auxSlot,
    CompactComplexNonleafRoleParentPayloadContinuation.extra,Tapes.append,Fin.addCases_left,Fin.addCases_right] using hh

theorem completed_frame (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadyChildReturnPath.frame (completed h hslots hd call)=h.aux.append (SharedBank.empty 7 2) := by
  have hh := frame stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call
  have ha : inputAux (returnEntry h hslots)=h.aux := by
    apply congrArg₂ Tapes.mk <;> funext i
    · change (returnEntry h hslots).head (auxSlot i)=h.aux.head i
      simp only [returnEntry,auxSlot,Tapes.append,Fin.addCases_right]
    · change (returnEntry h hslots).tape (auxSlot i)=h.aux.tape i
      simp only [returnEntry,auxSlot,Tapes.append,Fin.addCases_right]
  exact hh.trans (congrArg (fun x => x.append (SharedBank.empty 7 2)) ha)

theorem completed_exponent (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.control 1)=1 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.control 1)=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits e) := by
  have he := h.exponent
  rw [h.exponentValue_eq] at he
  have hc := completed_control h hslots hd call 1
  exact ⟨hc.1.trans he.1,hc.2.trans he.2⟩

theorem completed_control28 (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.control 28)=0 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.control 28)=(fun _ => blank) := by
  have hc := completed_control h hslots hd call 28
  exact ⟨hc.1.trans h.control28_blank.1,hc.2.trans h.control28_blank.2⟩

theorem completed_control29 (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.control 29)=0 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.control 29)=(fun _ => blank) := by
  have hc := completed_control h hslots hd call 29
  exact ⟨hc.1.trans h.control29_blank.1,hc.2.trans h.control29_blank.2⟩

theorem completed_count (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.storage ⟨0,by omega⟩)=0 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.storage ⟨0,by omega⟩)=(fun _ => blank) := by
  have hc := completed_storage h hslots hd call ⟨0,by omega⟩
  have h07 : (⟨0,by omega⟩ : Fin (10+s))≠⟨7,by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv
  have h08 : (⟨0,by omega⟩ : Fin (10+s))≠⟨8,by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv
  have hb : (CompactComplexControllerExactReturn.committed h.storage h.targetValue).head ⟨0,by omega⟩=0 ∧
      (CompactComplexControllerExactReturn.committed h.storage h.targetValue).tape ⟨0,by omega⟩=(fun _ => blank) := by
    simpa only [CompactComplexControllerExactReturn.committed,setTape,
      Function.update_of_ne h07,
      Function.update_of_ne h08,
      CompactComplexSourceReadyActualTable.countHeader] using h.count_blank
  exact ⟨hc.1.trans hb.1,hc.2.trans hb.2⟩

theorem completed_live (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head CompactComplexNonleafRoleChildBank.current=1 ∧
    (completed h hslots hd call).tape CompactComplexNonleafRoleChildBank.current=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits h.targetValue) := by
  have h78 : (⟨7,by omega⟩ : Fin (10+s))≠⟨8,by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv
  have hc := completed_storage h hslots hd call ⟨7,by omega⟩
  simpa only [CompactComplexNonleafRoleChildBank.current,CompactComplexControllerExactReturn.committed,setTape,Function.update_self,
    Function.update_of_ne h78] using hc

theorem completed_target_blank (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed h hslots hd call).head CompactComplexNonleafRoleChildBank.target=0 ∧
    (completed h hslots hd call).tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank) := by
  have hc := completed_storage h hslots hd call ⟨8,by omega⟩
  simpa only [CompactComplexNonleafRoleChildBank.target,CompactComplexControllerExactReturn.committed,setTape,Function.update_self] using hc

theorem completed_saved (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 pcStack)))
      ((completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 pcStack))) := by
  have hs := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack v
  have hv := (congrArg CompactComplexSourceReadyScalarWorkspace.permanent h.canonical_bank).trans
    (CompactComplexSourceReadyReachedEventInvariant.canonical_permanent _ _)
  rw [hv] at hs
  have hb := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload (Fin.natAdd 10 pcStack)
  have ha := h.saved_calls
  unfold CompactComplexSourceReadySavedCallHistory.Reached at ha
  rw [hs.1,hs.2] at ha
  change (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload).head
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.head _ ∧
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload).tape
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.tape _ at hb
  rw [hb.1,hb.2] at ha
  have hc := completed_storage h hslots hd call (Fin.natAdd 10 pcStack)
  have hp := CompactComplexSourceReadyNonleafFinalPorts.committed_saved h.storage h.targetValue pcStack
  rw [hc.1,hc.2,hp.1,hp.2]
  exact ha

/-- The endpoint in the paid aligned tag-three theorem is exactly this
public completed bank with the canonical leaf/work suffix. -/
theorem completed_endpoint (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadyOrientation.output call
      (CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell metadataP stage.rho stage.left stage.f
        stage.slots stage.right stage.source.val stage.target.val (joined h hslots hd)
        (returnEntry h hslots) (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2))
      (joined h hslots hd)=CompactComplexSourceReadyWorkspace.ready (completed h hslots hd call) :=
  actual_endpoint stage rows ell metadataP (joined h hslots hd) (returnEntry h hslots) call _

theorem completed_dormant (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (snapshot : CompactComplexSourceReadyReachedDormantFrameInvariant.Snapshot s)
    (settled : CompactComplexSourceReadyReachedDormantFrameInvariant.Settled snapshot h.storage h.aux) :
    (∀ i,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
        snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
      (completed h hslots hd call).head (CompactComplexNonleafRoleChildBank.storage i)=snapshot.storage.head i ∧
      (completed h hslots hd call).tape (CompactComplexNonleafRoleChildBank.storage i)=snapshot.storage.tape i) ∧
    (completed h hslots hd call).head (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=snapshot.aux.head 0 ∧
    (completed h hslots hd call).tape (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=snapshot.aux.tape 0 := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have h7 := CompactComplexSourceReadyReachedDormantFrameInvariant.protected_ne_live _ _ _ _ hi
    have h8 : i≠(⟨8,by omega⟩ : Fin (10+s)) := by
      rcases hi with rfl|rfl|rfl|rfl <;>
        intro he <;> have hv := congrArg Fin.val he <;> simp only [Fin.val_natAdd] at hv <;> omega
    have hp := CompactComplexSourceReadyReachedDormantFrameInvariant.settled_storage settled i hi
    have hc := completed_storage h hslots hd call i
    simp only [CompactComplexControllerExactReturn.committed,setTape,Function.update_of_ne h7,
      Function.update_of_ne h8] at hc
    exact ⟨hc.1.trans hp.1,hc.2.trans hp.2⟩
  · exact (completed_aux h hslots hd call 0).1.trans
      (CompactComplexSourceReadyReachedDormantFrameInvariant.settled_aux settled).1
  · exact (completed_aux h hslots hd call 0).2.trans
      (CompactComplexSourceReadyReachedDormantFrameInvariant.settled_aux settled).2

end Reached
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildBoundary
