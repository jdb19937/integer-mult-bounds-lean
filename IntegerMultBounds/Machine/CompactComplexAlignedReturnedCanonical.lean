module

public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedCallerPayload

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedReturnedCanonical
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSourceReadyWorkspace (ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller canonical)
open CompactComplexSourceReadyReachedReturnInvariant (roleData returnedCaller)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexNonleafSpectatorTargetRestore (entry)
open CompactComplexAlignedReachedChildReturnPath (mid callerAux)
variable {s c : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount

private theorem entry_flat (w : Tapes (permanentTapes (10+s) c) 2) (aux : Tapes 2 2) :
    entry w (aux.append (SharedBank.empty 7 2))=
      (CompactComplexSourceReadyScalarChildReadiness.entryBank w aux).append (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=permanentTapes (10+s) c+2) (n:=7) with
  | left i =>
    induction i using Fin.addCases (m:=permanentTapes (10+s) c) (n:=2) with
    | left i =>
      have he : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c)
          (Fin.castAdd 7 (Fin.castAdd 2 i))=Fin.castAdd 9 i := by
        apply Fin.ext
        rfl
      simp only [Equiv.symm_symm,he,
        CompactComplexSourceReadyScalarChildReadiness.entryBank,Tapes.append,Fin.addCases_left]
    | right i =>
      have he : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c)
          (Fin.castAdd 7 (Fin.natAdd (permanentTapes (10+s) c) i))=
          Fin.natAdd (permanentTapes (10+s) c) (Fin.castAdd 7 i) := by
        apply Fin.ext
        rfl
      simp only [Equiv.symm_symm,he,
        CompactComplexSourceReadyScalarChildReadiness.entryBank,Tapes.append,
        Fin.addCases_left,Fin.addCases_right]
  | right i =>
    have he : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c)
        (Fin.natAdd (permanentTapes (10+s) c+2) i)=
        Fin.natAdd (permanentTapes (10+s) c) (Fin.natAdd 2 i) := by
      apply Fin.ext
      simp only [CompactComplexNonleafSpectatorTargetRestore.entryEquiv,finCongr_apply,
        Fin.val_cast,Fin.val_natAdd]
      omega
    simp only [Equiv.symm_symm,he,
      CompactComplexSourceReadyScalarChildReadiness.entryBank,Tapes.append,
      Fin.addCases_right]

theorem entry_ready (w : Tapes (permanentTapes (10+s) c) 2) (aux : Tapes 2 2) :
    ready (entry w (aux.append (SharedBank.empty 7 2)))=
      ready ((CompactComplexSourceReadyScalarChildReadiness.entryBank w aux).append (SharedBank.empty 7 2)) :=
  congrArg ready (entry_flat w aux)

theorem entry_bank (w : Tapes (permanentTapes (10+s) c) 2) (aux : Tapes 2 2) :
    CompactComplexSourceReadyWorkspace.bank (entry w (aux.append (SharedBank.empty 7 2)))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)=
      ready ((CompactComplexSourceReadyScalarChildReadiness.entryBank w aux).append (SharedBank.empty 7 2)) :=
  entry_ready w aux

section Reached
variable {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)

theorem normalized_endpoint (selected : Fin roles) (gap : ℕ)
    (child : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) :
    CompactComplexSourceReadyWorkspace.bank
      (entry (bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
        tail storage (CompactComplexStoppedGridHandoff.payload sh (rows/roles) ell (fun _ => blank) 0
          (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected (roleData h) child)))
        ((callerAux (caller h)).append (SharedBank.empty 7 2)))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)=
      canonical (returnedCaller h selected gap child control queue scalar tail storage) h.aux := by
  rw [CompactComplexAlignedReturnedCallerPayload.caller_aux h]
  exact entry_bank (s:=s) (c:=roles)
    (returnedCaller h selected gap child control queue scalar tail storage) h.aux

theorem normalized_of_frame (selected : Fin roles) (gap : ℕ)
    (child : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (storage : Tapes (10+s) 2)
    (hframe : CompactComplexSourceReadyChildReturnPath.frame u=
      (callerAux (caller h)).append (SharedBank.empty 7 2)) :
    CompactComplexSourceReadyWorkspace.bank
      (entry (bank (CompactComplexSourceReadyChildReturnPath.controlPart u)
        (CompactComplexSourceReadyChildReturnPath.queuePart u) scalar
        (CompactComplexNativeCodec.raw stage rows ell metadataP)
        (CompactComplexSourceReadyChildReturnPath.tailPart u) storage
        (CompactComplexStoppedGridHandoff.payload sh (rows/roles) ell (fun _ => blank) 0
          (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected (roleData h) child)))
        (CompactComplexSourceReadyChildReturnPath.frame u))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)=
      canonical (returnedCaller h selected gap child
        (CompactComplexSourceReadyChildReturnPath.controlPart u)
        (CompactComplexSourceReadyChildReturnPath.queuePart u) scalar
        (CompactComplexSourceReadyChildReturnPath.tailPart u) storage) h.aux := by
  rw [hframe]
  exact normalized_endpoint h selected gap child
    (CompactComplexSourceReadyChildReturnPath.controlPart u)
    (CompactComplexSourceReadyChildReturnPath.queuePart u) scalar
    (CompactComplexSourceReadyChildReturnPath.tailPart u) storage

/-- The genuine mid-frame theorem supplies canonical return geometry. -/
theorem mid_endpoint {left k : ℕ} (selected : Fin roles) (gap : ℕ)
    (child : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (headerStack liveStack : Fin s) (f : ℤ → Fin 6) (head : ℤ)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (exponent parentLive childLive : ℕ)
    (rho : Fin sh.chunk) (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (payload : Tapes (1+roles) 2) (returnedWord : ℤ → Fin 6)
    (scalar : ActiveRepairRankHeadersCommands.State) (nextStorage : Tapes (10+s) 2) :
    let m := mid selected (caller h) u headerStack liveStack f head liveFrame liveHead
      exponent parentLive childLive rho visit ha pair rows ell metadataP payload returnedWord
    CompactComplexSourceReadyWorkspace.bank
      (entry (bank (CompactComplexSourceReadyChildReturnPath.controlPart m)
        (CompactComplexSourceReadyChildReturnPath.queuePart m) scalar
        (CompactComplexNativeCodec.raw stage rows ell metadataP)
        (CompactComplexSourceReadyChildReturnPath.tailPart m) nextStorage
        (CompactComplexStoppedGridHandoff.payload sh (rows/roles) ell (fun _ => blank) 0
          (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected (roleData h) child)))
        (CompactComplexSourceReadyChildReturnPath.frame m))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)=
      canonical (returnedCaller h selected gap child
        (CompactComplexSourceReadyChildReturnPath.controlPart m)
        (CompactComplexSourceReadyChildReturnPath.queuePart m) scalar
        (CompactComplexSourceReadyChildReturnPath.tailPart m) nextStorage) h.aux := by
  dsimp only
  apply normalized_of_frame h selected gap child _ scalar nextStorage
  exact CompactComplexAlignedReachedChildReturnPath.mid_frame selected (caller h) u
    headerStack liveStack f head liveFrame liveHead exponent parentLive childLive
    rho visit ha pair rows ell metadataP payload returnedWord

end Reached
end
end IntegerMultBounds.Machine.CompactComplexAlignedReturnedCanonical
