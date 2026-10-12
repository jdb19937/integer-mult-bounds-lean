module

public import IntegerMultBounds.Machine.CompactComplexAlignedCapturedReturnPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant

/-! Named stack ports of the balanced physical parent return. Consumed header,
live and target frames restore their literal prior words; unrelated ports are
preserved by the existing physical return frame theorem. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames
noncomputable section
open CompactComplexNonleafRoleChildBank (tapes storage)
open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexSourceReadyChildReturnPath (storagePart)
open CompactComplexAlignedReachedChildReturnPath (mid source_storage storage_read)
open CompactComplexChildHeadersData (parent)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexNativeCodec (raw)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ} {sh : CompactGadgetReservationShape.Shape} {left k : ℕ}

private theorem storage_injective : Function.Injective (storage (s:=s) (c:=c)) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem saved_ne_small (stack : Fin s) (j : Fin (10+s)) (hj : j.val<10) :
    storage (s:=s) (c:=c) (Fin.natAdd 10 stack)≠storage j := by
  intro he
  have hv := congrArg Fin.val (storage_injective he)
  simp only [Fin.val_natAdd] at hv
  omega

private theorem storage_outside (j : Fin (10+s)) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    placement (s:=s) (c:=c) (Fin.castAdd _ i)≠storage j := by
  unfold placement
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  intro h
  have hv := congrArg Fin.val h
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

private theorem replaced_storage (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (j : Fin (10+s)) :
    (Placement.replace placement v small).head (storage j)=v.head (storage j) ∧
      (Placement.replace placement v small).tape (storage j)=v.tape (storage j) := by
  obtain ⟨i,he⟩ := (placement (s:=s) (c:=c)).surjective (storage j)
  rw [←he]
  induction i using Fin.addCases with
  | left i => exact (storage_outside j i he).elim
  | right i => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

section Ports
variable (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6)

/-- Physical geometry restoration returns the consumed header-stack word and
head, and subsequent live/payload restoration leaves that named port intact. -/
theorem mid_header (hstacks : headerStack≠liveStack) :
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)).head
        (Fin.natAdd 10 headerStack)=p ∧
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)).tape
        (Fin.natAdd 10 headerStack)=f := by
  let row := CompactComplexNonleafRoleParentContinuation.output v headerStack f p e
    rho visit ha pair rows ell metadataP payload
  let live := CompactComplexNonleafRoleParentLiveContinuation.liveOutput row liveStack liveFrame liveHead
    parentLive childLive
  have hs := source_storage selected caller live returned (Fin.natAdd 10 headerStack)
  have hr := replaced_storage (s:=s) (c:=c)
    (CompactComplexNonleafRoleParentBank.output v headerStack f p
      (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e)
    (CompactNativeRoleOriginal.bank (raw (parent rho visit ha pair) rows ell metadataP) payload)
    (Fin.natAdd 10 headerStack)
  have hp := CompactComplexNonleafRoleParentBank.output_stack v headerStack f p
    (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e
  have hn : storage (s:=s) (c:=c) (Fin.natAdd 10 headerStack)≠storage (Fin.natAdd 10 liveStack) := by
    intro he
    exact hstacks (Fin.ext (by
      have hv := congrArg Fin.val (storage_injective he)
      simp only [Fin.val_natAdd] at hv
      omega))
  have hl := CompactComplexNonleafRoleParentLiveContinuation.live_output_frame row liveStack
    liveFrame liveHead parentLive childLive (storage (Fin.natAdd 10 headerStack))
    (saved_ne_small headerStack ⟨7,by omega⟩ (by change (7:ℕ)<10; decide))
    (saved_ne_small headerStack ⟨8,by omega⟩ (by change (8:ℕ)<10; decide)) hn
  refine ⟨hs.1.trans ((storage_read live _).1.trans (hl.1.trans (hr.1.trans hp.1))),
    hs.2.trans ((storage_read live _).2.trans (hl.2.trans (hr.2.trans hp.2)))⟩

/-- The actual live continuation consumes exactly its own frame and restores
its older word and head, regardless of the numerical child live value. -/
theorem mid_live :
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)).head
        (Fin.natAdd 10 liveStack)=liveHead ∧
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)).tape
        (Fin.natAdd 10 liveStack)=liveFrame := by
  let live := CompactComplexNonleafRoleParentLiveContinuation.output v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload
  have hs := source_storage selected caller live returned (Fin.natAdd 10 liveStack)
  have hp : live.head (storage (Fin.natAdd 10 liveStack))=liveHead ∧
      live.tape (storage (Fin.natAdd 10 liveStack))=liveFrame := by
    simp only [live,CompactComplexNonleafRoleParentLiveContinuation.output,
      CompactComplexNonleafRoleParentLiveContinuation.liveOutput,
      CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,setTape,
      Function.update_of_ne (saved_ne_small liveStack ⟨7,by omega⟩ (by change (7:ℕ)<10; decide)),
      Function.update_self,and_self]
  exact ⟨hs.1.trans ((storage_read live _).1.trans hp.1),
    hs.2.trans ((storage_read live _).2.trans hp.2)⟩

/-- The advanced-live commit and target pop preserve both older stack words. -/
theorem final_named (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (parentTarget : ℕ)
    (hstacks : headerStack≠liveStack) :
    let middle := mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    let finalStore := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart (s:=s) (c:=c) middle)
      childLive targetFrame targetHead parentTarget
    (finalStore.head (Fin.natAdd 10 headerStack)=p ∧ finalStore.tape (Fin.natAdd 10 headerStack)=f) ∧
    (finalStore.head (Fin.natAdd 10 liveStack)=liveHead ∧ finalStore.tape (Fin.natAdd 10 liveStack)=liveFrame) ∧
    (finalStore.head ⟨9,by omega⟩=targetHead ∧ finalStore.tape ⟨9,by omega⟩=targetFrame) := by
  dsimp only
  let middle := mid selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned
  have frame (stack : Fin s) := CompactComplexNonleafSpectatorTargetRestore.restoredStorage_frame
    (storagePart (s:=s) (c:=c) middle) childLive targetFrame targetHead parentTarget (Fin.natAdd 10 stack)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)
  have hh := mid_header selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned hstacks
  have hl := mid_live selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned
  have ht := CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports
    (storagePart (s:=s) (c:=c) middle) childLive targetFrame targetHead parentTarget
  exact ⟨⟨(frame headerStack).1.trans hh.1,(frame headerStack).2.trans hh.2⟩,
    ⟨(frame liveStack).1.trans hl.1,(frame liveStack).2.trans hl.2⟩,ht.2.2.2.2⟩

/-- The original associated call history determines the older PC frame,
without assuming equality of any complete dormant storage bank. -/
theorem pc_prior (pcStack : Fin s) (origin : ℤ)
    (calls : List Networks.ComplexRecursiveCallSchema.Call) (old : Tapes (10+s) 2)
    (hbefore : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart (s:=s) (c:=c) v).tape (Fin.natAdd 10 pcStack))
      ((storagePart (s:=s) (c:=c) v).head (Fin.natAdd 10 pcStack)))
    (hparent : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (old.tape (Fin.natAdd 10 pcStack)) (old.head (Fin.natAdd 10 pcStack))) :
    (storagePart (s:=s) (c:=c) v).head (Fin.natAdd 10 pcStack)=old.head (Fin.natAdd 10 pcStack) ∧
    (storagePart (s:=s) (c:=c) v).tape (Fin.natAdd 10 pcStack)=old.tape (Fin.natAdd 10 pcStack) := by
  have hp := CompactComplexSourceReadySettledFrames.saved_calls_unique hbefore hparent
  exact ⟨hp.2,hp.1⟩

/-- Returning the actual individually captured header/live/target frames and
the uniquely associated older PC frame retains an ancestor's Settled proof.
Auxiliary payload recovery is represented by its literal older auxiliary pair. -/
theorem balanced_settled
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (parentTarget : ℕ)
    (pcStack : Fin s) (old : Tapes (10+s) 2) (aux : Tapes 2 2)
    (snapshot : CompactComplexSourceReadyReachedDormantFrameInvariant.Snapshot s)
    (hsettled : CompactComplexSourceReadyReachedDormantFrameInvariant.Settled snapshot old aux)
    (hheader : snapshot.headerStack=headerStack) (hlive : snapshot.liveStack=liveStack)
    (hpc : snapshot.pcStack=pcStack)
    (hstacks : headerStack≠liveStack) (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
    (hf : p=old.head (Fin.natAdd 10 headerStack) ∧ f=old.tape (Fin.natAdd 10 headerStack))
    (hl : liveHead=old.head (Fin.natAdd 10 liveStack) ∧ liveFrame=old.tape (Fin.natAdd 10 liveStack))
    (ht : targetHead=old.head ⟨9,by omega⟩ ∧ targetFrame=old.tape ⟨9,by omega⟩)
    (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (hbefore : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart (s:=s) (c:=c) v).tape (Fin.natAdd 10 pcStack))
      ((storagePart (s:=s) (c:=c) v).head (Fin.natAdd 10 pcStack)))
    (hparent : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (old.tape (Fin.natAdd 10 pcStack)) (old.head (Fin.natAdd 10 pcStack))) :
    let middle := mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    CompactComplexSourceReadyReachedDormantFrameInvariant.Settled snapshot
      (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart (s:=s) (c:=c) middle)
        childLive targetFrame targetHead parentTarget) aux := by
  dsimp only
  have named := final_named selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    targetFrame targetHead parentTarget hstacks
  have prior := pc_prior v pcStack origin calls old hbefore hparent
  have pc := CompactComplexAlignedReachedChildReturnPath.final_storage selected caller v headerStack liveStack
    f p liveFrame liveHead e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    targetFrame targetHead parentTarget (Fin.natAdd 10 pcStack)
    (by intro he; exact hpcHeader (Fin.ext (by
      have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)))
    (by intro he; exact hpcLive (Fin.ext (by
      have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)))
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)
  apply CompactComplexSourceReadySettledFrames.settled_of_port_eq hsettled
  · intro j hj
    rw [hheader,hlive,hpc] at hj
    rcases hj with rfl|rfl|rfl|rfl
    · exact ⟨named.1.1.trans hf.1,named.1.2.trans hf.2⟩
    · exact ⟨named.2.1.1.trans hl.1,named.2.1.2.trans hl.2⟩
    · exact ⟨pc.1.trans prior.1,pc.2.trans prior.2⟩
    · exact ⟨named.2.2.1.trans ht.1,named.2.2.2.trans ht.2⟩
  · exact ⟨rfl,rfl⟩

end Ports

section Reached
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes permanent)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical caller)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller)
open CompactComplexSourceReadyReachedBasisInvariant (replacementCaller)
open CompactComplexAlignedPoppedReturnReadiness (popped)
variable {stage : ActivePrefixStageParameters.Stage sh}
  {rows ell metadataP e pNum C axes baseline levels frames returned pref n : ℕ}
  {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {pv : Tapes (nodeTapes s roles) 2}

attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  CompactComplexCompletedLiveLower.schedule

/-- Recover the literal parent storage-PC association from the actual reached
bank and its saved-calls field, rather than adding another history premise. -/
theorem parent_saved_associated
    (h : Reached stage rows ell metadataP e pNum C axes baseline levels frames returned pref n pcStack origin calls pv) :
    CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (h.storage.tape (Fin.natAdd 10 pcStack)) (h.storage.head (Fin.natAdd 10 pcStack)) := by
  have hv := (congrArg permanent h.canonical_bank).trans
    (CompactComplexSourceReadyReachedEventInvariant.canonical_permanent _ _)
  have hs := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack pv
  rw [hv] at hs
  have hb := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload
    (Fin.natAdd 10 pcStack)
  change (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload).head
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.head _ ∧
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload).tape
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.tape _ at hb
  rw [hb.1,hb.2] at hs
  have history := h.saved_calls
  unfold CompactComplexSourceReadySavedCallHistory.Reached at history
  rw [hs.1,hs.2] at history
  exact history

/-- The actual return-storage computation, using individually captured parent
words and the physically popped child bank. -/
def capturedStorage
    (h : Reached stage rows ell metadataP e pNum C axes baseline levels frames returned pref n pcStack origin calls pv)
    (j : Fin roles) (u : Tapes (tapes s roles) 2)
    (older : ℤ → Fin 6) (top : ℤ) (headerStack liveStack : Fin s)
    (gap : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (payload : Tapes (1+roles) 2) (result : ℤ → Fin 6) :=
  CompactComplexNonleafSpectatorTargetRestore.restoredStorage
    (storagePart (s:=s) (c:=roles)
      (mid j (caller h) (popped u pcStack older top) headerStack liveStack
        (h.storage.tape (Fin.natAdd 10 headerStack)) (h.storage.head (Fin.natAdd 10 headerStack))
        (h.storage.tape (Fin.natAdd 10 liveStack)) (h.storage.head (Fin.natAdd 10 liveStack))
        e n (n+gap) rho visit ha pair rows ell metadataP payload result))
    (n+gap) (h.storage.tape ⟨9,by omega⟩) (h.storage.head ⟨9,by omega⟩) h.targetValue

/-- The genuine popped-PC endpoint and captured frames retain settled parent
ports on the actual computed return-storage bank. -/
theorem captured_storage_settled
    (h : Reached stage rows ell metadataP e pNum C axes baseline levels frames returned pref n pcStack origin calls pv)
    (j : Fin roles) (u : Tapes (tapes s roles) 2)
    (older : ℤ → Fin 6) (top : ℤ)
    (ho : CompactComplexSourceReadySavedCallHistory.Associated origin calls older top)
    (headerStack liveStack : Fin s) (snapshot : Snapshot s)
    (hsettled : Settled snapshot h.storage h.aux)
    (hheader : snapshot.headerStack=headerStack) (hlive : snapshot.liveStack=liveStack)
    (hpc : snapshot.pcStack=pcStack)
    (hstacks : headerStack≠liveStack) (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
    (gap : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (payload : Tapes (1+roles) 2) (result : ℤ → Fin 6) :
    Settled snapshot (capturedStorage h j u older top headerStack liveStack gap rho visit ha pair payload result) h.aux := by
  have hs := CompactComplexAlignedPoppedReturnPorts.popped_saved_associated
    u pcStack older top origin calls ho
  have before : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart (s:=s) (c:=roles) (popped u pcStack older top)).tape (Fin.natAdd 10 pcStack))
      ((storagePart (s:=s) (c:=roles) (popped u pcStack older top)).head (Fin.natAdd 10 pcStack)) := by
    rw [(storage_read (popped u pcStack older top) (Fin.natAdd 10 pcStack)).1,
      (storage_read (popped u pcStack older top) (Fin.natAdd 10 pcStack)).2]
    exact hs
  exact balanced_settled j (caller h) (popped u pcStack older top) headerStack liveStack
    (h.storage.tape (Fin.natAdd 10 headerStack)) (h.storage.head (Fin.natAdd 10 headerStack))
    (h.storage.tape (Fin.natAdd 10 liveStack)) (h.storage.head (Fin.natAdd 10 liveStack))
    e n (n+gap) rho visit ha pair rows ell metadataP payload result
    (h.storage.tape ⟨9,by omega⟩) (h.storage.head ⟨9,by omega⟩) h.targetValue
    pcStack h.storage h.aux snapshot hsettled hheader hlive hpc hstacks hpcHeader hpcLive
    ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ origin calls before (parent_saved_associated h)

/-- Actual returned numerical and inverse-basis witnesses retain Settled.
Their storage and auxiliary fields are read back from their literal canonical
endpoints, with no assumed return invariant or whole-bank equality. -/
theorem captured_final_settled
    (h : Reached stage rows ell metadataP e pNum C axes baseline levels frames returned pref n pcStack origin calls pv)
    (j : Fin roles) (u : Tapes (tapes s roles) 2)
    (older : ℤ → Fin 6) (top : ℤ)
    (ho : CompactComplexSourceReadySavedCallHistory.Associated origin calls older top)
    (headerStack liveStack : Fin s) (snapshot : Snapshot s)
    (hsettled : Settled snapshot h.storage h.aux)
    (hheader : snapshot.headerStack=headerStack) (hlive : snapshot.liveStack=liveStack)
    (hpc : snapshot.pcStack=pcStack)
    (hstacks : headerStack≠liveStack) (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
    (gap volume : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (payload : Tapes (1+roles) 2) (result : ℤ → Fin 6)
    (child : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2)
    (hn : Reached stage rows ell metadataP e pNum C axes baseline levels frames (returned+volume) pref
      (n+gap) pcStack origin calls
      (canonical (returnedCaller h j gap child control queue scalar tail
        (capturedStorage h j u older top headerStack liveStack gap rho visit ha pair payload result)) h.aux))
    (after : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (final : Reached stage rows ell metadataP e pNum C axes baseline levels frames (returned+volume) pref
      (n+gap) pcStack origin calls (canonical (replacementCaller hn j after) hn.aux)) :
    Settled snapshot hn.storage hn.aux ∧ Settled snapshot final.storage final.aux := by
  have storage := captured_storage_settled h j u older top ho headerStack liveStack snapshot
    hsettled hheader hlive hpc hstacks hpcHeader hpcLive gap rho visit ha pair payload result
  obtain ⟨hs,haux⟩ := CompactComplexSourceReadySettledEventInvariant.canonical_fields hn _ h.aux rfl
  simp only [returnedCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at hs
  have reached : Settled snapshot hn.storage hn.aux := by
    rw [hs,haux]
    exact storage
  obtain ⟨hfinal,hfinalAux⟩ := CompactComplexSourceReadySettledEventInvariant.canonical_fields final _ hn.aux rfl
  simp only [replacementCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at hfinal
  refine ⟨reached,?_⟩
  rw [hfinal,hfinalAux]
  exact reached

end Reached

end
end IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames
