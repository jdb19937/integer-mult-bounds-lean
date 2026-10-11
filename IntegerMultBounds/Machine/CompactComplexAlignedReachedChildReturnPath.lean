module

public import IntegerMultBounds.Machine.CompactComplexAlignedChildReturnPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant

/-! Literal return-fragment preservation for the reached child-return path.
The original parent continuation supplies the actual advanced live word,
restored target and exponent; dormant completion supplies only saved prefixes.
No whole returned-bank equality or recursive execution is assumed. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedReachedChildReturnPath
noncomputable section
open CompactComplexNonleafRoleChildBank (tapes storage)
open CompactComplexSourceReadyChildReturnPath (controlPart storagePart)
open CompactComplexChildHeadersData (parent)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexNativeCodec (raw)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ} {sh : CompactGadgetReservationShape.Shape} {left k : ℕ}

private theorem placed_frame {L R T a : ℕ} (placement : Fin (L+R) ≃ Fin T)
    (v : Tapes T a) (small : Tapes L a) (port : Fin T)
    (hport : ∀ i,port≠placement (Fin.castAdd R i)) :
    (Placement.replace placement v small).head port=v.head port ∧
      (Placement.replace placement v small).tape port=v.tape port := by
  obtain ⟨i,rfl⟩ := placement.surjective port
  induction i using Fin.addCases with
  | left i => exact (hport i rfl).elim
  | right i => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

private theorem controller_outside (j : Fin 43)
    (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j≠CompactComplexNonleafRoleParentContinuation.placement
      (Fin.castAdd _ i) := by
  unfold CompactComplexNonleafRoleParentContinuation.placement
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  intro he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  dsimp only [CompactComplexNonleafRoleSplit.slot,CompactComplexNonleafRoleChildBank.control] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  split_ifs at hv <;> omega

/-- Row-header restoration preserves every actual controller tape. -/
theorem row_control (v : Tapes (tapes s c) 2) (headerStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (j : Fin 43) :
    let previous := CompactComplexNonleafRoleParentBank.output v headerStack f p
      (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e
    let next := CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit ha pair
      rows ell metadataP payload
    next.head (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)=previous.head (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) ∧
      next.tape (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)=previous.tape (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) := by
  dsimp only
  exact placed_frame _ _ _ _ (controller_outside j)

private theorem storage_ne_control (j : Fin (10+s)) (i : Fin 43) :
    CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) i≠storage (s:=s) (c:=c) j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [CompactComplexNonleafRoleChildBank.control,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Physical live restoration retains every complete controller word. -/
theorem live_control (v : Tapes (tapes s c) 2) (liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (parentLive childLive : ℕ) (j : Fin 43) :
    (CompactComplexNonleafRoleParentLiveContinuation.liveOutput v liveStack f p parentLive childLive).head
      (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)=v.head (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) ∧
    (CompactComplexNonleafRoleParentLiveContinuation.liveOutput v liveStack f p parentLive childLive).tape
      (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)=v.tape (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) :=
  CompactComplexNonleafRoleParentLiveContinuation.live_output_frame v liveStack f p parentLive childLive
    (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) (storage_ne_control _ _) (storage_ne_control _ _) (storage_ne_control _ _)

private theorem controller_slot (j : Fin 43) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (Fin.castAdd c (CompactComplexControllerNativeFrame.controllerSlot j)))=CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j :=
  Fin.ext rfl

/-- Actual permanent payload recovery leaves all controller words intact. -/
theorem source_control (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) (j : Fin 43) :
    (controlPart (s:=s) (c:=c) (CompactComplexNonleafRoleSourceReturn.output selected caller v returned)).head j=
      (controlPart (s:=s) (c:=c) v).head j ∧
    (controlPart (s:=s) (c:=c) (CompactComplexNonleafRoleSourceReturn.output selected caller v returned)).tape j=
      (controlPart (s:=s) (c:=c) v).tape j := by
  have hn : ¬CompactComplexNonleafRoleReturnFrames.Core
      (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.controllerSlot (s:=10+s+43) j))) := by
    rw [CompactComplexSourceReadyChildReturnPath.core_iff]
    have hj := j.isLt
    simp only [CompactComplexControllerNativeFrame.controllerSlot,Fin.val_castAdd] at *
    omega
  have h := CompactComplexNonleafRoleSourceReturn.output_frame selected caller v returned _ hn
  have hi : Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
      (CompactComplexControllerNativeFrame.controllerSlot (s:=10+s+43) j)))=
      CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j := Fin.ext rfl
  rw [hi] at h
  simpa only [controlPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
    Tapes.reindex,controller_slot] using h

/-- Read a projected controller word at its literal original public port. -/
theorem control_read (v : Tapes (tapes s c) 2) (j : Fin 43) :
    (controlPart (s:=s) (c:=c) v).head j=v.head (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) ∧ (controlPart (s:=s) (c:=c) v).tape j=v.tape (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) := by
  simp only [controlPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
    Tapes.reindex,controller_slot,and_self]

private theorem controlPart_update (v : Tapes (tapes s c) 2) (i : Fin 43)
    (f : ℤ → Fin 6) (p : ℤ) :
    controlPart (s:=s) (c:=c) (setTape v (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) i) f p)=
      setTape (controlPart (s:=s) (c:=c) v) i f p := by
  have hinj : Function.Injective (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c)) := by
    intro i j he
    have hv := congrArg Fin.val he
    exact Fin.ext hv
  apply congrArg₂ Tapes.mk
  · funext j
    simp only [controlPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
      Tapes.reindex,controller_slot,setTape,Function.update_apply,hinj.eq_iff]
  · funext j
    simp only [controlPart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
      Tapes.reindex,controller_slot,setTape,Function.update_apply,hinj.eq_iff]

private theorem controlPart_eq (v w : Tapes (tapes s c) 2)
    (h : ∀ j,v.head (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)=w.head (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j) ∧
      v.tape (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)=w.tape (CompactComplexNonleafRoleChildBank.control (s:=s) (c:=c) j)) :
    controlPart (s:=s) (c:=c) v=controlPart (s:=s) (c:=c) w := by
  apply congrArg₂ Tapes.mk
  · funext j
    exact (control_read (s:=s) (c:=c) v j).1.trans ((h j).1.trans (control_read (s:=s) (c:=c) w j).1.symm)
  · funext j
    exact (control_read (s:=s) (c:=c) v j).2.trans ((h j).2.trans (control_read (s:=s) (c:=c) w j).2.symm)

/-- Real decoded geometry return installs the original exponent and retains
the other actual controller tapes, before row/live/payload restoration. -/
theorem geometry_control (v : Tapes (tapes s c) 2) (headerStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) :
    controlPart (s:=s) (c:=c) (CompactComplexNonleafRoleParentBank.output v headerStack f p data e)=
      setTape (controlPart (s:=s) (c:=c) v) 1 (BinaryDescriptorStack.descriptor (bits e)) 1 := by
  have hr : controlPart (s:=s) (c:=c) (CompactComplexNonleafRoleParentBank.restored v headerStack f p data)=
      controlPart (s:=s) (c:=c) v := by
    apply congrArg₂ Tapes.mk
    · funext j
      exact (control_read (s:=s) (c:=c) _ j).1.trans
        ((CompactComplexNonleafRoleParentBank.restored_control v headerStack f p data j).1.trans
          (control_read (s:=s) (c:=c) v j).1.symm)
    · funext j
      exact (control_read (s:=s) (c:=c) _ j).2.trans
        ((CompactComplexNonleafRoleParentBank.restored_control v headerStack f p data j).2.trans
          (control_read (s:=s) (c:=c) v j).2.symm)
  unfold CompactComplexNonleafRoleParentBank.output CompactComplexNonleafRoleParentBank.ascended
  rw [controlPart_update,hr]

private theorem storage_slot (j : Fin (10+s)) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexSpectatorTargetBank.oldSlot (s:=10+s) (c:=c) j))=storage (s:=s) (c:=c) j :=
  Fin.ext rfl

/-- Read an actual projected storage tape at its original public port. -/
theorem storage_read (v : Tapes (tapes s c) 2) (j : Fin (10+s)) :
    (storagePart (s:=s) (c:=c) v).head j=v.head (storage (s:=s) (c:=c) j) ∧ (storagePart (s:=s) (c:=c) v).tape j=v.tape (storage (s:=s) (c:=c) j) := by
  simp only [storagePart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
    Tapes.reindex,storage_slot,and_self]

/-- Permanent payload recovery preserves all named storage words. -/
theorem source_storage (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) (j : Fin (10+s)) :
    (storagePart (s:=s) (c:=c) (CompactComplexNonleafRoleSourceReturn.output selected caller v returned)).head j=
      (storagePart (s:=s) (c:=c) v).head j ∧
    (storagePart (s:=s) (c:=c) (CompactComplexNonleafRoleSourceReturn.output selected caller v returned)).tape j=
      (storagePart (s:=s) (c:=c) v).tape j := by
  have hn : ¬CompactComplexNonleafRoleReturnFrames.Core
      (CompactComplexNonleafRoleReturnFrame.oldSlot (s:=10+s) (c:=c) j) := by
    rw [CompactComplexSourceReadyChildReturnPath.core_iff]
    have hj := j.isLt
    simp only [CompactComplexNonleafRoleReturnFrame.oldSlot,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd]
    omega
  have h := CompactComplexNonleafRoleSourceReturn.output_frame selected caller v returned _ hn
  simpa only [storagePart,CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,
    Tapes.reindex,storage_slot,storage,CompactComplexNonleafRoleReturnFrame.oldSlot] using h

/-- The actual full parent payload-return endpoint, before spectator
promotion and saved node-target restoration. -/
def mid (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6) :=
  CompactComplexNonleafRoleSourceReturn.output selected caller
    (CompactComplexNonleafRoleParentLiveContinuation.output v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload) returned

/-- The physically restored original parent exponent is derived from the
actual continuation, while all other controller tapes retain their cells. -/
theorem mid_control (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6) :
    controlPart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)=
      setTape (controlPart (s:=s) (c:=c) v) 1 (BinaryDescriptorStack.descriptor (bits e)) 1 := by
  let old := CompactComplexNonleafRoleParentBank.output v headerStack f p
    (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e
  let row := CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit ha pair rows ell metadataP payload
  let live := CompactComplexNonleafRoleParentLiveContinuation.liveOutput row liveStack liveFrame liveHead parentLive childLive
  have hrow : controlPart (s:=s) (c:=c) row=controlPart (s:=s) (c:=c) old :=
    controlPart_eq (s:=s) (c:=c) row old (row_control v headerStack f p e rho visit ha pair rows ell metadataP payload)
  have hlive : controlPart (s:=s) (c:=c) live=controlPart (s:=s) (c:=c) row :=
    controlPart_eq (s:=s) (c:=c) live row (live_control row liveStack liveFrame liveHead parentLive childLive)
  have hsource : controlPart (s:=s) (c:=c) (CompactComplexNonleafRoleSourceReturn.output selected caller live returned)=
      controlPart (s:=s) (c:=c) live := by
    apply congrArg₂ Tapes.mk
    · funext j; exact (source_control (s:=s) (c:=c) selected caller live returned j).1
    · funext j; exact (source_control (s:=s) (c:=c) selected caller live returned j).2
  exact hsource.trans (hlive.trans (hrow.trans
    (geometry_control (s:=s) (c:=c) v headerStack f p (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e)))

/-- Named dormant storage ports are retained throughout the actual decoded
return, except the consumed header/live frames and its two live-value cells. -/
theorem mid_storage (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6) (j : Fin (10+s))
    (hh : j≠Fin.natAdd 10 headerStack) (hl : j≠Fin.natAdd 10 liveStack)
    (h7 : j≠⟨7,by omega⟩) (h8 : j≠⟨8,by omega⟩) :
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)).head j=(storagePart (s:=s) (c:=c) v).head j ∧
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned)).tape j=(storagePart (s:=s) (c:=c) v).tape j := by
  have hs := source_storage selected caller
    (CompactComplexNonleafRoleParentLiveContinuation.output v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload) returned j
  have hinj : Function.Injective (storage (s:=s) (c:=c)) := by
    intro i j he; apply Fin.ext
    have hv := congrArg Fin.val he
    simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
      Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have hp := CompactComplexNonleafRoleParentLiveContinuation.parent_output_storage v headerStack f p e rho visit ha pair
    rows ell metadataP payload j hh
  have hlive := CompactComplexNonleafRoleParentLiveContinuation.live_output_frame
    (CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit ha pair rows ell metadataP payload)
    liveStack liveFrame liveHead parentLive childLive (storage (s:=s) (c:=c) j)
    (fun he => h7 (hinj he)) (fun he => h8 (hinj he)) (fun he => hl (hinj he))
  exact ⟨hs.1.trans ((storage_read _ j).1.trans (hlive.1.trans (hp.1.trans (storage_read _ j).1.symm))),
    hs.2.trans ((storage_read _ j).2.trans (hlive.2.trans (hp.2.trans (storage_read _ j).2.symm)))⟩

open CompactComplexSourceReadyReachedReturnInvariant (Restored)

/-- The actual restored node-target storage preserves all other saved ports. -/
theorem final_storage (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (parentTarget : ℕ) (j : Fin (10+s))
    (hh : j≠Fin.natAdd 10 headerStack) (hl : j≠Fin.natAdd 10 liveStack)
    (h7 : j≠⟨7,by omega⟩) (h8 : j≠⟨8,by omega⟩) (h9 : j≠⟨9,by omega⟩) :
    let middle := mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    let finalStore := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart (s:=s) (c:=c) middle)
      childLive targetFrame targetHead parentTarget
    finalStore.head j=(storagePart (s:=s) (c:=c) v).head j ∧ finalStore.tape j=(storagePart (s:=s) (c:=c) v).tape j := by
  have ht := CompactComplexNonleafSpectatorTargetRestore.restoredStorage_frame
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned))
    childLive targetFrame targetHead parentTarget j h7 h8 h9
  have hm := mid_storage selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned j hh hl h7 h8
  exact ⟨ht.1.trans hm.1,ht.2.trans hm.2⟩

/-- Local completed-child controller/count/call facts yield all the parent
Restored ports from the actual decoded return. Advanced live, original target
and exponent are generated by the physical continuation rather than supplied
as assumed parent endpoint words. The auxiliary facts belong to the caller's
actual restored payload stack. -/
theorem restored_ports (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack pcStack liveStack : Fin s)
    (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (parentTarget : ℕ)
    (aux : Tapes 2 2) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (hcount : (storagePart (s:=s) (c:=c) v).head 0=0 ∧ (storagePart (s:=s) (c:=c) v).tape 0=(fun _ => blank))
    (h28 : (controlPart (s:=s) (c:=c) v).head 28=0 ∧ (controlPart (s:=s) (c:=c) v).tape 28=(fun _ => blank))
    (h29 : (controlPart (s:=s) (c:=c) v).head 29=0 ∧ (controlPart (s:=s) (c:=c) v).tape 29=(fun _ => blank))
    (hclock : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank))
    (hfree : CompactComplexSourceReadyPrefixReadiness.BlankAfter aux 0)
    (hsaved : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart (s:=s) (c:=c) v).tape (Fin.natAdd 10 pcStack)) ((storagePart (s:=s) (c:=c) v).head (Fin.natAdd 10 pcStack))) :
    let middle := mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    Restored e childLive parentTarget pcStack origin calls (controlPart (s:=s) (c:=c) middle)
      (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart (s:=s) (c:=c) middle)
        childLive targetFrame targetHead parentTarget) aux := by
  dsimp only
  have hzero := final_storage selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned targetFrame targetHead parentTarget
    (0 : Fin (10+s))
    (by intro he;have hv := congrArg Fin.val he;simp only [Fin.val_zero,Fin.val_natAdd] at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;simp only [Fin.val_zero,Fin.val_natAdd] at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;change 0=7 at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;change 0=8 at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;change 0=9 at hv;omega)
  have hpc := final_storage selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned targetFrame targetHead parentTarget
    (Fin.natAdd 10 pcStack)
    (by intro he;apply hpcHeader;apply Fin.ext;have hv := congrArg Fin.val he;simp only [Fin.val_natAdd] at hv;omega)
    (by intro he;apply hpcLive;apply Fin.ext;have hv := congrArg Fin.val he;simp only [Fin.val_natAdd] at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;simp only [Fin.val_natAdd] at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;simp only [Fin.val_natAdd] at hv;omega)
    (by intro he;have hv := congrArg Fin.val he;simp only [Fin.val_natAdd] at hv;omega)
  have hc := mid_control selected caller v headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell metadataP payload returned
  have hp := CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports
    (storagePart (s:=s) (c:=c) (mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned))
    childLive targetFrame targetHead parentTarget
  refine {
    count_blank := ⟨hzero.1.trans hcount.1,hzero.2.trans hcount.2⟩,
    exponent := ?_,control28_blank := ?_,control29_blank := ?_,
    live := ⟨hp.1,hp.2.1⟩,
    target_word := ⟨hp.2.2.1,hp.2.2.2.1.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _ )⟩,
    clock_blank := hclock,aux_free := hfree,saved := ?_ }
  · rw [hc]
    simp only [setTape,Function.update_self,and_self]
  · rw [hc]
    simpa only [setTape,Function.update_of_ne (by decide : (28 : Fin 43)≠1)] using h28
  · rw [hc]
    simpa only [setTape,Function.update_of_ne (by decide : (29 : Fin 43)≠1)] using h29
  · rw [hpc.2,hpc.1]
    exact hsaved

private def scratchIndex (j : Fin 7) : Fin (43+CompactNativeRoleInstall.rawCount c) :=
  Fin.natAdd 43 ⟨1+c+j.val,by
    have := j.isLt
    unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount
    omega⟩

private theorem scratch_slot (j : Fin 7) :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) (scratchIndex j)=
      Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j := by
  apply Fin.ext
  have h0 : ¬43+(1+c+j.val)<43 := by omega
  have h2 : ¬43+(1+c+j.val)<44+c := by omega
  simp [scratchIndex,CompactComplexNonleafRoleSplit.slot,h0,h2]
  omega

/-- The genuine row-restoration native bank clears all seven private frames. -/
theorem row_scratch (v : Tapes (tapes s c) 2) (headerStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (j : Fin 7) :
    let row := CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit ha pair rows ell metadataP payload
    row.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j)=0 ∧
    row.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j)=(fun _ => blank) := by
  have h := CompactComplexNonleafRoleParentContinuation.output_active v headerStack f p e rho visit ha pair rows ell metadataP payload
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head (scratchIndex j)) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape (scratchIndex j)) h
  simp only [CompactComplexNonleafRoleParentContinuation.placement,CompactComplexNonleafRoleSplit.placement,
    InjectivePlacement.active_bank,scratch_slot] at hh ht
  constructor
  · simpa [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,scratchIndex,
      Tapes.append,SharedBank.empty,Fin.addCases] using hh
  · simpa [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,scratchIndex,
      Tapes.append,SharedBank.empty,Fin.addCases] using ht

/-- All seven real return frames are blank before the inverse basis pass. -/
theorem mid_scratch (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6) (j : Fin 7) :
    let middle := mid selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned
    middle.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j)=0 ∧
    middle.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j)=(fun _ => blank) := by
  let row := CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit ha pair rows ell metadataP payload
  let live := CompactComplexNonleafRoleParentLiveContinuation.liveOutput row liveStack liveFrame liveHead parentLive childLive
  have hn (i : Fin (10+s)) :
      Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j≠storage (s:=s) (c:=c) i := by
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
      Fin.val_natAdd,Fin.val_castAdd] at hv
    unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
      CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
    omega
  have hl := CompactComplexNonleafRoleParentLiveContinuation.live_output_frame row liveStack liveFrame liveHead
    parentLive childLive (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) j) (hn _) (hn _) (hn _)
  have hs := CompactComplexNonleafRoleSourceReturn.output_extra selected caller live returned j
  have hr := row_scratch v headerStack f p e rho visit ha pair rows ell metadataP payload j
  exact ⟨hs.1.trans (hl.1.trans hr.1),hs.2.trans (hl.2.trans hr.2)⟩

def callerAux (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2) : Tapes 2 2 :=
  SharedBank.payload caller (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+s) c))

/-- Physical payload recovery restores the original caller's two auxiliary
words, independently of all nested completed-child changes. -/
theorem source_aux (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) (i : Fin 2) :
    (CompactComplexNonleafRoleSourceReturn.output selected caller v returned).head
      (CompactComplexNonleafRoleParentPayloadContinuation.extra i)=(callerAux caller).head i ∧
    (CompactComplexNonleafRoleSourceReturn.output selected caller v returned).tape
      (CompactComplexNonleafRoleParentPayloadContinuation.extra i)=(callerAux caller).tape i := by
  fin_cases i
  · change (CompactComplexNonleafRoleSourceReturn.output selected caller v returned).head
      (CompactComplexNonleafRoleParentPayloadContinuation.extra (0 : Fin 2))=(callerAux caller).head 0 ∧
      (CompactComplexNonleafRoleSourceReturn.output selected caller v returned).tape
      (CompactComplexNonleafRoleParentPayloadContinuation.extra (0 : Fin 2))=(callerAux caller).tape 0
    have h := CompactComplexNonleafRoleSourceReturn.output_core selected caller v returned
      CompactComplexNonleafRoleEntry.stack (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hn : CompactComplexNonleafRoleEntry.stack (s:=10+s) (c:=c)≠CompactComplexNonleafRoleEntry.roleTape selected := by
      intro he;have hv := congrArg Fin.val he;have := selected.isLt
      simp only [CompactComplexNonleafRoleEntry.stack,CompactComplexNonleafRoleEntry.roleTape,
        Fin.val_natAdd,Fin.val_castAdd] at hv
      unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes at hv
      omega
    simp only [setTape,Function.update_of_ne hn] at h
    simpa only [CompactComplexNonleafRoleParentPayloadContinuation.extra,CompactComplexNonleafRoleEntry.stack,
      callerAux,SharedBank.payload] using h
  · change (CompactComplexNonleafRoleSourceReturn.output selected caller v returned).head
      (CompactComplexNonleafRoleParentPayloadContinuation.extra (1 : Fin 2))=(callerAux caller).head 1 ∧
      (CompactComplexNonleafRoleSourceReturn.output selected caller v returned).tape
      (CompactComplexNonleafRoleParentPayloadContinuation.extra (1 : Fin 2))=(callerAux caller).tape 1
    have h := CompactComplexNonleafRoleSourceReturn.output_core selected caller v returned
      CompactComplexNonleafRoleEntry.clock (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    have hn : CompactComplexNonleafRoleEntry.clock (s:=10+s) (c:=c)≠CompactComplexNonleafRoleEntry.roleTape selected := by
      intro he;have hv := congrArg Fin.val he;have := selected.isLt
      simp only [CompactComplexNonleafRoleEntry.clock,CompactComplexNonleafRoleEntry.roleTape,
        Fin.val_natAdd,Fin.val_castAdd] at hv
      unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes at hv
      omega
    simp only [setTape,Function.update_of_ne hn] at h
    simpa only [CompactComplexNonleafRoleParentPayloadContinuation.extra,CompactComplexNonleafRoleEntry.clock,
      callerAux,SharedBank.payload] using h

private theorem frame_aux_read (v : Tapes (tapes s c) 2) (i : Fin 2) :
    (CompactComplexSourceReadyChildReturnPath.frame v).head (Fin.castAdd 7 i)=
      v.head (CompactComplexNonleafRoleParentPayloadContinuation.extra i) ∧
    (CompactComplexSourceReadyChildReturnPath.frame v).tape (Fin.castAdd 7 i)=
      v.tape (CompactComplexNonleafRoleParentPayloadContinuation.extra i) := by
  have hi : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) (Fin.castAdd 7 i))=
      CompactComplexNonleafRoleParentPayloadContinuation.extra i := Fin.ext rfl
  simp only [CompactComplexSourceReadyChildReturnPath.frame,SharedBank.payload,Tapes.reindex,hi,and_self]

private theorem frame_scratch_read (v : Tapes (tapes s c) 2) (i : Fin 7) :
    (CompactComplexSourceReadyChildReturnPath.frame v).head (Fin.natAdd 2 i)=
      v.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) i) ∧
    (CompactComplexSourceReadyChildReturnPath.frame v).tape (Fin.natAdd 2 i)=
      v.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) i) := by
  have hi : (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) (Fin.natAdd 2 i))=
      Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) i := by
    apply Fin.ext
    change CompactComplexNativeCodecFrame.permanentTapes (10+s) c+(2+i.val)=
      (CompactComplexNativeCodecFrame.permanentTapes (10+s) c+2)+i.val
    omega
  simp only [CompactComplexSourceReadyChildReturnPath.frame,SharedBank.payload,Tapes.reindex,hi,and_self]

private theorem frame_from_ports (v : Tapes (tapes s c) 2) (aux : Tapes 2 2)
    (ha : ∀ i : Fin 2,v.head (CompactComplexNonleafRoleParentPayloadContinuation.extra i)=aux.head i ∧
      v.tape (CompactComplexNonleafRoleParentPayloadContinuation.extra i)=aux.tape i)
    (hs : ∀ i : Fin 7,v.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) i)=0 ∧
      v.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+s) c) i)=(fun _ => blank)) :
    CompactComplexSourceReadyChildReturnPath.frame (s:=s) (c:=c) v=
      aux.append (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m:=2) (n:=7) with
    | left i =>
      simpa only [Tapes.append,Fin.addCases_left,CompactComplexSourceReadyChildReturnPath.frame,SharedBank.payload] using
        (frame_aux_read (s:=s) (c:=c) v i).1.trans (ha i).1
    | right i =>
      simpa only [Tapes.append,Fin.addCases_right,SharedBank.empty,CompactComplexSourceReadyChildReturnPath.frame,SharedBank.payload] using
        (frame_scratch_read (s:=s) (c:=c) v i).1.trans (hs i).1
  · funext i
    induction i using Fin.addCases (m:=2) (n:=7) with
    | left i =>
      simpa only [Tapes.append,Fin.addCases_left,CompactComplexSourceReadyChildReturnPath.frame,SharedBank.payload] using
        (frame_aux_read (s:=s) (c:=c) v i).2.trans (ha i).2
    | right i =>
      simpa only [Tapes.append,Fin.addCases_right,SharedBank.empty,CompactComplexSourceReadyChildReturnPath.frame,SharedBank.payload] using
        (frame_scratch_read (s:=s) (c:=c) v i).2.trans (hs i).2

/-- The actual return endpoint has the original caller auxiliaries and all
seven private frames blank. Canonical geometry is proved, not assumed. -/
theorem mid_frame (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP : ℕ) (payload : Tapes (1+c) 2) (returned : ℤ → Fin 6) :
    CompactComplexSourceReadyChildReturnPath.frame (s:=s) (c:=c)
      (mid selected caller v headerStack liveStack f p liveFrame liveHead
        e parentLive childLive rho visit ha pair rows ell metadataP payload returned)=
      (callerAux caller).append (SharedBank.empty 7 2) := by
  apply frame_from_ports (s:=s) (c:=c)
  · intro i
    exact source_aux (s:=s) (c:=c) selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output v headerStack liveStack f p liveFrame liveHead
        e parentLive childLive rho visit ha pair rows ell metadataP payload) returned i
  · intro i
    exact mid_scratch selected caller v headerStack liveStack f p liveFrame liveHead
      e parentLive childLive rho visit ha pair rows ell metadataP payload returned i

end
end IntegerMultBounds.Machine.CompactComplexAlignedReachedChildReturnPath
