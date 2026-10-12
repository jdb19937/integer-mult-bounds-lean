module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant

/-! Literal saved-frame references captured from the actual physical child-entry
output. These equations identify the header, denominator, target and payload
stacks independently of the recursive preservation obligation. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedChildFrames
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexNonleafRoleChildBank
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexSourceReadyChildEntryPath (publicOutput selected)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Holds captured)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCallReturn.addressCount
  CompactComplexCallReturn.addressWidth CompactComplexRolePhaseSite.roleCount

/-- Capture the actual storage and physical payload-stack ports; no separately
prepared reference bank is supplied. -/
def capture (headerStack pcStack liveStack : Fin s) (u : Tapes (tapes s c) 2) : Snapshot s where
  headerStack := headerStack
  liveStack := liveStack
  pcStack := pcStack
  storage := SharedBank.payload u storage
  aux := SharedBank.payload u extra

theorem capture_holds (headerStack pcStack liveStack : Fin s) (u : Tapes (tapes s c) 2) :
    Holds (capture headerStack pcStack liveStack u)
      (SharedBank.payload u storage) (SharedBank.payload u extra) :=
  captured (capture headerStack pcStack liveStack u)

private theorem storage_slot (j : Fin (10+s)) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexSpectatorTargetBank.oldSlot (s:=10+s) (c:=c) j))=storage j := by
  apply Fin.ext
  rfl

/-- The direct captured storage projection agrees with the physical return
adapter's canonical storage projection. -/
theorem capture_storagePart (headerStack pcStack liveStack : Fin s) (u : Tapes (tapes s c) 2) :
    (capture headerStack pcStack liveStack u).storage=CompactComplexSourceReadyChildReturnPath.storagePart u := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,storage_slot]

private theorem storage_injective : Function.Injective (storage (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem storage_control (j : Fin (10+s)) (i : Fin 43) :
    storage (s:=s) (c:=c) j≠CompactComplexNonleafRoleChildBank.control i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexNonleafRoleChildBank.control,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

private theorem future_ne (j : Fin s) (i : Fin (10+s)) (hi : i.val<10) :
    storage (s:=s) (c:=c) (Fin.natAdd 10 j)≠storage i := by
  intro he
  have hv := congrArg Fin.val (storage_injective he)
  simp only [Fin.val_natAdd] at hv
  omega

private theorem future_distinct (i j : Fin s) (hij : i≠j) :
    storage (s:=s) (c:=c) (Fin.natAdd 10 i)≠storage (Fin.natAdd 10 j) := by
  intro he
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val (storage_injective he)
  simp only [Fin.val_natAdd] at hv
  omega

private theorem extra_storage (i : Fin 2) (j : Fin (10+s)) :
    extra (s:=s) (c:=c) i≠storage j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [extra,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at hv
  omega

private theorem extra_control (i : Fin 2) : extra (s:=s) (c:=c) i≠CompactComplexNonleafRoleChildBank.control 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [extra,CompactComplexNonleafRoleChildBank.control,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at hv
  omega

private theorem extra_outside (i : Fin 2) (j : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    extra (s:=s) (c:=c) i≠CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [extra,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hj
  split_ifs at hv <;> omega

private theorem replace_extra (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (i : Fin 2) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).head (extra i)=v.head (extra i) ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).tape (extra i)=v.tape (extra i) := by
  obtain ⟨j,he⟩ := (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)).surjective (extra i)
  rw [←he]
  induction j using Fin.addCases with
  | left j =>
    have hs : CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ j)=
        CompactComplexNonleafRoleSplit.slot j := by
      simp [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    exact (extra_outside i j (he.symm.trans hs)).elim
  | right j =>
    simp only [Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra,and_self]

section Output
variable {sh : Shape} {left k siteCount : ℕ}
    (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity)
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
local notation "out" => output v parentTarget n e headerStack pcStack liveStack site
  rho visit hactive pair coordinate rows ell precision payload

/-- Later PC save and child numeric synthesis retain the original geometric
frame pushed by the real entry. -/
theorem output_header_stack (hpc : headerStack≠pcStack) (hlive : headerStack≠liveStack) :
    (out).head (storage (Fin.natAdd 10 headerStack))=
      CompactChildHeadersStack.top (v.head (storage (Fin.natAdd 10 headerStack)))
        (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) ∧
    (out).tape (storage (Fin.natAdd 10 headerStack))=
      CompactChildHeadersStack.frames (v.tape (storage (Fin.natAdd 10 headerStack)))
        (v.head (storage (Fin.natAdd 10 headerStack)))
        (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) := by
  have hpci := future_distinct (c:=c) headerStack pcStack hpc
  have hlivei := future_distinct (c:=c) headerStack liveStack hlive
  have htar := future_ne (c:=c) headerStack (⟨8,by omega⟩ : Fin (10+s)) (by change (8:ℕ)<10; omega)
  have hstack := future_ne (c:=c) headerStack (⟨9,by omega⟩ : Fin (10+s)) (by change (9:ℕ)<10; omega)
  have h := replace_storage
    (descended (pcSaved (headersSaved (liveSaved (targetSaved v parentTarget) liveStack n) headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (child rho visit hactive pair coordinate)
      rows ell precision) payload) (Fin.natAdd 10 headerStack)
  constructor
  · apply h.1.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,target,targetStack,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) (Fin.natAdd 10 headerStack) 1),
      Function.update_of_ne hpci,Function.update_self]
    simp only [Function.update_of_ne hlivei,Function.update_of_ne htar,Function.update_of_ne hstack]
  · apply h.2.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,target,targetStack,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) (Fin.natAdd 10 headerStack) 1),
      Function.update_of_ne hpci,Function.update_self]
    simp only [Function.update_of_ne hlivei,Function.update_of_ne htar,Function.update_of_ne hstack]

/-- All dynamically named stacks lie beyond storage9, so the true parent
return-target descriptor survives the subsequent saves. -/
theorem output_target_stack :
    (out).head targetStack=v.head targetStack+1+(bits parentTarget).length ∧
    (out).tape targetStack=BinaryDescriptorStack.frame (v.tape targetStack) (v.head targetStack) (bits parentTarget) := by
  have hpci := Ne.symm (future_ne (c:=c) pcStack (⟨9,by omega⟩ : Fin (10+s)) (by change (9:ℕ)<10; omega))
  have hheadi := Ne.symm (future_ne (c:=c) headerStack (⟨9,by omega⟩ : Fin (10+s)) (by change (9:ℕ)<10; omega))
  have hlivei := Ne.symm (future_ne (c:=c) liveStack (⟨9,by omega⟩ : Fin (10+s)) (by change (9:ℕ)<10; omega))
  have htar : storage (s:=s) (c:=c) (⟨9,by omega⟩ : Fin (10+s))≠storage (⟨8,by omega⟩ : Fin (10+s)) := target_ne_stack.symm
  have h := replace_storage
    (descended (pcSaved (headersSaved (liveSaved (targetSaved v parentTarget) liveStack n) headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (child rho visit hactive pair coordinate)
      rows ell precision) payload) (⟨9,by omega⟩ : Fin (10+s))
  constructor
  · apply h.1.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,target,targetStack,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) (⟨9,by omega⟩ : Fin (10+s)) 1),
      Function.update_of_ne hpci,Function.update_of_ne hheadi,Function.update_of_ne hlivei,
      Function.update_of_ne htar,Function.update_self]
  · apply h.2.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,target,targetStack,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) (⟨9,by omega⟩ : Fin (10+s)) 1),
      Function.update_of_ne hpci,Function.update_of_ne hheadi,Function.update_of_ne hlivei,
      Function.update_of_ne htar,Function.update_self]
/-- Numeric/header/live/PC saves do not modify the actual parked payload
stack or the reusable clock. -/
theorem output_extra (i : Fin 2) :
    (out).head (extra i)=v.head (extra i) ∧ (out).tape (extra i)=v.tape (extra i) := by
  have h := replace_extra
    (descended (pcSaved (headersSaved (liveSaved (targetSaved v parentTarget) liveStack n) headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (child rho visit hactive pair coordinate)
      rows ell precision) payload) i
  constructor
  · apply h.1.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,target,targetStack,setTape,
      Function.update_of_ne (extra_control (s:=s) (c:=c) i),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (Fin.natAdd 10 pcStack)),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (Fin.natAdd 10 headerStack)),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (Fin.natAdd 10 liveStack)),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (⟨8,by omega⟩ : Fin (10+s))),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (⟨9,by omega⟩ : Fin (10+s)))]
  · apply h.2.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,target,targetStack,setTape,
      Function.update_of_ne (extra_control (s:=s) (c:=c) i),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (Fin.natAdd 10 pcStack)),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (Fin.natAdd 10 headerStack)),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (Fin.natAdd 10 liveStack)),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (⟨8,by omega⟩ : Fin (10+s))),
      Function.update_of_ne (extra_storage (s:=s) (c:=c) i (⟨9,by omega⟩ : Fin (10+s)))]
end Output

section Reached
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexNonleafRolePreparation (sourceReady)
variable {sh : Shape} {left k levels frames returned rows ell precision p C axes baseline pref n : ℕ}
    (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached (parent rho visit hactive pair) rows ell precision (k+2) p C axes
      baseline levels frames returned pref n pcStack origin calls v)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (headerStack liveStack : Fin s)

/-- Actual public child entry, valid at every accumulated parent axes budget. -/
def childOutput :=
  publicOutput call rho visit hactive pair rows ell precision (selectedArray h call)
    (caller h) h.targetValue n headerStack pcStack liveStack

/-- The saved reference is the literal child-entry endpoint of this reached
parent, with the same actual stacks and original saved-PC code. -/
def snapshot : Snapshot s :=
  capture headerStack pcStack liveStack (childOutput rho visit hactive pair h call headerStack liveStack)

private theorem caller_storage (i : Fin (10+s)) :
    (caller h).head (CompactComplexNonleafRoleReturnFrame.oldSlot i)=h.storage.head i ∧
    (caller h).tape (CompactComplexNonleafRoleReturnFrame.oldSlot i)=h.storage.tape i := by
  have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw (parent rho visit hactive pair) rows ell precision)
      h.tail h.storage h.payload) h.aux (CompactComplexSpectatorTargetBank.oldSlot i)
  have hb := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw (parent rho visit hactive pair) rows ell precision)
    h.tail h.storage h.payload i
  exact ⟨he.1.trans hb.1,he.2.trans hb.2⟩

private theorem source_storage (i : Fin (10+s)) :
    (sourceReady (selected call) rho visit hactive pair rows ell precision
      (selectedArray h call) (caller h)).head (storage i)=h.storage.head i ∧
    (sourceReady (selected call) rho visit hactive pair rows ell precision
      (selectedArray h call) (caller h)).tape (storage i)=h.storage.tape i := by
  have hq := CompactComplexNonleafRolePreparation.quotient_output_storage
    (selected call) sh rows ell precision (parent rho visit hactive pair).rho
    (parent rho visit hactive pair).left (parent rho visit hactive pair).f
    (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
    (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val
    (selectedArray h call) (caller h) i
  have hc := caller_storage rho visit hactive pair h i
  exact ⟨hq.1.trans hc.1,hq.2.trans hc.2⟩

/-- Original geometry descriptors are obtained from the reached parent's
literal storage, rather than assumed as captured-reference equations. -/
theorem snapshot_headers (hpc : headerStack≠pcStack) (hlive : headerStack≠liveStack) :
    (snapshot rho visit hactive pair h call headerStack liveStack).storage.head (Fin.natAdd 10 headerStack)=
      CompactChildHeadersStack.top (h.storage.head (Fin.natAdd 10 headerStack))
        (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) ∧
    (snapshot rho visit hactive pair h call headerStack liveStack).storage.tape (Fin.natAdd 10 headerStack)=
      CompactChildHeadersStack.frames (h.storage.tape (Fin.natAdd 10 headerStack))
        (h.storage.head (Fin.natAdd 10 headerStack))
        (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) := by
  have ho := output_header_stack
    (sourceReady (selected call) rho visit hactive pair rows ell precision (selectedArray h call) (caller h))
    h.targetValue n (k+2) headerStack pcStack liveStack call.site
    rho visit hactive pair call.slot (rows/roles) ell precision
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (selectedArray h call) roles) hpc hlive
  have hs := source_storage rho visit hactive pair h call (Fin.natAdd 10 headerStack)
  exact ⟨ho.1.trans (by rw [hs.1]),ho.2.trans (by rw [hs.1,hs.2])⟩

/-- The saved denominator is the actual reached parent live word. -/
theorem snapshot_live (hhead : liveStack≠headerStack) (hpc : liveStack≠pcStack) :
    (snapshot rho visit hactive pair h call headerStack liveStack).storage.head (Fin.natAdd 10 liveStack)=
      h.storage.head (Fin.natAdd 10 liveStack)+1+(bits n).length ∧
    (snapshot rho visit hactive pair h call headerStack liveStack).storage.tape (Fin.natAdd 10 liveStack)=
      BinaryDescriptorStack.frame (h.storage.tape (Fin.natAdd 10 liveStack))
        (h.storage.head (Fin.natAdd 10 liveStack)) (bits n) := by
  have ho := output_live_stack
    (sourceReady (selected call) rho visit hactive pair rows ell precision (selectedArray h call) (caller h))
    h.targetValue n (k+2) headerStack pcStack liveStack hhead hpc call.site
    rho visit hactive pair call.slot (rows/roles) ell precision
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (selectedArray h call) roles)
  have hs := source_storage rho visit hactive pair h call (Fin.natAdd 10 liveStack)
  exact ⟨ho.1.trans (by rw [hs.1]),ho.2.trans (by rw [hs.1,hs.2])⟩

/-- The saved target is the actual parent's target, on fixed storage9. -/
theorem snapshot_target :
    (snapshot rho visit hactive pair h call headerStack liveStack).storage.head ⟨9,by omega⟩=
      h.storage.head ⟨9,by omega⟩+1+(bits h.targetValue).length ∧
    (snapshot rho visit hactive pair h call headerStack liveStack).storage.tape ⟨9,by omega⟩=
      BinaryDescriptorStack.frame (h.storage.tape ⟨9,by omega⟩)
        (h.storage.head ⟨9,by omega⟩) (bits h.targetValue) := by
  have ho := output_target_stack
    (sourceReady (selected call) rho visit hactive pair rows ell precision (selectedArray h call) (caller h))
    h.targetValue n (k+2) headerStack pcStack liveStack call.site
    rho visit hactive pair call.slot (rows/roles) ell precision
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (selectedArray h call) roles)
  simp only [targetStack] at ho
  have hs := source_storage rho visit hactive pair h call (⟨9,by omega⟩ : Fin (10+s))
  exact ⟨ho.1.trans (by rw [hs.1]),ho.2.trans (by rw [hs.1,hs.2])⟩

/-- The captured payload-stack equation required by physical restoration is
proved from the original actual parking output. -/
theorem snapshot_payload :
    (snapshot rho visit hactive pair h call headerStack liveStack).aux.head 0=
      (CompactComplexNonleafRoleEntry.output (selected call) sh rows ell precision
        (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
        (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
        (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
        (parent rho visit hactive pair).target.val (caller h)).head CompactComplexNonleafRoleEntry.stack ∧
    (snapshot rho visit hactive pair h call headerStack liveStack).aux.tape 0=
      (CompactComplexNonleafRoleEntry.output (selected call) sh rows ell precision
        (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
        (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
        (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
        (parent rho visit hactive pair).target.val (caller h)).tape CompactComplexNonleafRoleEntry.stack := by
  have ho := output_extra
    (sourceReady (selected call) rho visit hactive pair rows ell precision (selectedArray h call) (caller h))
    h.targetValue n (k+2) headerStack pcStack liveStack call.site
    rho visit hactive pair call.slot (rows/roles) ell precision
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (selectedArray h call) roles) 0
  have hq := CompactComplexNonleafRolePreparation.quotient_output_frame
    (selected call) sh rows ell precision (parent rho visit hactive pair).rho
    (parent rho visit hactive pair).left (parent rho visit hactive pair).f
    (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
    (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val
    (selectedArray h call) (caller h) (extra (s:=s) (c:=roles) 0) (extra_outside 0)
  exact ⟨ho.1.trans (by simpa only [sourceReady,extra,CompactComplexNonleafRoleEntry.stack,Tapes.append,Fin.addCases_left] using hq.1),
    ho.2.trans (by simpa only [sourceReady,extra,CompactComplexNonleafRoleEntry.stack,Tapes.append,Fin.addCases_left] using hq.2)⟩

end Reached

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedChildFrames
