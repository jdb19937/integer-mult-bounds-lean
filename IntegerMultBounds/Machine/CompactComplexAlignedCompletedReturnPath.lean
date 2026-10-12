module

public import IntegerMultBounds.Machine.CompactComplexAlignedJoinedPhysicalReturn
public import IntegerMultBounds.Machine.CompactComplexAlignedCompletedSavedPop
public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnPorts

/-! Guard, saved-PC pop, original physical return and inverse basis execute
on the unchanged aligned table from the computed completed child. Captured
individual stack equations, recursive Settled and child output grid remain
explicit; completed source, controller, width and saved-history ports derive. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller canonical)
open CompactComplexSourceReadyReachedReturnInvariant (roleData returnedCaller returnedData returned_reached_from_path)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData basis_reached)
open CompactComplexAlignedChildReturnPath (liftedReturn liftedBank)
open CompactComplexAlignedReachedChildReturnPath (mid)
open CompactComplexAlignedPoppedReturnReadiness (popped)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexNonleafRoleChildBank (storage current target control)
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexSourceReadyChildReturnPath
open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexNativeCodec (raw)
open CompactNativeRoleConjugatedPorts (encoding)
variable {s q : ℕ} {sh : Shape} {left k : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  CompactComplexSourceReadyCompletedChildBoundary.completed
  CompactComplexSourceReadyCompletedChildBoundary.result
  CompactComplexAlignedPoppedReturnReadiness.popped

private theorem ready_frame (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2) :
    ((Alphabet.mapTapes encoding ((CompactComplexSourceReadyWorkspace.ready u).append
      (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).append
      (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime))=
    liftedBank (CompactComplexSourceReadyWorkspace.bank u
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)) := rfl

/- Compose over abstract banks before specializing to the computed child.
   This avoids repeatedly reducing completed-child data in dependent witnesses. -/
private theorem prepend_runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) (rows ell precision : ℕ)
    (result : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (headerStack pcStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed gap : ℕ)
    (pNum growthC axes baseline levels frames returned pref : ℕ) (origin : ℤ)
    (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (pv : Tapes (nodeTapes s roles) 2)
    (h : Reached (parent rho visit hactive pair) rows ell precision e pNum growthC axes
      baseline levels frames returned pref parentLive pcStack origin calls pv)
    (scalar : State) (targetFrame : ℤ → Fin 6) (targetHead : ℤ)
    (D : ℕ) (P : Program ActivePrefixStageNative.tapes q prime) (K : ℝ)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hr : 0<rows/roles)
    (hslots : (parent rho visit hactive pair).slots=25^3)
    (hpack : ∀ op,1<(parent rho visit hactive pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rho visit hactive pair)
          (rows/roles) ell precision hG hGK hr) op) D)
    (initial : Tapes (CompactComplexActualCallFullAlignment.tapes s roles) prime)
    (pcStart : Fin (CompactComplexScheduledPCLayout.originalCount+
      (4+CompactComplexCompletedLiveLower.schedule.length)+2)) (prefixTime : ℕ)
    (hprefix : CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack pcStart initial prefixTime
      (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank u
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2))))
    (hjoined :
    let stage := parent rho visit hactive pair
    let j := CompactComplexRolePhaseSite.role call.site
    let pc := CompactComplexRolePhaseSite.pc call.site
    let middle := mid j (caller h) u headerStack liveStack f p liveFrame liveHead e parentLive (parentLive+gap)
      rho visit hactive pair rows ell precision (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell result roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
      (parentLive+gap) targetFrame targetHead h.targetValue
    let start := canonical (returnedCaller h j gap result (controlPart middle) (queuePart middle)
      scalar (tailPart middle) nextStorage) h.aux
    let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell precision hG hGK hr
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
      (CompactComplexActualCallAlignment.nativeCost D d hslots pc true
        (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh precision)) hpack)
    ∃ hn : Reached stage rows ell precision e pNum growthC axes baseline levels frames (returned+completed) pref
      (parentLive+gap) pcStack origin calls start,
      hn.data=returnedData h j gap result ∧
      let after := basisArray stage (rows/roles) ell precision hG hGK hr hslots pc true
        (hn.data (CompactComplexScalarRolePorts.roleIndex.symm j))
      ∃ final : Reached stage rows ell precision e pNum growthC axes baseline levels frames (returned+completed) pref
        (parentLive+gap) pcStack origin calls (canonical (replacementCaller hn j after) hn.aux),
        final.data=replacementData hn j after ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage rows ell precision passTime : ℝ)≤
          K*ActivePrefixStageInverseBudget.scale d ∧
        ∃ time≤timeConstant roles*CompactNativeRoleTransferBudget.volume rows sh ell precision+1+
          CompactComplexActualCallRoleAlignment.cost roles stage rows ell precision passTime+1,
          CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack
            (CompactComplexScheduledPCDecode.savedPC call)
            (liftedBank (CompactComplexSourceReadyWorkspace.bank u
              (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2))) time
            (CompactComplexScheduledPCLayout.callNextPC call)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready
              (canonical (replacementCaller hn j after) hn.aux))))) :
    let stage := parent rho visit hactive pair
    let j := CompactComplexRolePhaseSite.role call.site
    let pc := CompactComplexRolePhaseSite.pc call.site
    let middle := mid j (caller h) u headerStack liveStack f p liveFrame liveHead e parentLive (parentLive+gap)
      rho visit hactive pair rows ell precision (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell result roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
      (parentLive+gap) targetFrame targetHead h.targetValue
    let start := canonical (returnedCaller h j gap result (controlPart middle) (queuePart middle)
      scalar (tailPart middle) nextStorage) h.aux
    let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell precision hG hGK hr
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
      (CompactComplexActualCallAlignment.nativeCost D d hslots pc true
        (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh precision)) hpack)
    ∃ hn : Reached stage rows ell precision e pNum growthC axes baseline levels frames (returned+completed) pref
      (parentLive+gap) pcStack origin calls start,
      hn.data=returnedData h j gap result ∧
      let after := basisArray stage (rows/roles) ell precision hG hGK hr hslots pc true
        (hn.data (CompactComplexScalarRolePorts.roleIndex.symm j))
      ∃ final : Reached stage rows ell precision e pNum growthC axes baseline levels frames (returned+completed) pref
        (parentLive+gap) pcStack origin calls (canonical (replacementCaller hn j after) hn.aux),
        final.data=replacementData hn j after ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage rows ell precision passTime : ℝ)≤
          K*ActivePrefixStageInverseBudget.scale d ∧
        ∃ time≤prefixTime+(timeConstant roles*CompactNativeRoleTransferBudget.volume rows sh ell precision+1+
          CompactComplexActualCallRoleAlignment.cost roles stage rows ell precision passTime+1),
          CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack
            pcStart initial time
            (CompactComplexScheduledPCLayout.callNextPC call)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready
              (canonical (replacementCaller hn j after) hn.aux)))) := by
  dsimp only at hjoined ⊢
  obtain ⟨hn,hdata,final,hfinalData,hcost,time,htime,hreturn⟩ := hjoined
  refine ⟨hn,hdata,final,hfinalData,hcost,prefixTime+time,
    Nat.add_le_add_left htime prefixTime,?_⟩
  exact FiniteFlowPath.append hprefix hreturn


theorem runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) (rows ell precision : ℕ)
    (headerStack pcStack liveStack : Fin s) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (e parentLive gap cp cC caxes cbaseline clevels cframes creturned cpref cn : ℕ)
    (cv : Tapes (nodeTapes s roles) 2)
    (hcChild : Reached (child rho visit hactive pair call.slot) (rows/roles) ell precision (e-1)
      cp cC caxes cbaseline clevels cframes creturned cpref cn pcStack origin (call::calls) cv)
    (hchildSlots : (child rho visit hactive pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (hchildDiv : roles∣rows/roles) (hchildTarget : hcChild.targetValue=parentLive+gap)
    (snapshot : Snapshot s) (settled : Settled snapshot hcChild.storage hcChild.aux)
    (hSnapshotHeader : snapshot.headerStack=headerStack) (hSnapshotLive : snapshot.liveStack=liveStack)
    (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (he : 0<e) (hr : 0<rows/roles) (hd : roles ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (ht : snapshot.storage.tape (Fin.natAdd 10 headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : snapshot.storage.head (Fin.natAdd 10 headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (completed : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+gap))
    (hstack : snapshot.storage.tape (Fin.natAdd 10 liveStack)=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : snapshot.storage.head (Fin.natAdd 10 liveStack)=liveHead+1+(bits parentLive).length)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (pNum growthC axes baseline levels frames returned pref : ℕ)
    (pv : Tapes (nodeTapes s roles) 2)
    (h : Reached (parent rho visit hactive pair) rows ell precision e pNum growthC axes
      baseline levels frames returned pref parentLive pcStack origin calls pv)
    (hc : 0<roles) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hstackActual : snapshot.aux.head 0=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val (caller h)).head CompactComplexNonleafRoleEntry.stack ∧
      snapshot.aux.tape 0=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val (caller h)).tape CompactComplexNonleafRoleEntry.stack)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN h.targetValue ledgerLeft ledgerExponent)
    (htargetStack : snapshot.storage.tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits h.targetValue))
    (htargetStackHead : snapshot.storage.head ⟨9,by omega⟩=targetHead+1+(bits h.targetValue).length)
    (htargetFree : ∀ z,targetHead≤z → z<targetHead+1+(bits h.targetValue).length → targetFrame z=blank)
    (D : ℕ) (P : Program ActivePrefixStageNative.tapes q prime) (K : ℝ)
    (hP : CompactComplexAlignedChildEntryPath.BasisRuns D q P K)
    (path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
    (ha : 0<sh.active) (hmeta : pNum+2*sh.bits≤precision) (haxes : axes+gap≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤growthC)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient growthC+Nat.clog 2 (growthC+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk) (hgap : gap≤2*completed)
    (hgrid : CompactSpectatorInheritedGrid.Grid sh (rows/roles) ell (precision-2*sh.bits) (parentLive+gap)
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound pNum growthC levels (frames+2*(returned+completed)+axes))) (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call))
    (hGK : sh.guard+1≤sh.chunk) (hrows : 0<rows) (hpay : sh.payload=1)
    (hslots : (parent rho visit hactive pair).slots=25^3)
    (hpack : ∀ op,1<(parent rho visit hactive pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rho visit hactive pair)
          (rows/roles) ell precision hG hGK hr) op) D)
    (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
 :
    ∃ older top,
    CompactComplexSourceReadySavedCallHistory.Associated origin calls older top ∧
    let stage := parent rho visit hactive pair
    let j := CompactComplexRolePhaseSite.role call.site
    let pc := CompactComplexRolePhaseSite.pc call.site
    let middle := mid j (caller h) (popped (CompactComplexSourceReadyCompletedChildBoundary.completed hcChild hchildSlots hchildDiv call) pcStack older top) headerStack liveStack f p liveFrame liveHead e parentLive (parentLive+gap)
      rho visit hactive pair rows ell precision (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call)))
    let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
      (parentLive+gap) targetFrame targetHead h.targetValue
    let start := canonical (returnedCaller h j gap (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) (controlPart middle) (queuePart middle)
      hcChild.scalar (tailPart middle) nextStorage) h.aux
    let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell precision hG hGK hr
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
      (CompactComplexActualCallAlignment.nativeCost D d hslots pc true
        (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh precision)) hpack)
    ∃ hn : Reached stage rows ell precision e pNum growthC axes baseline levels frames (returned+completed) pref
      (parentLive+gap) pcStack origin calls start,
      hn.data=returnedData h j gap (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) ∧
      let after := basisArray stage (rows/roles) ell precision hG hGK hr hslots pc true
        (hn.data (CompactComplexScalarRolePorts.roleIndex.symm j))
      ∃ final : Reached stage rows ell precision e pNum growthC axes baseline levels frames (returned+completed) pref
        (parentLive+gap) pcStack origin calls (canonical (replacementCaller hn j after) hn.aux),
        final.data=replacementData hn j after ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage rows ell precision passTime : ℝ)≤
          K*ActivePrefixStageInverseBudget.scale d ∧
        ∃ time≤(CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)+
          (timeConstant roles*CompactNativeRoleTransferBudget.volume rows sh ell precision+1+
          CompactComplexActualCallRoleAlignment.cost roles stage rows ell precision passTime+1),
          CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack
            0
            (liftedBank (CompactComplexSourceReadyWorkspace.bank
              (CompactComplexSourceReadyCompletedChildBoundary.completed hcChild hchildSlots hchildDiv call)
              (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2))) time
            (CompactComplexScheduledPCLayout.callNextPC call)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready
              (canonical (replacementCaller hn j after) hn.aux)))) := by
  have hmetadata : 2*sh.bits≤precision := by omega
  have hpcHeader' : pcStack≠snapshot.headerStack := by simpa only [hSnapshotHeader] using hpcHeader
  have hpcLive' : pcStack≠snapshot.liveStack := by simpa only [hSnapshotLive] using hpcLive
  obtain ⟨older,top,ho,hpop,hh,hl,htargetPorts,hpayload,hclock⟩ :=
    CompactComplexAlignedCompletedSavedPop.runs P headerStack pcStack liveStack origin calls call hcChild
      hchildSlots hchildDiv (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
      (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime)
      snapshot settled hpcHeader' hpcLive'
  rw [ready_frame,ready_frame] at hpop
  rw [hSnapshotHeader] at hh
  rw [hSnapshotLive] at hl
  let u := popped (CompactComplexSourceReadyCompletedChildBoundary.completed hcChild hchildSlots hchildDiv call)
    pcStack older top
  have hraw := CompactComplexAlignedPoppedReturnPorts.popped_raw_source call hcChild hchildSlots hchildDiv older top
  have hexp := CompactComplexAlignedPoppedReturnPorts.popped_exponent call hcChild hchildSlots hchildDiv older top
  have hcontrol := CompactComplexAlignedReachedChildReturnPath.control_read u 1
  have hx' : u.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1)) := hcontrol.2.symm.trans hexp.2
  have hhx' : u.head (control 1)=1 := hcontrol.1.symm.trans hexp.1
  have hcur := CompactComplexAlignedPoppedReturnPorts.popped_current call hcChild hchildSlots hchildDiv older top
  have hcurRead := CompactComplexAlignedReachedChildReturnPath.storage_read u (⟨7,by omega⟩ : Fin (10+s))
  have hcurrent' : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+gap)) := by
    change u.tape (storage ⟨7,by omega⟩)=_
    exact hcurRead.2.symm.trans (hcur.2.trans (by rw [hchildTarget,BinaryDescriptorStackRoundtrip.descriptor_encoded]))
  have hcurrentHead' : u.head current=1 := hcurRead.1.symm.trans hcur.1
  have htgt := CompactComplexAlignedPoppedReturnPorts.popped_target call hcChild hchildSlots hchildDiv older top
  have htgtRead := CompactComplexAlignedReachedChildReturnPath.storage_read u (⟨8,by omega⟩ : Fin (10+s))
  have htarget' : u.tape target=(fun _ => blank) := htgtRead.2.symm.trans htgt.2
  have htargetHead' : u.head target=0 := htgtRead.1.symm.trans htgt.1
  have hscalar := CompactComplexAlignedPoppedReturnPorts.popped_scalar call hcChild hchildSlots hchildDiv older top
  have hwidth := CompactComplexAlignedCompletedReturnReadiness.completed_record_width hcChild hchildSlots hchildDiv call hmetadata
  have hcount := CompactComplexAlignedPoppedReturnPorts.popped_count call hcChild hchildSlots hchildDiv older top
  have h28 := CompactComplexAlignedPoppedReturnPorts.popped_control28 call hcChild hchildSlots hchildDiv older top
  have h29 := CompactComplexAlignedPoppedReturnPorts.popped_control29 call hcChild hchildSlots hchildDiv older top
  have hsave := CompactComplexAlignedPoppedReturnPorts.popped_saved_associated
    (CompactComplexSourceReadyCompletedChildBoundary.completed hcChild hchildSlots hchildDiv call)
    pcStack older top origin calls ho
  have hsread := CompactComplexAlignedReachedChildReturnPath.storage_read u (Fin.natAdd 10 pcStack)
  have hsaved : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart u).tape (Fin.natAdd 10 pcStack)) ((storagePart u).head (Fin.natAdd 10 pcStack)) := by
    rw [hsread.1,hsread.2]
    exact hsave
  have ht' : u.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=
      CompactChildHeadersStack.frames f p (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) :=
    hh.2.trans ht
  have hp' : u.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=
      CompactChildHeadersStack.top p (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) :=
    hh.1.trans hp
  have hstack' := hl.2.trans hstack
  have hstackHead' := hl.1.trans hstackHead
  have hstackActual' := And.intro (hpayload.1.trans hstackActual.1) (hpayload.2.trans hstackActual.2)
  have htargetStack' : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits h.targetValue) := by
    rw [(CompactComplexAlignedReachedChildReturnPath.storage_read u ⟨9,by omega⟩).2]
    exact htargetPorts.2.trans htargetStack
  have htargetStackHead' : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits h.targetValue).length := by
    rw [(CompactComplexAlignedReachedChildReturnPath.storage_read u ⟨9,by omega⟩).1]
    exact htargetPorts.1.trans htargetStackHead
  have hjoined :=
    CompactComplexAlignedJoinedPhysicalReturn.runs rho visit hactive pair call rows ell precision
      (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call)
      u headerStack pcStack liveStack hstacks f p e he hr hd heq hG hraw ht' hp' hb hx' hhx'
      liveFrame liveHead parentLive completed gap progress hstack' hstackHead' hcurrent' hcurrentHead'
      htarget' htargetHead' hfree pNum growthC axes baseline levels frames returned pref origin calls pv h
      hwidth hc hA hK hstackActual' hclock hcChild.scalar hscalar targetFrame targetHead ledgerN ledgerLeft ledgerExponent
      ledger htargetStack' htargetStackHead' htargetFree D P K hP path ha hmeta haxes hC hroom hgap hgrid
      hGK hrows hpay hslots hpack hpcHeader hpcLive hcount h28 h29 hsaved
  refine ⟨older,top,ho,?_⟩
  exact prepend_runs rho visit hactive pair call rows ell precision
    (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call)
    u headerStack pcStack liveStack f p e liveFrame liveHead parentLive completed gap
    pNum growthC axes baseline levels frames returned pref origin calls pv h hcChild.scalar
    targetFrame targetHead D P K hG hGK hr hslots hpack _ 0 _ hpop hjoined

end
end IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnPath
