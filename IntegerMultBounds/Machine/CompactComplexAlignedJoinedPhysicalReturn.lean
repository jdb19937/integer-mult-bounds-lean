module

public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedCanonical
public import IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnReadiness

/-! Original physical child return and the original inverse basis pass compose
in the unchanged aligned table. Canonical mid geometry and restored numerical
ports are derived; only literal input readiness and recursive grid remain. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedJoinedPhysicalReturn
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller canonical)
open CompactComplexSourceReadyReachedReturnInvariant (roleData returnedCaller returnedData returned_reached_from_path)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData basis_reached)
open CompactComplexAlignedChildReturnPath (liftedReturn liftedBank)
open CompactComplexAlignedReachedChildReturnPath (mid)
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

private theorem return_pair (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack liveStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack call=
      ⟨_,seq (liftedReturn (CompactComplexRolePhaseSite.role call.site) headerStack liveStack)
        (CompactComplexActualCallFullAlignment.roleProgram P s roles
          (CompactComplexRolePhaseSite.role call.site) (CompactComplexRolePhaseSite.pc call.site) true)⟩ := rfl

private theorem hoare_pair_eq {t a : ℕ} (A B : Σ q,Program t q a) (he : A=B)
    {before after : Tapes t a} {cost : ℕ}
    (h : HoareTime B.2 (fun z => z=before) (fun z => z=after) cost) :
    HoareTime A.2 (fun z => z=before) (fun z => z=after) cost := by
  cases he
  exact h

/-- Actual decoded return restores the parent then runs its original inverse
basis word with one fixed program witness; every join/table transition is paid. -/
theorem runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) (rows ell precision : ℕ) (result : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (headerStack pcStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/roles) (hd : roles ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement u=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair call.slot) (rows/roles) ell precision) (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell result roles))
    (ht : u.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : u.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : u.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : u.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed gap : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+gap))
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+gap))) (hcurrentHead : u.head current=1)
    (htarget : u.tape target=(fun _ => blank)) (htargetHead : u.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (pNum growthC axes baseline levels frames returned pref : ℕ) (origin : ℤ)
    (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (pv : Tapes (nodeTapes s roles) 2)
    (h : Reached (parent rho visit hactive pair) rows ell precision e pNum growthC axes
      baseline levels frames returned pref parentLive pcStack origin calls pv)
    (hresultWidth : ∀ j,(result j).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (result j).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hc : 0<roles) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hstackActual : u.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val (caller h)).head CompactComplexNonleafRoleEntry.stack ∧
      u.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val (caller h)).tape CompactComplexNonleafRoleEntry.stack)
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank)
    (scalar : State) (hscalar : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN h.targetValue ledgerLeft ledgerExponent)
    (htargetStack : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits h.targetValue))
    (htargetStackHead : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits h.targetValue).length)
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
        (CompactRecursiveGridBudget.bound pNum growthC levels (frames+2*(returned+completed)+axes))) result)
    (hGK : sh.guard+1≤sh.chunk) (hrows : 0<rows) (hpay : sh.payload=1)
    (hslots : (parent rho visit hactive pair).slots=25^3)
    (hpack : ∀ op,1<(parent rho visit hactive pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rho visit hactive pair)
          (rows/roles) ell precision hG hGK hr) op) D)
    (hpcHeader : pcStack≠headerStack) (hpcLive : pcStack≠liveStack)
    (hcount : (storagePart u).head 0=0 ∧ (storagePart u).tape 0=(fun _ => blank))
    (h28 : (controlPart u).head 28=0 ∧ (controlPart u).tape 28=(fun _ => blank))
    (h29 : (controlPart u).head 29=0 ∧ (controlPart u).tape 29=(fun _ => blank))
    (hsaved : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((storagePart u).tape (Fin.natAdd 10 pcStack)) ((storagePart u).head (Fin.natAdd 10 pcStack))) :

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
              (canonical (replacementCaller hn j after) hn.aux)))) := by
  dsimp only
  have hmetadata : 2*sh.bits≤precision := by omega
  have hw := CompactComplexSourceReadyReachedReturnInvariant.role_width h hmetadata
  have hphysical := CompactComplexAlignedChildReturnPath.physical_return_runs rho visit hactive pair call.slot
    rows ell precision result u headerStack liveStack hstacks f p e he hr hd heq hG hi ht hp hb hx hhx
    liveFrame liveHead parentLive completed gap progress hstack hstackHead hcurrent hcurrentHead
    htarget htargetHead hfree (CompactComplexRolePhaseSite.role call.site) (caller h) hresultWidth hc hA hK
    (CompactComplexSourceReadyReachedEventInvariant.child_headers h)
    (CompactComplexSourceReadyReachedEventInvariant.child_clock h)
    (CompactComplexAlignedCompletedReturnReadiness.caller_source_supported h)
    (CompactComplexAlignedCompletedReturnReadiness.caller_roles_supported h)
    (CompactComplexAlignedCompletedReturnReadiness.caller_free h call)
    hstackActual hclockActual scalar hscalar (roleData h) hw (fun _ => blank) 0
    (CompactComplexAlignedReturnedCallerPayload.returned_payload h _ result)
    targetFrame targetHead ledgerN h.targetValue ledgerLeft ledgerExponent ledger
    htargetStack htargetStackHead htargetFree (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
  let middle := mid (CompactComplexRolePhaseSite.role call.site) (caller h) u headerStack liveStack f p liveFrame liveHead
    e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell result roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
  let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
    (parentLive+gap) targetFrame targetHead h.targetValue
  have hend := CompactComplexAlignedReturnedCanonical.mid_endpoint h (CompactComplexRolePhaseSite.role call.site)
    gap result u headerStack liveStack f p liveFrame liveHead e parentLive (parentLive+gap) rho visit hactive pair
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell result roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) scalar nextStorage
  have hlift := congrArg (liftedBank (c:=roles)) hend
  dsimp only at hphysical
  have hphysicalCanonical : HoareTime
      (liftedReturn (CompactComplexRolePhaseSite.role call.site) headerStack liveStack)
      (fun z => z=liftedBank (CompactComplexSourceReadyWorkspace.bank u
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
      (fun z => z=liftedBank (canonical (returnedCaller h (CompactComplexRolePhaseSite.role call.site)
        gap result (controlPart middle) (queuePart middle) scalar (tailPart middle) nextStorage) h.aux))
      (timeConstant roles*CompactNativeRoleTransferBudget.volume rows sh ell precision) :=
    hphysical.consequence (fun _ hz => hz) (fun _ hz => hz.trans hlift) le_rfl
  have hports := CompactComplexAlignedReachedChildReturnPath.restored_ports
    (CompactComplexRolePhaseSite.role call.site) (caller h) u headerStack pcStack liveStack hpcHeader hpcLive
    f p liveFrame liveHead e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell result roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) targetFrame targetHead h.targetValue h.aux
    origin calls hcount h28 h29 h.clock_blank h.aux_free hsaved
  have hwidth : ∀ i,(result i).1.length=ButterflyGuard.halfWidth precision sh.bits+1 ∧
      (result i).2.length=ButterflyGuard.halfWidth precision sh.bits+1 := by
    simpa only [CompactNativeRoleHeaders.recordWidth,ButterflyGuard.width] using hresultWidth
  obtain ⟨hn,hdata⟩ := returned_reached_from_path h path (CompactComplexRolePhaseSite.role call.site) gap completed result
    ha hmeta haxes hC hroom hgap hwidth hgrid (controlPart middle) (queuePart middle) scalar (tailPart middle)
    nextStorage h.aux hports
  obtain ⟨hfinal,hfinalData⟩ := basis_reached hn (CompactComplexRolePhaseSite.role call.site) hG hGK hr hslots
    (CompactComplexRolePhaseSite.pc call.site) true
  obtain ⟨hinverse,hbound⟩ := hP s sh (parent rho visit hactive pair) rows ell precision e pNum growthC axes baseline
    levels frames (returned+completed) pref (parentLive+gap) pcStack origin calls _ hn
    (CompactComplexRolePhaseSite.role call.site) hG hGK hrows hr hd hpay hslots
    (CompactComplexRolePhaseSite.pc call.site) true hpack
  have hsequence := hphysicalCanonical.seq hinverse
  have hactual := hoare_pair_eq _ _ (return_pair P headerStack liveStack call) hsequence
  refine ⟨hn,hdata,hfinal,hfinalData,hbound,?_⟩
  exact CompactComplexFixedNodePaths.decoded_return_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) call _ _ _ hactual

end
end IntegerMultBounds.Machine.CompactComplexAlignedJoinedPhysicalReturn
