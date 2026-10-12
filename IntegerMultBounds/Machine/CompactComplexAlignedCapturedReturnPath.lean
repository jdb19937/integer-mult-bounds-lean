module

public import IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedChildFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedReturnGrid

/-! Actual captured child frames discharge every individual stack-reference
equation required by the completed-return path. Parent clean stack tails and
genuine recursive settling, grid and numerical progress remain explicit. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedCapturedReturnPath
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

theorem runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) (rows ell precision : ℕ)
    (headerStack pcStack liveStack : Fin s) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (parentLive gap cp cC caxes cbaseline clevels cframes creturned cpref cn : ℕ)
    (pNum growthC axes baseline levels frames returned pref : ℕ)
    (pv : Tapes (nodeTapes s roles) 2)
    (h : Reached (parent rho visit hactive pair) rows ell precision (k+2) pNum growthC axes
      baseline levels frames returned pref parentLive pcStack origin calls pv)
    (cv : Tapes (nodeTapes s roles) 2)
    (hcChild : Reached (child rho visit hactive pair call.slot) (rows/roles) ell precision ((k+2)-1)
      cp cC caxes cbaseline clevels cframes creturned cpref cn pcStack origin (call::calls) cv)
    (hchildSlots : (child rho visit hactive pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (hchildDiv : roles∣rows/roles) (hchildTarget : hcChild.targetValue=parentLive+gap)
    (settled : Settled
      (CompactComplexSourceReadyCapturedChildFrames.snapshot rho visit hactive pair h call headerStack liveStack)
      hcChild.storage hcChild.aux)
    (hstacks : headerStack≠liveStack)
    (hr : 0<rows/roles) (hd : roles ∣ rows) (hG : 1≤sh.guard)
    (hclean : ∀ i,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack i → ∀ z,h.storage.head i≤z → h.storage.tape i z=blank)
    (childVolume : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive cn (parentLive+gap))
    (hc : 0<roles) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (ledgerN ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN h.targetValue ledgerLeft ledgerExponent)
    (D : ℕ) (P : Program ActivePrefixStageNative.tapes q prime) (K : ℝ)
    (hP : CompactComplexAlignedChildEntryPath.BasisRuns D q P K)
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (ha : 0<sh.active) (hmeta : pNum+2*sh.bits≤precision) (haxes : axes+gap≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤growthC)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient growthC+Nat.clog 2 (growthC+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk) (hgap : gap≤2*childVolume)
    (hgrid : CompactSpectatorInheritedGrid.Grid sh (rows/roles) ell (precision-2*sh.bits) (parentLive+gap)
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound pNum growthC levels (frames+2*(returned+childVolume)+axes))) (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call))
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
    let middle := mid j (caller h) (popped (CompactComplexSourceReadyCompletedChildBoundary.completed hcChild hchildSlots hchildDiv call) pcStack older top) headerStack liveStack (h.storage.tape (Fin.natAdd 10 headerStack)) (h.storage.head (Fin.natAdd 10 headerStack)) (h.storage.tape (Fin.natAdd 10 liveStack)) (h.storage.head (Fin.natAdd 10 liveStack)) (k+2) parentLive (parentLive+gap)
      rho visit hactive pair rows ell precision (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call)))
    let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
      (parentLive+gap) (h.storage.tape (⟨9,by omega⟩ : Fin (10+s))) (h.storage.head (⟨9,by omega⟩ : Fin (10+s))) h.targetValue
    let start := canonical (returnedCaller h j gap (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) (controlPart middle) (queuePart middle)
      hcChild.scalar (tailPart middle) nextStorage) h.aux
    let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell precision hG hGK hr
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
      (CompactComplexActualCallAlignment.nativeCost D d hslots pc true
        (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh precision)) hpack)
    ∃ hn : Reached stage rows ell precision (k+2) pNum growthC axes baseline levels frames (returned+childVolume) pref
      (parentLive+gap) pcStack origin calls start,
      hn.data=returnedData h j gap (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) ∧
      let after := basisArray stage (rows/roles) ell precision hG hGK hr hslots pc true
        (hn.data (CompactComplexScalarRolePorts.roleIndex.symm j))
      ∃ final : Reached stage rows ell precision (k+2) pNum growthC axes baseline levels frames (returned+childVolume) pref
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
  have hh := CompactComplexSourceReadyCapturedChildFrames.snapshot_headers
    rho visit hactive pair h call headerStack liveStack hpcHeader.symm hstacks
  have hl := CompactComplexSourceReadyCapturedChildFrames.snapshot_live
    rho visit hactive pair h call headerStack liveStack hstacks.symm hpcLive.symm
  have ht := CompactComplexSourceReadyCapturedChildFrames.snapshot_target
    rho visit hactive pair h call headerStack liveStack
  have hp := CompactComplexSourceReadyCapturedChildFrames.snapshot_payload
    rho visit hactive pair h call headerStack liveStack
  have hheaderClean := hclean (Fin.natAdd 10 headerStack) (Or.inl rfl)
  have hliveClean := hclean (Fin.natAdd 10 liveStack) (Or.inr (Or.inl rfl))
  have htargetClean := hclean (⟨9,by omega⟩ : Fin (10+s)) (Or.inr (Or.inr (Or.inr rfl)))
  exact CompactComplexAlignedCompletedReturnPath.runs rho visit hactive pair call rows ell precision
    headerStack pcStack liveStack origin calls (k+2) parentLive gap cp cC caxes cbaseline clevels
    cframes creturned cpref cn cv hcChild hchildSlots hchildDiv hchildTarget
    (CompactComplexSourceReadyCapturedChildFrames.snapshot rho visit hactive pair h call headerStack liveStack)
    settled rfl rfl hstacks
    (h.storage.tape (Fin.natAdd 10 headerStack)) (h.storage.head (Fin.natAdd 10 headerStack))
    (by omega) hr hd rfl hG hh.2 hh.1 hheaderClean
    (h.storage.tape (Fin.natAdd 10 liveStack)) (h.storage.head (Fin.natAdd 10 liveStack)) childVolume progress
    hl.2 hl.1 (fun z hz _ => hliveClean z hz)
    pNum growthC axes baseline levels frames returned pref pv h hc hA hK hp
    (h.storage.tape (⟨9,by omega⟩ : Fin (10+s))) (h.storage.head (⟨9,by omega⟩ : Fin (10+s)))
    ledgerN ledgerLeft ledgerExponent ledger ht.2 ht.1 (fun z hz _ => htargetClean z hz)
    D P K hP path ha hmeta haxes hC hroom hgap hgrid hGK hrows hpay hslots hpack hpcHeader hpcLive

/-- The named role-bank cardinality agrees with the original child wire layout. -/
theorem child_address_div {rows : ℕ} (hdiv : roles∣rows/roles) :
    CompactComplexNonleafChildAddress.roles∣rows/roles := by
  simpa only [CompactComplexNonleafChildAddress.roles,roles,CompactComplexRolePhaseSite.roleCount,
    Networks.NetworkBudget.complex_role_card_25] using hdiv

theorem recursive_runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) (rows ell precision : ℕ)
    (headerStack pcStack liveStack : Fin s) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (parentLive cp cC caxes clevels cframes creturned cpref cn : ℕ)
    (pNum growthC axes baseline levels frames returned pref : ℕ)
    (pv : Tapes (nodeTapes s roles) 2)
    (h : Reached (parent rho visit hactive pair) rows ell precision (k+2) pNum growthC axes
      baseline levels frames returned pref parentLive pcStack origin calls pv)
    (cv : Tapes (nodeTapes s roles) 2)
    (hcChild : Reached (child rho visit hactive pair call.slot) (rows/roles) ell precision ((k+2)-1)
      cp cC caxes baseline clevels cframes creturned cpref cn pcStack origin (call::calls) cv)
    (hchildSlots : (child rho visit hactive pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (hchildDiv : roles∣rows/roles) (hchildTarget : hcChild.targetValue=parentLive+(2*arity^(k+1)))
    (settled : Settled
      (CompactComplexSourceReadyCapturedChildFrames.snapshot rho visit hactive pair h call headerStack liveStack)
      hcChild.storage hcChild.aux)
    (hstacks : headerStack≠liveStack)
    (hr : 0<rows/roles) (hd : roles ∣ rows) (hG : 1≤sh.guard)
    (hclean : ∀ i,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack i → ∀ z,h.storage.head i≤z → h.storage.tape i z=blank)
    (childPath : CompactRecursiveDependencyBudget.Path sh.active
      (left+call.slot.val*arity^(k+1)) ((k+2)-1) clevels cframes creturned)
    (hbase : baseline≤pNum)
    (hdenRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤sh.chunk)
    (hcompleted : parentLive+2*arity^(k+1)≤cn)
    (hc : 0<roles) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (ledgerN ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN h.targetValue ledgerLeft ledgerExponent)
    (D : ℕ) (P : Program ActivePrefixStageNative.tapes q prime) (K : ℝ)
    (hP : CompactComplexAlignedChildEntryPath.BasisRuns D q P K)
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (ha : 0<sh.active) (hmeta : pNum+2*sh.bits≤precision) (haxes : axes+(2*arity^(k+1))≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤growthC)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient growthC+Nat.clog 2 (growthC+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hsem : ∀ i,CompactSpectatorInheritedGrid.decoded sh (rows/roles) ell (precision-2*sh.bits)
      (parentLive+2*arity^(k+1)) (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) i=
      CompactComplexCorrectedChildGridSemantics.tensor call
        (fun wire address => CompactSpectatorInheritedGrid.decoded sh (rows/roles) ell (precision-2*sh.bits) parentLive
          (roleData h (CompactComplexRolePhaseSite.role call.site))
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/roles) ell (child_address_div hchildDiv) rho
            (Visit.child visit call.slot) i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/roles) ell (child_address_div hchildDiv) i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/roles) ell (child_address_div hchildDiv) rho
          (Visit.child visit call.slot) i))
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
    let middle := mid j (caller h) (popped (CompactComplexSourceReadyCompletedChildBoundary.completed hcChild hchildSlots hchildDiv call) pcStack older top) headerStack liveStack (h.storage.tape (Fin.natAdd 10 headerStack)) (h.storage.head (Fin.natAdd 10 headerStack)) (h.storage.tape (Fin.natAdd 10 liveStack)) (h.storage.head (Fin.natAdd 10 liveStack)) (k+2) parentLive (parentLive+(2*arity^(k+1)))
      rho visit hactive pair rows ell precision (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call)))
    let nextStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart middle)
      (parentLive+(2*arity^(k+1))) (h.storage.tape (⟨9,by omega⟩ : Fin (10+s))) (h.storage.head (⟨9,by omega⟩ : Fin (10+s))) h.targetValue
    let start := canonical (returnedCaller h j (2*arity^(k+1)) (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) (controlPart middle) (queuePart middle)
      hcChild.scalar (tailPart middle) nextStorage) h.aux
    let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell precision hG hGK hr
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
      (CompactComplexActualCallAlignment.nativeCost D d hslots pc true
        (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh precision)) hpack)
    ∃ hn : Reached stage rows ell precision (k+2) pNum growthC axes baseline levels frames (returned+(arity^(k+1))) pref
      (parentLive+(2*arity^(k+1))) pcStack origin calls start,
      hn.data=returnedData h j (2*arity^(k+1)) (CompactComplexSourceReadyCompletedChildBoundary.result hcChild hchildSlots hchildDiv call) ∧
      let after := basisArray stage (rows/roles) ell precision hG hGK hr hslots pc true
        (hn.data (CompactComplexScalarRolePorts.roleIndex.symm j))
      ∃ final : Reached stage rows ell precision (k+2) pNum growthC axes baseline levels frames (returned+(arity^(k+1))) pref
        (parentLive+(2*arity^(k+1))) pcStack origin calls (canonical (replacementCaller hn j after) hn.aux),
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
  have hbaseWidth : baseline≤precision-2*sh.bits := by omega
  have hpow : arity^(k+1)≤arity^(k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hvolume : 2*arity^(k+1)≤2*arity^(k+2) := Nat.mul_le_mul_left 2 hpow
  have progress := CompactComplexSourceReadyCompletedReturnGrid.computed_progress h path hcChild
    childPath rfl hmetadata hbaseWidth hdenRoom hvolume hcompleted
  have grid := CompactComplexSourceReadyCompletedReturnGrid.computed_grid h call rho
    (Visit.child visit call.slot) (child_address_div hchildDiv) hmetadata hcChild hchildSlots hchildDiv hsem
  exact runs rho visit hactive pair call rows ell precision headerStack pcStack liveStack origin calls
    parentLive (2*arity^(k+1)) cp cC caxes baseline clevels cframes creturned cpref cn
    pNum growthC axes baseline levels frames returned pref pv h cv hcChild hchildSlots hchildDiv hchildTarget
    settled hstacks hr hd hG hclean (arity^(k+1)) progress hc hA hK
    ledgerN ledgerLeft ledgerExponent ledger D P K hP path ha hmeta haxes hC hroom le_rfl grid
    hGK hrows hpay hslots hpack hpcHeader hpcLive

end
end IntegerMultBounds.Machine.CompactComplexAlignedCapturedReturnPath
