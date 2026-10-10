import IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath
import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedChildReturnPath
import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant

/-! The actual decoded return restores parent numerical metadata before
the inverse original selected-role basis word. All fixed table edges and
the sequence join are charged separately from the recursive child. -/
namespace IntegerMultBounds.Machine.CompactComplexAlignedChildReturnPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexActualCallFullAlignment (localTapes tapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedBasisInvariant
open CompactAllAxisPhaseDispatch (count)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexCompletedLiveLower (schedule)
variable {s q : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule CompactComplexRolePhaseSite.roleCount

section Arrays
variable {sh : CompactGadgetReservationShape.Shape}
  (stage : ActivePrefixStageParameters.Stage sh) (m ell metadataP : ℕ)
  (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

/-- The physical basis output, reinterpreted in the native polynomial
coordinates, is exactly the original coefficient permutation. -/
theorem polynomial_basisArray (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) :
    polynomial stage m ell metadataP hG hGK hm
      (basisArray stage m ell metadataP hG hGK hm hslots pc reverse f)=
    CompactComplexActualCallAlignment.coefficients
      (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)
      hslots pc reverse (polynomial stage m ell metadataP hG hGK hm f) := by
  unfold polynomial basisArray
  simp only [Fin.cast_cast,Fin.cast_refl]
  exact CompactComplexScalarNativeEndpoint.unflatten_flatten _

/-- Forward and inverse literal role basis words restore the original array
at its original cardinality, including the immutable polynomial coordinate. -/
theorem basisArray_reverse_forward (hslots : stage.slots=25^3) (pc : Fin count)
    (f : CompactSpectatorVisitGeometry.Array sh m ell) :
    basisArray stage m ell metadataP hG hGK hm hslots pc true
      (basisArray stage m ell metadataP hG hGK hm hslots pc false f)=f := by
  change (fun i => ActivePrefixStageNativePolynomial.flattenArray
    (CompactComplexActualCallAlignment.coefficients
      (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)
      hslots pc true (polynomial stage m ell metadataP hG hGK hm
        (basisArray stage m ell metadataP hG hGK hm hslots pc false f)))
    (Fin.cast (cardinality stage m ell metadataP hG hGK hm).symm i))=f
  rw [polynomial_basisArray]
  rw [CompactComplexActualCallAlignment.coefficients_reverse_forward
    (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm) hslots pc
    (polynomial stage m ell metadataP hG hGK hm f)]
  have he := CompactComplexScalarNativeEndpoint.flatten_unflatten
    (fun i => f (Fin.cast (cardinality stage m ell metadataP hG hGK hm) i))
  unfold polynomial
  rw [he]
  funext i
  simp only [Fin.cast_cast,Fin.cast_refl,id_eq]

end Arrays

private theorem return_path (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Call)
    (before after : Tapes (tapes s roles) prime) (B : ℕ)
    (h : HoareTime (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack call).2
      (fun z => z=before) (fun z => z=after) B) :
    ∃ time≤B+1,CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack
      (CompactComplexScheduledPCDecode.savedPC call) before time
      (CompactComplexScheduledPCLayout.callNextPC call) after := by
  exact CompactComplexFixedNodePaths.decoded_return_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) call before after B h

/-- Exact physical lifting and joining used after the numerical return
bridge has supplied its literal canonical endpoint. This helper is private:
the public return contract must derive the original return execution. -/
private theorem join_return (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Call)
    (before mid after : Tapes (nodeTapes s roles) 2) (returnCost basisCost : ℕ)
    (hr : HoareTime (CompactComplexSourceReadyChildReturnPath.program
      (CompactComplexRolePhaseSite.role call.site) headerStack liveStack)
      (fun z => z=before) (fun z => z=mid) returnCost)
    (hb : HoareTime (CompactComplexActualCallFullAlignment.roleProgram P s roles
      (CompactComplexRolePhaseSite.role call.site) (CompactComplexRolePhaseSite.pc call.site) true)
      (fun z => z=CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready mid)))
      (fun z => z=CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready after))) basisCost) :
    ∃ time≤returnCost+1+basisCost+1,
      CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack
        (CompactComplexScheduledPCDecode.savedPC call)
        (CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready before))) time
        (CompactComplexScheduledPCLayout.callNextPC call)
        (CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready after))) := by
  have he := hoare_extend_eq hr (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  have hl := CompactComplexSourceReadyAlignedActualTable.lift_runs
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack call).2
    _ _ (SharedBank.empty (localTapes roles) prime) he
  exact return_path P headerStack pcStack liveStack call _ _ _ (hl.seq hb)

section Physical
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
variable {c : ℕ} {sh : Shape} {left k : ℕ}

/-- Original physical return block with its real scalar and basis suffixes. -/
def liftedReturn (selected : Fin c) (headerStack liveStack : Fin s) :=
  extend (Alphabet.program CompactNativeRoleConjugatedPorts.encoding
    (extend (program selected headerStack liveStack) CompactComplexSourceReadyScalarWorkspace.scratch)) (localTapes c)

def liftedBank (v : Tapes (CompactComplexSourceReadyWorkspace.tapes s c) 2) :=
  CleanSubbank.bank (s:=localTapes c) (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
    (v.append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))

/-- Callback-free physical return adapter. Its explicit premises are literal
completed-child headers, saved frames and payload readiness from the original
return routine. It makes no claim that recursive execution supplies them. -/
theorem physical_return_runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (result : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (u : Tapes (CompactComplexNonleafRoleChildBank.tapes s c) 2)
    (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/c) (hd : c ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement u=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) (rows/c) ell precision) (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
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
    (selected : Fin c) (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (hresultWidth : ∀ j,(result j).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (result j).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hc : 0<c) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hrawCaller : Placement.active CompactComplexNonleafRoleEntry.headerPlacement caller=
      ActiveRepairRankHeadersCommands.bank (raw (parent rho visit hactive pair) rows ell precision))
    (hclockCaller : caller.head CompactComplexNonleafRoleEntry.clock=0 ∧
      caller.tape CompactComplexNonleafRoleEntry.clock=fun _ => blank)
    (hsourceCaller : caller.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (caller.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision false))
    (hrolesCaller : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (caller.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision true))
    (hfreeCaller : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision true) caller)
    (hstackActual : u.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).head CompactComplexNonleafRoleEntry.stack ∧
      u.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).tape CompactComplexNonleafRoleEntry.stack)
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank)
    (scalar : State) (hscalar : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (rows/c) ell (precision-2*sh.bits) (before j))
    (source : ℤ → Fin 6) (sourceHead : ℤ)
    (hcallerPayload : payloadPart
      ((setTape caller (CompactComplexNonleafRoleEntry.roleTape selected)
        (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh (rows/c) ell selected source sourceHead before result)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN parentTarget ledgerLeft ledgerExponent)
    (htargetStack : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits parentTarget))
    (htargetStackHead : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits parentTarget).length)
    (htargetFree : ∀ z,targetHead≤z → z<targetHead+1+(bits parentTarget).length → targetFrame z=blank)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    let mid := CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    HoareTime (liftedReturn selected headerStack liveStack)
      (fun z => z=liftedBank (CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2)))
      (fun z => z=liftedBank (CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+gap) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/c) ell source sourceHead
            (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/c) ell gap selected before result)))
        (frame mid)) leaf (SharedBank.empty 10 2)))
      (timeConstant c*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  have hr := CompactComplexSourceReadyNormalizedChildReturnPath.runs_linear rho visit hactive pair coordinate
    rows ell precision result u headerStack liveStack hstacks f p e he hr hd heq hG hi ht hp hb hx hhx
    liveFrame liveHead parentLive completed gap progress hstack hstackHead hcurrent hcurrentHead
    htarget htargetHead hfree selected caller hresultWidth hc hA hK hrawCaller hclockCaller
    hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual scalar hscalar before hw
    source sourceHead hcallerPayload targetFrame targetHead ledgerN parentTarget ledgerLeft ledgerExponent
    ledger htargetStack htargetStackHead htargetFree leaf
  have hs := hoare_extend_eq hr (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  have ha := Alphabet.map_hoare CompactNativeRoleConjugatedPorts.encoding hs
  have he : HoareTime (Alphabet.program CompactNativeRoleConjugatedPorts.encoding
      (extend (program selected headerStack liveStack) CompactComplexSourceReadyScalarWorkspace.scratch))
      (fun z => z=Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
        ((CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2)).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))
      (fun z => z=Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding _) _ :=
    ha.consequence (fun _ hz => ⟨_,rfl,hz⟩) (by rintro _ ⟨_,rfl,rfl⟩;rfl) le_rfl
  exact hoare_extend_eq he (SharedBank.empty (localTapes c) prime)

end Physical

open CompactComplexSourceReadyReachedReturnInvariant

/-- The actual inverse basis machine executes on the restored parent
fragments. Numerical return readiness is derived from the parent's reached
state and the child's grid. Restored explicitly records the physical port
facts still required from the completed-child return boundary. -/
theorem exists_restored_inverse_runs (D : ℕ) (hroles : 0<roles) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ K : ℝ,0<K ∧
    ∀ (s : ℕ) (sh : CompactGadgetReservationShape.Shape) (stage : ActivePrefixStageParameters.Stage sh)
      (rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ)
      (pcStack : Fin s) (origin : ℤ) (calls : List Call) (v : Tapes (nodeTapes s roles) 2)
      (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
      (selected : Fin roles) (pc : Fin count) (gap volume : ℕ)
      (child : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
      (_hmetadata : 2*sh.bits≤metadataP) (_hgap : gap≤2*volume)
      (_hw : ∀ i,(child i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
        (child i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
      (_hgrid : CompactSpectatorInheritedGrid.Grid sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
        (CompactFramedScalarGrid.bound pref
          (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes))) child)
      (_hcapacity : gap≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1)
      (_hguard : CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*2^gap<
          2^(CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)))
      (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
      (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (aux : Tapes 2 2)
      (_physical : Restored e (n+gap) h.targetValue pcStack origin calls control storage aux)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (_hr : 0<rows) (hm : 0<rows/roles)
      (_hd : roles∣rows) (_hpay : sh.payload=1) (hslots : stage.slots=25^3)
      (hpack : ∀ op,1<stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell metadataP hG hGK hm) op) D),
      let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell metadataP hG hGK hm
      let start := canonical (returnedCaller h selected gap child control queue scalar tail storage) aux
      ∃ hn : Reached stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
        (n+gap) pcStack origin calls start,
        hn.data=returnedData h selected gap child ∧
        let after := basisArray stage (rows/roles) ell metadataP hG hGK hm hslots pc true
          (hn.data (CompactComplexScalarRolePorts.roleIndex.symm selected))
        let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
          (CompactComplexActualCallAlignment.nativeCost D d hslots pc true
            (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh metadataP)) hpack)
        ∃ ha : Reached stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
          (n+gap) pcStack origin calls (canonical (replacementCaller hn selected after) hn.aux),
          ha.data=replacementData hn selected after ∧
          HoareTime (CompactComplexActualCallFullAlignment.roleProgram P s roles selected pc true)
            (fun z => z=CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready start)))
            (fun z => z=CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
              (ready (canonical (replacementCaller hn selected after) hn.aux))))
            (CompactComplexActualCallRoleAlignment.cost roles stage rows ell metadataP passTime) ∧
          (CompactComplexActualCallRoleAlignment.cost roles stage rows ell metadataP passTime : ℝ)≤
            K*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,K,hK,hP⟩ := CompactComplexAlignedChildEntryPath.exists_basis_runs D hroles
  refine ⟨q,P,K,hK,?_⟩
  intro s sh stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v h
    selected pc gap volume child hmetadata hgap hw hgrid hcapacity hguard control queue scalar tail storage aux physical
    hG hGK hr hm hd hpay hslots hpack
  dsimp only
  obtain ⟨hn,hdata⟩ := returned_reached h selected gap volume child hmetadata hgap hw hgrid hcapacity hguard
    control queue scalar tail storage aux physical
  refine ⟨hn,hdata,?_⟩
  obtain ⟨ha,hadata⟩ := basis_reached hn selected hG hGK hm hslots pc true
  refine ⟨ha,hadata,?_⟩
  exact hP s sh stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
    (n+gap) pcStack origin calls _ hn selected hG hGK hr hm hd hpay hslots pc true hpack

end
end IntegerMultBounds.Machine.CompactComplexAlignedChildReturnPath
