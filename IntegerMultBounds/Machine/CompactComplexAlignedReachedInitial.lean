module

public import IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths
public import IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath

/-! The actual corrected source boundary both executes and establishes the
concrete reached event invariant. All physical runs follow from original input
words, numerical guards and dependency data; no execution callback is supplied. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedReachedInitial
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexNativeCodecFrame (bank)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexDenominatorCapacity (ledger scalarRows)
variable {s nativeStates : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount

/-- The source/sink control layout is exactly the canonical reached layout. -/
theorem full_canonical (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (aux : Tapes 2 2) :
    (CompactComplexSourceReadyNonleafContraction.ready w (aux.append (SharedBank.empty 7 2))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append
      (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)=ready (canonical w aux) := by
  unfold CompactComplexSourceReadyNonleafContraction.ready
  rw [CompactComplexSourceReadyNonleafFinalGeometry.entry_append]
  rfl

theorem initial_path (P : Program ActivePrefixStageNative.tapes nativeStates Networks.Shared50ModularControl.prime)
    (headerStack liveStack : Fin s) {left k levels frames returned : ℕ}
    (stage : ActivePrefixStageParameters.Stage sh)
    (hslots : stage.slots=CompactComplexRecursiveGeometry.arity)
    (hf : stage.f=CompactComplexRecursiveGeometry.arity^k) (hleft : stage.left=left)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk) (hpay : sh.payload=1)
    (rows ell q p C baseline n : ℕ) (hr : 0<rows) (hbase : baseline≤q)
    (hroom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk) (hd : roles∣rows) (f : Array sh rows ell)
    (dependency : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (old : Tapes (10+s) 2) (aux : Tapes 2 2)
    (hblank : old.head ⟨0,by omega⟩=0 ∧ old.tape ⟨0,by omega⟩=(fun _ => blank))
    (hlive : old.head ⟨7,by omega⟩=1 ∧ old.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (htarget : old.head ⟨8,by omega⟩=0 ∧ old.tape ⟨8,by omega⟩=(fun _ => blank))
    (hclock : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank))
    (hfree : CompactComplexSourceReadyPrefixReadiness.BlankAfter aux 0)
    (he : control.head 1=1 ∧ control.tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (k+1)))
    (h28 : control.head 28=0 ∧ control.tape 28=(fun _ => blank))
    (h29 : control.head 29=0 ∧ control.tape 29=(fun _ => blank))
    (hledger : n≤ledger scalarRows baseline levels frames returned (CompactFramedScalarGrid.rows 0).length)
    (pcStack : Fin s) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (hCalls : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (old.tape (Fin.natAdd 10 pcStack)) (old.head (Fin.natAdd 10 pcStack))) :
    let metadataP := ButterflyIndependentGuardHeaders.reservation sh.bits q
    let w := CompactComplexCorrectedEntryGeometryReadiness.permanent stage hslots rows ell metadataP n k hd f
      control queue scalar tail old
    ∃ h : Reached stage rows ell metadataP (k+1) p C 0 baseline levels frames returned 0 n pcStack origin calls
      (canonical w aux),
      (h.data=fun a => CompactComplexCorrectedEntryGeometryReadiness.array stage hslots rows ell metadataP hd f
        (CompactComplexScalarRolePorts.roleIndex a)) ∧
      ∃ time≤CompactComplexSourceReadyNonleafTargetSplit.constant roles*CompactNativeRoleTransferBudget.volume rows sh ell metadataP+1+
        NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*CompactNativeRoleTransferBudget.volume rows sh ell metadataP+1,
        CompactComplexAlignedScalarEventPath.path P headerStack pcStack liveStack
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length 2)
          (CompactComplexAlignedScalarEventPath.bank (canonical
            (bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataP) tail old
              (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f roles)) aux)) time
          (CompactComplexSourceReadyCorrectedEntryTablePath.firstEventPC CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length)
          (CompactComplexAlignedScalarEventPath.bank (canonical w aux)) := by
  dsimp only
  let metadataP := ButterflyIndependentGuardHeaders.reservation sh.bits q
  obtain ⟨hn,heq⟩ := CompactComplexSourceReadyReachedEventInvariant.initial stage hslots
    rows ell q p C baseline n hd f dependency hp hchunk hw hg control queue scalar tail old aux
    hblank hlive hclock hfree he h28 h29 hledger pcStack origin calls hCalls
  refine ⟨hn,heq,?_⟩
  have hwidth : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP := hw
  have hdependency : CompactRecursiveDependencyBudget.Path sh.active stage.left (k+1) levels frames returned := by
    rw [hleft]
    exact dependency
  have hliveBound : n≤ledger scalarRows baseline levels frames returned 0 := by
    simpa only [CompactFramedScalarGrid.rows,List.take_zero,List.map_nil,Networks.GroupedCircuit.compileGroups,List.flatMap_nil,List.length_nil] using hledger
  obtain ⟨time,ht,hpath⟩ := CompactComplexAlignedBoundaryPaths.tag2_path P headerStack pcStack liveStack
    stage k rows ell metadataP n hslots hf hr hd hG hA hGK hpay
    (by unfold metadataP ButterflyIndependentGuardHeaders.reservation;omega)
    control queue scalar tail old aux hlive htarget f hwidth hdependency scalarRows baseline 0
    (by unfold metadataP ButterflyIndependentGuardHeaders.reservation;omega) (by omega) hroom hliveBound
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  refine ⟨time,ht,?_⟩
  rw [full_canonical,full_canonical] at hpath
  exact hpath

end
end IntegerMultBounds.Machine.CompactComplexAlignedReachedInitial
