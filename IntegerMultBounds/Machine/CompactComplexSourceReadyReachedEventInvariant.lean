import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarSavedCallHistory
import IntegerMultBounds.Machine.CompactComplexCorrectedEntryGridReadiness
import IntegerMultBounds.Machine.CompactComplexActualScalarNetworkPrefix

/-! Concrete reached scalar-event banks. The raw Stage is the retained original
Stage, not its expanded polynomial codec. The middle bank is the actual child
entry layout, and the call list is associated with the real saved-PC tape. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventInvariant
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes permanent ready output)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarCallerEndpoint (storageOutput emitted)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSequenceSemantics (values)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open Networks.GaussianPrecision (BoundedGrid)
variable {s : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  CompactComplexScalarIntegerRows.gates CompactComplexCompletedLiveLower.schedule

/-- The literal child-ready public/auxiliary/seven/leaf/work layout. -/
def canonical (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (aux : Tapes 2 2) : Tapes (nodeTapes s roles) 2 :=
  CompactComplexSourceReadyWorkspace.ready
    ((CompactComplexSourceReadyScalarChildReadiness.entryBank w aux).append (SharedBank.empty 7 2))

private theorem nested_prefix {P A F L W : ℕ}
    (v : Tapes P 2) (aux : Tapes A 2) (frame : Tapes F 2)
    (leaf : Tapes L 2) (work : Tapes W 2) :
    (⟨fun i => ((((v.append aux).append frame).append leaf).append work).head
      ⟨i.val,by have := i.isLt; omega⟩,
      fun i => ((((v.append aux).append frame).append leaf).append work).tape
      ⟨i.val,by have := i.isLt; omega⟩⟩ : Tapes P 2)=v := by
  apply congrArg₂ Tapes.mk
  · funext i
    change ((((v.append aux).append frame).append leaf).append work).head
      (Fin.castAdd W (Fin.castAdd L (Fin.castAdd F (Fin.castAdd A i))))=v.head i
    simp only [Tapes.append,Fin.addCases_left]
  · funext i
    change ((((v.append aux).append frame).append leaf).append work).tape
      (Fin.castAdd W (Fin.castAdd L (Fin.castAdd F (Fin.castAdd A i))))=v.tape i
    simp only [Tapes.append,Fin.addCases_left]

theorem canonical_permanent (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (aux : Tapes 2 2) : permanent (canonical w aux)=w :=
  nested_prefix w aux (SharedBank.empty 7 2)
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)

theorem canonical_output (before next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (aux : Tapes 2 2) : output (canonical before aux) next=canonical next aux :=
  CompactComplexSourceReadyScalarChildReadiness.scalar_output_bank before next aux _ _ _

/-- Every field is physical readiness or a numerical assertion about the
literal arrays stored on that bank. No field supplies an execution callback. -/
structure Reached (stage : ActivePrefixStageParameters.Stage sh)
    (rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n : ℕ)
    (pcStack : Fin s) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (v : Tapes (nodeTapes s roles) 2) where
  control : Tapes 43 2
  queue : Tapes 1 2
  scalar : ActiveRepairRankHeadersCommands.State
  tail : Tapes 22 2
  storage : Tapes (10+s) 2
  payload : Tapes (1+roles) 2
  aux : Tapes 2 2
  data : Fin CompactComplexScalarRowBlock.wireCount → Array sh (rows/roles) ell
  canonical_bank : v=canonical (bank control queue scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) tail storage payload) aux
  width : ∀ a i,(data a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
    (data a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1
  count_blank : storage.head CompactComplexSourceReadyActualTable.countHeader=0 ∧
    storage.tape CompactComplexSourceReadyActualTable.countHeader=(fun _ => blank)
  role_words : ∀ a,(bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
    tail storage payload).head (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
    (bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
    tail storage payload).tape (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
      CompactSpectatorLeafAxis.word (data a)
  source_blank : payload.head (Fin.castAdd roles (0 : Fin 1))=0 ∧ payload.tape (Fin.castAdd roles (0 : Fin 1))=(fun _ => blank)
  clock_blank : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank)
  aux_free : CompactComplexSourceReadyPrefixReadiness.BlankAfter aux 0
  exponentValue : ℕ
  exponentValue_eq : exponentValue=nodeExponent
  exponent : control.head 1=1 ∧ control.tape 1=BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits exponentValue)
  control28_blank : control.head 28=0 ∧ control.tape 28=(fun _ => blank)
  control29_blank : control.head 29=0 ∧ control.tape 29=(fun _ => blank)
  live : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
    RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n)
  targetValue : ℕ
  target : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
    RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits targetValue)
  target_growth : targetValue≤n+2*CompactComplexRecursiveGeometry.arity^nodeExponent
  upper_ledger : n≤ledger scalarRows baseline levels frames returned (CompactFramedScalarGrid.rows pref).length
  grid : ∀ wire i,BoundedGrid n
    (CompactFramedScalarGrid.bound pref (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
    (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i wire)
  saved_calls : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin calls (ready v)

/-- The genuine corrected source-entry endpoint initializes the physical
invariant from the original parent grid and the original saved stack. -/
theorem initial {left k levels frames returned : ℕ}
    (stage : ActivePrefixStageParameters.Stage sh)
    (hslots : stage.slots=CompactComplexRecursiveGeometry.arity)
    (rows ell q p C baseline n : ℕ) (hd : roles∣rows) (f : Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (old : Tapes (10+s) 2) (aux : Tapes 2 2)
    (hblank : old.head ⟨0,by omega⟩=0 ∧ old.tape ⟨0,by omega⟩=(fun _ => blank))
    (hlive : old.head ⟨7,by omega⟩=1 ∧ old.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
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
      h.data=fun a => CompactComplexCorrectedEntryGeometryReadiness.array stage hslots rows ell metadataP hd f
        (CompactComplexScalarRolePorts.roleIndex a) := by
  dsimp only
  let metadataP := ButterflyIndependentGuardHeaders.reservation sh.bits q
  let st := CompactComplexCorrectedEntryGeometryReadiness.storage old (n+2*CompactComplexRecursiveGeometry.arity^(k+1))
  let pay := CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
    (CompactComplexCorrectedEntryGeometryReadiness.data stage hslots rows ell metadataP hd f)
  let w := bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataP) tail st pay
  have hw0 : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP := hw
  have hw1 := CompactComplexCorrectedEntryGeometryReadiness.array_width stage hslots rows ell metadataP hd f hw0
  have hgrid := CompactComplexCorrectedEntryGridReadiness.array_grid stage hslots rows ell metadataP q hd f
    path p C n hp hchunk hw hg
  have hsave : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin calls (ready (canonical w aux)) := by
    have hs := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack (canonical w aux)
    unfold CompactComplexSourceReadySavedCallHistory.Reached
    rw [hs.1,hs.2,canonical_permanent]
    have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) tail st pay (Fin.natAdd 10 pcStack)
    change CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (w.tape (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack)))
      (w.head (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack)))
    change w.head (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=st.head _ ∧
      w.tape (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=st.tape _ at hb
    rw [hb.1,hb.2]
    have ho := CompactComplexCorrectedEntryGeometryReadiness.storage_ancestor old
      (n+2*CompactComplexRecursiveGeometry.arity^(k+1)) pcStack
    rw [ho.1,ho.2]
    exact hCalls
  refine ⟨{
    control := control, queue := queue, scalar := scalar, tail := tail,
    storage := st, payload := pay, aux := aux,
    data := fun a => CompactComplexCorrectedEntryGeometryReadiness.array stage hslots rows ell metadataP hd f
      (CompactComplexScalarRolePorts.roleIndex a),
    canonical_bank := rfl, width := ?_, count_blank := ?_, role_words := ?_,
    source_blank := ⟨rfl,rfl⟩, clock_blank := hclock, aux_free := hfree,
    exponentValue := k+1, exponentValue_eq := rfl, exponent := he, control28_blank := h28, control29_blank := h29,
    live := CompactComplexCorrectedEntryGeometryReadiness.storage_live old _ n hlive,
    targetValue := n+2*CompactComplexRecursiveGeometry.arity^(k+1),
    target := CompactComplexCorrectedEntryGeometryReadiness.storage_target old _, target_growth := le_rfl,
    upper_ledger := hledger, grid := ?_, saved_calls := hsave },rfl⟩
  · exact fun a i => hw1 _ i
  · exact CompactComplexCorrectedEntryGeometryReadiness.storage_count_blank old _ hblank
  · intro a
    have hc := CompactComplexCorrectedEntryGeometryReadiness.caller_role stage hslots rows ell metadataP n k hd f
      control queue scalar tail old aux (CompactComplexScalarRolePorts.roleIndex a)
    have hb := CompactComplexSourceReadyScalarChildReadiness.entry_prefix w aux
      (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))
    exact ⟨hb.1.symm.trans hc.1,hb.2.symm.trans hc.2⟩
  · intro wire i
    have hh := hgrid (CompactComplexScalarRolePorts.roleIndex (CompactComplexScalarIntegerRows.wireIndex wire)) i
    simpa only [CompactSpectatorInheritedGrid.decoded,
      CompactSpectatorInheritedGrid.half,values,ButterflyStreamSemantics.decode,
      ButterflyIndependentGuardSemantics.half_eq,CompactFramedScalarGrid.bound,CompactFramedScalarGrid.rows,
      List.take_zero,List.map_nil,Networks.GroupedCircuit.compileGroups,List.flatMap_nil,
      Networks.RationalScalarGrid.castRows,Networks.GaussianPrecision.scalarBound,
      Nat.add_zero] using hh

section Successor
variable {stage : ActivePrefixStageParameters.Stage sh}
  {rows ell metadataP nodeExponent p C axes baseline levels frames returned n : ℕ}
  {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {v : Tapes (nodeTapes s roles) 2}

/-- Stored width fixes the exact finite source support needed by real child
entry; it is derived rather than another invariant premise. -/
theorem role_supported {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v)
    (a : Fin CompactComplexScalarRowBlock.wireCount) :
    RoleArrayStack.Supported
      ((bank h.control h.queue h.scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
        h.tail h.storage h.payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a)))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP true) := by
  rw [(h.role_words a).2]
  change RoleArrayStack.Supported (NativeZeroPadding.word (NativeZeroPaddingArray.word (h.data a))) _
  apply RoleArrayStack.supported_word
  have hh := CyclicRowSplit.prefix_length (fun i => ButterflyStreamData.encoded (h.data a i))
    (2*(CompactNativeRoleHeaders.recordWidth sh metadataP+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (h.width a i).1 (h.width a i).2)
    (ButterflySpectatorGeometry.Size (rows/roles) sh.bits (2^ell)) le_rfl
  rw [CyclicRowCycle.prefix_all] at hh
  change (NativeZeroPaddingArray.word (h.data a)).length≤_
  change (NativeZeroPaddingArray.word (h.data a)).length=_ at hh
  rw [hh]
  simp only [CompactComplexSpectatorVolumeHeaders.streamVolume,
    CompactComplexSpectatorVolumeHeaders.roleRows,ite_true,ButterflySpectatorGeometry.Size]
  exact le_of_eq (by ring)

/-- Actual child-entry caller view of a reached bank. -/
def caller {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v) :=
  CompactComplexSourceReadyScalarChildReadiness.entryBank
    (bank h.control h.queue h.scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
      h.tail h.storage h.payload) h.aux

theorem child_headers {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement (caller h)=
      ActiveRepairRankHeadersCommands.bank (CompactComplexNativeCodec.raw stage rows ell metadataP) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_headers _ _ _ _ _ _ _ _

theorem child_source {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v) :
    (caller h).head CompactComplexNonleafRoleEntry.source=0 ∧
    (caller h).tape CompactComplexNonleafRoleEntry.source=(fun _ => blank) := by
  have hz : Fin.castAdd roles (0 : Fin 1)=(0 : Fin (1+roles)) :=
    Fin.ext (by simp only [Fin.val_castAdd,Fin.val_zero])
  have hp := h.source_blank
  rw [hz] at hp
  have hb := CompactComplexSourceReadyPrefixReadiness.source_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload
  have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (bank h.control h.queue h.scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
      h.tail h.storage h.payload) h.aux (CompactComplexSpectatorTargetBank.numericSlot 65)
  exact ⟨he.1.trans (hb.1.trans hp.1),he.2.trans (hb.2.trans hp.2)⟩

theorem child_clock {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v) :
    (caller h).head CompactComplexNonleafRoleEntry.clock=0 ∧
    (caller h).tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_clock _ _ h.clock_blank

theorem child_free {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v)
    (selected : Fin roles) (masterVolume roleVolume : ℕ) :
    CompactComplexNonleafRoleReturn.Free selected masterVolume roleVolume (caller h) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_free _ _ h.aux_free selected masterVolume roleVolume

theorem child_exponent {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v) :
    Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      ((caller h).append (SharedBank.empty 7 2))=CompactComplexExponentStep.bank h.exponentValue :=
  CompactComplexSourceReadyScalarChildReadiness.entry_exponent _ _ _ _ _ _ _ _ _ _
    h.exponent h.control28_blank h.control29_blank

theorem child_role_supported {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v)
    (a : Fin CompactComplexScalarRowBlock.wireCount) :
    RoleArrayStack.Supported ((caller h).tape
      (CompactComplexNonleafRoleEntry.roleTape (CompactComplexScalarRolePorts.roleIndex a)))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP true) := by
  have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (bank h.control h.queue h.scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
      h.tail h.storage h.payload) h.aux
    (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))
  have ht : (caller h).tape (CompactComplexNonleafRoleEntry.roleTape (CompactComplexScalarRolePorts.roleIndex a))=
      (bank h.control h.queue h.scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
        h.tail h.storage h.payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a)) := he.2
  rw [ht]
  exact role_supported h a

def nextCaller {pref : ℕ}
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned pref n pcStack origin calls v)
    (g : GroupIndex) :=
  bank h.control h.queue h.scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
    h.tail (storageOutput (by omega : 7<10+s) h.storage (n+(gates g).length))
    (emitted h.payload (fun j => CompactSpectatorLeafAxis.word
      (execute (block g) h.data (CompactComplexScalarRolePorts.roleIndex.symm j))))

/-- One actual scalar lifecycle advances all concrete reached-bank fields,
retaining the real child-entry layout and genuine associated call list. -/
theorem scalar_successor {left : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left nodeExponent levels frames returned)
    (g : GroupIndex)
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned g.val n pcStack origin calls v)
    (hrows : 0<rows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk) :
    HoareTime (CompactComplexSourceReadyActualTable.scalar (s:=s) g).2
      (fun z => z=ready v) (fun z => z=ready (output v (nextCaller h g)))
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block g)*
        (rows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    ∃ hn : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned (g.val+1)
      (n+(gates g).length) pcStack origin calls (output v (nextCaller h g)),
      hn.data=execute (block g) h.data := by
  have hv : permanent v=bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload := by
    exact (congrArg permanent h.canonical_bank).trans (canonical_permanent _ _)
  obtain ⟨hr,hw,hgrid,_,hledger⟩ := CompactComplexSourceReadyScalarGeometryEventPath.group_step
    path stage rows hrows hG hK g ell p C axes metadataP n h.control h.queue h.scalar
    h.tail h.storage h.payload v hv h.data h.width h.count_blank h.role_words h.live
    ha hp haxes hroom hC baseline hbase hdenRoom h.upper_ledger h.grid
  have hnext := CompactComplexSourceReadyScalarGeometryEventPath.next_ready rows ell
    (by omega : 7<10+s) CompactComplexSourceReadyActualTable.countHeader
    CompactComplexSourceReadyActualTable.countHeader_ne_live h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload
    (execute (block g) h.data) (n+(gates g).length) h.count_blank
  have hstack := CompactComplexSourceReadyScalarSavedCallHistory.output_reached pcStack
    (by omega : 7<10+s) h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload
    (fun j => CompactSpectatorLeafAxis.word
      (execute (block g) h.data (CompactComplexScalarRolePorts.roleIndex.symm j)))
    (n+(gates g).length) origin calls v hv h.saved_calls
  refine ⟨hr,?_⟩
  refine ⟨{
    control := h.control, queue := h.queue, scalar := h.scalar, tail := h.tail,
    storage := storageOutput (by omega) h.storage (n+(gates g).length),
    payload := emitted h.payload (fun j => CompactSpectatorLeafAxis.word
      (execute (block g) h.data (CompactComplexScalarRolePorts.roleIndex.symm j))),
    aux := h.aux, data := execute (block g) h.data,
    canonical_bank := ?_, width := hw, count_blank := ⟨hnext.1,hnext.2.1⟩,
    role_words := hnext.2.2, source_blank := ?_, clock_blank := h.clock_blank,
    aux_free := h.aux_free, exponentValue := h.exponentValue, exponentValue_eq := h.exponentValue_eq, exponent := h.exponent, control28_blank := h.control28_blank,
    control29_blank := h.control29_blank, live := ?_, targetValue := h.targetValue,
    target := ?_, target_growth := by have ht := h.target_growth; omega, upper_ledger := hledger,
    grid := fun wire i => hgrid i wire, saved_calls := hstack },rfl⟩
  · exact (congrArg (fun z => output z (nextCaller h g)) h.canonical_bank).trans
      (canonical_output _ _ _)
  · change (emitted h.payload _).head (Fin.castAdd roles (0 : Fin 1))=0 ∧
      (emitted h.payload _).tape (Fin.castAdd roles (0 : Fin 1))=(fun _ => blank)
    simpa only [emitted,Fin.addCases_left] using h.source_blank
  · simp only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_self,and_self]
  · have hne : (⟨8,by omega⟩ : Fin (10+s))≠⟨7,by omega⟩ := by
      intro he; have hv := congrArg Fin.val he; change (8 : ℕ)=7 at hv; omega
    simpa only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_of_ne hne] using h.target

/-- The same concrete successor is reached by the actual corrected cyclic
controller table, with its real jump included in the paid volume bound. -/
theorem scalar_table_successor {left : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left nodeExponent levels frames returned)
    (g : GroupIndex)
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned g.val n pcStack origin calls v)
    (hrows : 0<rows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (headerStack liveStack : Fin s)
    (i : Fin CompactComplexCompletedLiveLower.schedule.length)
    (hi : CompactComplexCompletedLiveLower.schedule.get i=CompactComplexCompletedLiveLower.Event.scalar g) :
    ∃ hn : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned (g.val+1)
      (n+(gates g).length) pcStack origin calls (output v (nextCaller h g)),
      hn.data=execute (block g) h.data ∧
      ∃ m≤(CompactComplexScalarCountLifecycle.roleTimeConstant (block g)+1)*
        (rows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth),
        CompactComplexSourceReadyCorrectedSavedReturnPath.path headerStack pcStack liveStack
          (CompactComplexScheduledPCLayout.eventPC i) (ready v) m
          (CompactComplexScheduledPCLayout.nextPC i) (ready (output v (nextCaller h g))) := by
  obtain ⟨_,hn,he⟩ := scalar_successor path g h hrows hG hK ha hp haxes hroom hC hbase hdenRoom
  have hv : permanent v=bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) h.tail h.storage h.payload :=
    (congrArg permanent h.canonical_bank).trans (canonical_permanent _ _)
  obtain ⟨m,hm,hpath,_⟩ := CompactComplexSourceReadyScalarSavedCallHistory.scalar_path_reached
    path stage rows hrows hG hK g ell p C axes metadataP n h.control h.queue h.scalar
    h.tail h.storage h.payload v hv h.data h.width h.count_blank h.role_words h.live
    ha hp haxes hroom hC baseline hbase hdenRoom h.upper_ledger h.grid
    headerStack pcStack liveStack origin calls h.saved_calls i hi
  exact ⟨hn,he,m,hm,hpath⟩

/-- The numerical refinement names an actual segment of the original compiler
network. Child events must establish its alignment before the scalar event. -/
def AlignedPrefix (columns : ℕ) (g : GroupIndex)
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned g.val n pcStack origin calls v)
    (lookup : Networks.BinaryColumns.Address (25^3) columns →
      Fin (ButterflySpectatorGeometry.Size (rows/roles) sh.bits (2^ell)))
    (original : CompactComplexScalarIntegerRows.Wire → Networks.BinaryColumns.Arrays (25^3) columns) : Prop :=
  CompactComplexActualScalarNetworkPrefix.bank columns (ButterflyGuard.halfWidth metadataP sh.bits) n h.data lookup=
    Networks.FramedCircuit.run (CompactComplexActualScalarNetworkPrefix.networkPrefix columns g.val++
      CompactComplexActualScalarNetworkPrefix.alignment columns g) original

/-- The exact arrays installed by scalar_successor represent the next literal
original-network prefix, rather than an assumed completed-network endpoint. -/
theorem scalar_original_prefix {left : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left nodeExponent levels frames returned)
    (columns : ℕ) (g : GroupIndex)
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned g.val n pcStack origin calls v)
    (lookup : Networks.BinaryColumns.Address (25^3) columns →
      Fin (ButterflySpectatorGeometry.Size (rows/roles) sh.bits (2^ell)))
    (original : CompactComplexScalarIntegerRows.Wire → Networks.BinaryColumns.Arrays (25^3) columns)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (halign : AlignedPrefix columns g h lookup original) :
    CompactComplexActualScalarNetworkPrefix.bank columns (ButterflyGuard.halfWidth metadataP sh.bits)
      (n+(gates g).length) (execute (block g) h.data) lookup=
      Networks.FramedCircuit.run (CompactComplexActualScalarNetworkPrefix.networkPrefix columns (g.val+1)) original := by
  have hroom' : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      (block g).length*guardBits≤sh.chunk := by
    simpa only [CompactComplexScalarSegmentRows.block_length] using hroom
  simpa only [CompactComplexScalarSegmentRows.block_length] using
    CompactComplexActualScalarNetworkPrefix.group_prefix_advance path columns g h.data lookup
      p C axes metadataP n ha hp haxes hC hroom' h.width h.grid original halign

end Successor

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventInvariant
