module

public import IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootTablePath
public import IntegerMultBounds.Machine.CompactComplexFixedNodeRootExit
public import IntegerMultBounds.Machine.CompactComplexSourceReadyFinalCapacity

/-! Root finalization and the real empty-stack halt in the aligned table. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedRootFinal
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexSourceReadyCorrectedFinal (family)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyAlignedActualTable (controls classify savedStackSlot)
open CompactComplexAlignedScalarEventPath (path)
open CompactComplexAlignedBoundaryPaths (alignedBank)
variable {s q : ℕ} {sh : Shape}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyCorrectedFinal.program

private theorem sigma_hoare {t B : ℕ} {P Q : Σ r,Program t r 2} (he : P=Q)
    {before after : Tapes t 2}
    (h : HoareTime P.2 (fun z => z=before) (fun z => z=after) B) :
    HoareTime Q.2 (fun z => z=before) (fun z => z=after) B := by cases he; exact h

private theorem terminal_path (P : Program ActivePrefixStageNative.tapes q Shared50ModularControl.prime)
    (headerStack pcStack liveStack : Fin s)
    (before after : Tapes (CompactComplexActualCallFullAlignment.tapes s roleCount) Shared50ModularControl.prime) (B : ℕ)
    (h : HoareTime (controls pcStack 3).2 (fun z => z=before) (fun z => z=after) B) :
    ∃ time≤B+1,path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3) before time 0 after :=
  CompactComplexFixedNodePaths.terminal_control_path
    (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (classify pcStack) 3 (Or.inr rfl) before after B h

/-- The original empty saved-stack cell remains blank after the common
alphabet encoding and fixed basis-workspace extension. -/
theorem aligned_empty (pcStack : Fin s)
    (v : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) 2)
    (h : v.tape (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack)
      (v.head (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack)-1)=blank) :
    (alignedBank v).tape (savedStackSlot pcStack)
      ((alignedBank v).head (savedStackSlot pcStack)-1)=blank := by
  simp only [alignedBank, savedStackSlot, Alphabet.mapTapes, Tapes.append, Fin.addCases_left]
  rw [h]
  rfl


section Capacity
variable {c : ℕ}
open CompactNativeRoleTransferBudget (volume)
open ActiveRepairRankHeadersCommands (State)
open CompactComplexSourceReadyCorrectedFinal (payload_family family_width)

private theorem root_runs_native_linear_capacity (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    (hsource : payload.head 0=0 ∧ payload.tape 0=fun _ => blank)
    (hroles : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧ payload.tape (Fin.natAdd 1 j)=
      NativeSignedGapReturn.word (CompactComplexStoppedGridHandoff.words
        (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)))
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current≤CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target payload)
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      (contracted (current-target) f) (v.append frame) leaf
    HoareTime (CompactComplexSourceReadyNonleafOrientedFinal.program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage payload) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=w.append scratch)
      (CompactComplexSourceReadyNonleafFinalPath.constant c*volume rows sh ell p+4) := by
  let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
  let ws := fun j => CompactComplexStoppedGridHandoff.words (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
  let ret := CompactComplexControllerExactReturn.returned ws current target payload
  let v := bank control queue scalar old tail (committed storage target) ret
  let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
    (contracted (current-target) f) (v.append frame) leaf
  have hrun := CompactComplexSourceReadyNonleafFinalPath.raw_runs_native_linear_capacity sh rows ell p hc hr hd hgroup
    hG hA hK hP rho left count slots right src dst control queue scalar tail storage payload f hw current target
    hle hcurrent htarget hsource hroles frame leaf currentCapacity
  have hfull := CompactComplexSourceReadyOrientedControls.widen_runs hrun scratch
  have hsave := CompactComplexSourceReadyNonleafFinalPorts.saved sh rows ell p rho left count slots right src dst target
    (contracted (current-target) f) control queue scalar old tail storage ret frame leaf pcStack
  have hempty : w.tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)
      (w.head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)-1)=blank := by
    rw [hsave.1,hsave.2]
    exact hroot
  have hpost := CompactComplexSourceReadyOrientation.root_runs
    (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack) w hempty
  have hpostFull := CompactComplexSourceReadyOrientedControls.widen_runs hpost scratch
  have hseq := hfull.seq hpostFull
  exact hseq.consequence (fun _ h => h) (fun _ h => h) (by omega)

open CompactSpectatorVisitGeometry (Array)
open CompactNativeRoleRecombine (recombine)
open CompactComplexSourceReadyCorrectedRoleRejoin (payload payload_source payload_roles contracted_recombine)

/-- Root finalization starts directly from the actual completed role family. -/
private theorem root_family_runs_native_linear_capacity (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current≤CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (data j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target (payload data))
    let joined := recombine sh rows c ell hd (fun j => contracted (current-target) (data j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      joined (v.append frame) leaf
    HoareTime (CompactComplexSourceReadyNonleafOrientedFinal.program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage (payload data)) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=w.append scratch)
      (CompactComplexSourceReadyNonleafFinalPath.constant c*volume rows sh ell p+4) := by
  have h := root_runs_native_linear_capacity sh rows ell p
    hc hr hd hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage (payload data)
    (recombine sh rows c ell hd data) (CompactNativeRoleRecombine.width sh rows c ell _ hd data hw)
    current target hle hcurrent htarget (payload_source data) (payload_roles sh rows ell hd data)
    frame leaf pcStack hroot scratch currentCapacity
  simp_rw [CompactNativeRoleRecombine.role_recombine] at h
  rw [contracted_recombine] at h
  exact h


private theorem compose_runs_capacity (v : Stage sh) (rows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (hr : 0<rows) (hd : roleCount∣rows) (hgroup : 0<rows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (before : Wire → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (before a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current≤CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1)
    (hblank : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    let old := CompactComplexNativeCodec.raw v rows ell p
    let after := family v hslots ell p before
    let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
    let ret := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target
        (CompactComplexSourceReadyCorrectedRoleRejoin.payload after))
    let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
      (fun j => contracted (current-target) (after j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
    HoareTime (CompactComplexSourceReadyCorrectedFinal.program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=w.append scratch)
      ((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p+4)) := by
  have hsink := CompactComplexSourceReadySinkCorrections.compose_runs v rows ell p
    hslots hG hA hGK hpay hgroup control queue scalar tail storage (fun _ => blank) 0 before
    hw (frame.append (SharedBank.empty 7 2)) leaf scratch hblank
  rw [payload_family v hslots ell p before] at hsink
  have hfinal := root_family_runs_native_linear_capacity sh rows ell p
    (by unfold roleCount; omega) hr hd hgroup hG hA (by omega) hP
    v.rho v.left v.f v.slots v.right v.source.val v.target.val
    control queue scalar tail storage (family v hslots ell p before)
    (family_width v hslots ell p (CompactNativeRoleHeaders.recordWidth sh p) before hw)
    current target hle hcurrent htarget frame leaf
    pcStack hroot scratch currentCapacity
  unfold CompactComplexSourceReadyCorrectedFinal.program
  exact ProgramPairSequence.runs
    (CompactComplexSourceReadySinkCorrections.program (s:=s))
    (CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roleCount) pcStack) hsink hfinal


end Capacity

theorem tag3_path (P : Program ActivePrefixStageNative.tapes q Shared50ModularControl.prime) (headerStack liveStack : Fin s) (v : Stage sh) (rows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (hr : 0<rows) (hd : roleCount∣rows) (hgroup : 0<rows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (before : Wire → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (before a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (dependency : CompactRecursiveDependencyBudget.Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (hblank : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    let old := CompactComplexNativeCodec.raw v rows ell p
    let after := family v hslots ell p before
    let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
    let ret := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target
        (CompactComplexSourceReadyCorrectedRoleRejoin.payload after))
    let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
      (fun j => contracted (current-target) (after j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
    ∃ time≤((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p+4))+1,path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
      (alignedBank ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)) time 0 (alignedBank (w.append scratch)) ∧
      (alignedBank (w.append scratch)).tape (savedStackSlot pcStack)
        ((alignedBank (w.append scratch)).head (savedStackSlot pcStack)-1)=blank := by
  dsimp only
  have hactual := CompactComplexSourceReadyCorrectedRootFinal.compose_runs v rows ell p
    hslots hr hd hgroup hG hA hGK hpay hP control queue scalar tail storage before hw
    current target hle hcurrent htarget dependency R base usedRows hb hu hroom frame leaf
    pcStack hroot scratch hlive hblank
  have hbinary := sigma_hoare
    ((CompactComplexSourceReadyCorrectedActualTable.final_program_eq pcStack).symm.trans
      (CompactComplexSourceReadyCorrectedActualTable.control_final pcStack).symm) hactual
  have hlift := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _
    (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roleCount) Shared50ModularControl.prime) hbinary
  obtain ⟨time,ht,hpath⟩ := terminal_path P headerStack pcStack liveStack _ _ _ hlift
  refine ⟨time,ht,hpath,?_⟩
  apply aligned_empty
  exact CompactComplexSourceReadyCorrectedRootTablePath.output_empty sh rows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val target
    _ control queue scalar _ tail storage _ frame leaf pcStack scratch hroot


theorem tag3_trace (P : Program ActivePrefixStageNative.tapes q Shared50ModularControl.prime) (headerStack liveStack : Fin s) (v : Stage sh) (rows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (hr : 0<rows) (hd : roleCount∣rows) (hgroup : 0<rows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (before : Wire → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (before a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (dependency : CompactRecursiveDependencyBudget.Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (hblank : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    let old := CompactComplexNativeCodec.raw v rows ell p
    let after := family v hslots ell p before
    let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
    let ret := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target
        (CompactComplexSourceReadyCorrectedRoleRejoin.payload after))
    let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
      (fun j => contracted (current-target) (after j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
    ∃ time≤((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p+4))+1+2, ∃ c,
      FiniteFlow.Trace
        (CompactComplexFixedNodePaths.nodeFamily (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
          (savedStackSlot pcStack) (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
          (controls pcStack) (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack))
        (CompactComplexFixedNodePaths.nodeNext (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
          (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack) (controls pcStack)
          (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack) (classify pcStack))
        (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
        (alignedBank ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)) time 0 c ∧ c.tapes=alignedBank (w.append scratch) := by
  dsimp only
  obtain ⟨time,ht,hpath,hempty⟩ := tag3_path P headerStack liveStack v rows ell p
    hslots hr hd hgroup hG hA hGK hpay hP control queue scalar tail storage before hw
    current target hle hcurrent htarget dependency R base usedRows hb hu hroom frame leaf
    pcStack hroot scratch hlive hblank
  obtain ⟨c,htail,hc⟩ := CompactComplexFixedNodeRootExit.root_trace
    (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack) (classify pcStack) _ hempty
  exact ⟨time+2,by omega,c,FiniteFlowPath.append_trace hpath htail,hc⟩

/-- Root tag three uses the actual retained live-field capacity, with the
same physical endpoint and paid fixed cost as the original root path. -/
theorem tag3_path_capacity (P : Program ActivePrefixStageNative.tapes q Shared50ModularControl.prime) (headerStack liveStack : Fin s) (v : Stage sh) (rows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (hr : 0<rows) (hd : roleCount∣rows) (hgroup : 0<rows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (before : Wire → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (before a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current≤CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1)
    (hblank : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    let old := CompactComplexNativeCodec.raw v rows ell p
    let after := family v hslots ell p before
    let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
    let ret := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target
        (CompactComplexSourceReadyCorrectedRoleRejoin.payload after))
    let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
      (fun j => contracted (current-target) (after j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
    ∃ time≤((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p+4))+1,path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
      (alignedBank ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)) time 0 (alignedBank (w.append scratch)) ∧
      (alignedBank (w.append scratch)).tape (savedStackSlot pcStack)
        ((alignedBank (w.append scratch)).head (savedStackSlot pcStack)-1)=blank := by
  dsimp only
  have hactual := compose_runs_capacity v rows ell p
    hslots hr hd hgroup hG hA hGK hpay hP control queue scalar tail storage before hw
    current target hle hcurrent htarget frame leaf
    pcStack hroot scratch currentCapacity hblank
  have hbinary := sigma_hoare
    ((CompactComplexSourceReadyCorrectedActualTable.final_program_eq pcStack).symm.trans
      (CompactComplexSourceReadyCorrectedActualTable.control_final pcStack).symm) hactual
  have hlift := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _
    (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roleCount) Shared50ModularControl.prime) hbinary
  obtain ⟨time,ht,hpath⟩ := terminal_path P headerStack pcStack liveStack _ _ _ hlift
  refine ⟨time,ht,hpath,?_⟩
  apply aligned_empty
  exact CompactComplexSourceReadyCorrectedRootTablePath.output_empty sh rows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val target
    _ control queue scalar _ tail storage _ frame leaf pcStack scratch hroot


theorem tag3_trace_capacity (P : Program ActivePrefixStageNative.tapes q Shared50ModularControl.prime) (headerStack liveStack : Fin s) (v : Stage sh) (rows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (hr : 0<rows) (hd : roleCount∣rows) (hgroup : 0<rows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (before : Wire → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (before a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current≤CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1)
    (hblank : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    let old := CompactComplexNativeCodec.raw v rows ell p
    let after := family v hslots ell p before
    let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
    let ret := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target
        (CompactComplexSourceReadyCorrectedRoleRejoin.payload after))
    let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
      (fun j => contracted (current-target) (after j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
    ∃ time≤((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p+4))+1+2, ∃ c,
      FiniteFlow.Trace
        (CompactComplexFixedNodePaths.nodeFamily (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
          (savedStackSlot pcStack) (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
          (controls pcStack) (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack))
        (CompactComplexFixedNodePaths.nodeNext (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
          (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack) (controls pcStack)
          (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack) (classify pcStack))
        (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
        (alignedBank ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)) time 0 c ∧ c.tapes=alignedBank (w.append scratch) := by
  dsimp only
  obtain ⟨time,ht,hpath,hempty⟩ := tag3_path_capacity P headerStack liveStack v rows ell p
    hslots hr hd hgroup hG hA hGK hpay hP control queue scalar tail storage before hw
    current target hle hcurrent htarget frame leaf
    pcStack hroot scratch currentCapacity hblank
  obtain ⟨c,htail,hc⟩ := CompactComplexFixedNodeRootExit.root_trace
    (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack) (classify pcStack) _ hempty
  exact ⟨time+2,by omega,c,FiniteFlowPath.append_trace hpath htail,hc⟩

end
end IntegerMultBounds.Machine.CompactComplexAlignedRootFinal
