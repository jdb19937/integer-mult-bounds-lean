module

public import IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths
public import IntegerMultBounds.Machine.CompactComplexSourceReadyFinalCapacity

/-! Actual-capacity finalization in the unchanged aligned table. The literal
sink, contraction, rejoin and post-orientation execute with the original paid
cost and retain every appended basis tape. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNativeCodecFrame (bank)
open NativeEndpointCharacterEntryRoles (data)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexFixedNodeTable
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyAlignedActualTable (controls classify savedStackSlot)
open CompactComplexAlignedScalarEventPath (path)
variable {s q : ℕ} {sh : Shape}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyCorrectedEntry.program
  returnDestination eventDestination

private theorem sigma_hoare {t a B : ℕ} {P Q : Σ r,Program t r a} (he : P=Q)
    {before after : Tapes t a}
    (h : HoareTime P.2 (fun z => z=before) (fun z => z=after) B) :
    HoareTime Q.2 (fun z => z=before) (fun z => z=after) B := by cases he; exact h

private theorem sigma_control_local_path {t a N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q a)
    (ctrl : Fin 4 → Σ q,Program t q a) (events : Fin length → Σ q,Program t q a)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (ctrl pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin 4) (dest : Fin (N+(4+length)+2))
    (P : Σ q,Program t q a) (hP : P=ctrl i) (before after : Tapes t a) (B : ℕ)
    (hlocal : HoareTime P.2 (fun z => z=before) (fun z => z=after) B)
    (he : ∀ st,ce i st=some dest) :
    ∃ time≤B+1,FiniteFlowPath.Path
      (GuardedFiniteReturnExtraFlow.family (k:=k) stack
        (fun pc => (tableProgramsWith returns ctrl events pc).1)
        (fun pc => (tableProgramsWith returns ctrl events pc).2))
      (GuardedFiniteReturnExtraFlow.next hN
        (fun pc => (tableProgramsWith returns ctrl events pc).1)
        (tableEdgesWith returns ctrl events re ce ee))
      (controlPCFor N length i) before time dest after := by
  exact CompactComplexFixedNodePaths.control_local_path hN stack returns ctrl events re ce ee
    i dest before after B (sigma_hoare hP hlocal) he

private theorem generic_control_path {t a : ℕ} (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ r,Program t r a)
    (ctrl : Fin 4 → Σ r,Program t r a)
    (events : CompactComplexCompletedLiveLower.Event → Σ r,Program t r a)
    (classifier : Fin (ctrl 0).1 → Bool) (tag : Fin 4)
    (dest : Fin (originalCount+(4+schedule.length)+2))
    (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (ctrl tag).2 (fun z => z=before) (fun z => z=after) B)
    (he : ∀ st,controlEdgesWith (N:=originalCount) (length:=schedule.length)
      ctrl classifier tag st=some dest) :
    ∃ time≤B+1,CompactComplexFixedNodePaths.nodePath ht stack childReturn ctrl events classifier
      (controlPCFor originalCount schedule.length tag) before time dest after := by
  exact sigma_control_local_path
    (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3))
    stack
    (returnPrograms ht childReturn)
    ctrl (fun i => events (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) ctrl classifier)
    (fun i _ => eventDestination i) tag dest (ctrl tag) rfl before after B h he

private theorem control_path (P : Program ActivePrefixStageNative.tapes q Shared50ModularControl.prime)
    (headerStack pcStack liveStack : Fin s) (tag : Fin 4)
    (dest : Fin (originalCount+(4+schedule.length)+2))
    (before after : Tapes (CompactComplexActualCallFullAlignment.tapes s roleCount) Shared50ModularControl.prime) (B : ℕ)
    (h : HoareTime (controls pcStack tag).2 (fun z => z=before) (fun z => z=after) B)
    (he : ∀ st,controlEdgesWith (N:=originalCount) (length:=schedule.length)
      (controls pcStack) (classify pcStack) tag st=some dest) :
    ∃ time≤B+1,path P headerStack pcStack liveStack
      (controlPCFor originalCount schedule.length tag) before time dest after := by
  exact generic_control_path (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (controls pcStack) (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (classify pcStack) tag dest before after B h he

open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexSourceReadyCorrectedFinal (family)
open CompactComplexControllerExactReturn (contracted committed)

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
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)))
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current ≤ CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1)
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
        CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p)+1,path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
      (alignedBank ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)) time 0 (alignedBank ((CompactComplexSourceReadyOrientation.output call w joined).append scratch)) := by
  dsimp only
  have hactual := CompactComplexSourceReadyCorrectedFinal.compose_runs_capacity v rows ell p
    hslots hr hd hgroup hG hA hGK hpay hP control queue scalar tail storage before hw
    current target hle hcurrent htarget frame leaf
    pcStack call older origin hstack scratch currentCapacity hblank
  have hbinary := sigma_hoare
    ((CompactComplexSourceReadyCorrectedActualTable.final_program_eq pcStack).symm.trans
      (CompactComplexSourceReadyCorrectedActualTable.control_final pcStack).symm) hactual
  have hlift := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _
    (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roleCount) Shared50ModularControl.prime) hbinary
  exact control_path P headerStack pcStack liveStack 3 0 _ _ _ hlift (fun _ => rfl)

end
end IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths
