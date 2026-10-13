module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal

/-! Actual contraction, row rejoin and saved-call post-orientation retain their
original programs, endpoints and linear costs when live capacity is supplied
by the actual reached cursor. No dependency Path at an advanced sibling ledger
is required. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPath
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSourceReadyNonleafFinalGeometry
open CompactComplexControllerExactReturn (contracted committed)
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexNonleafRoleMergeCurrent.program

/-- Actual finalization with the unchanged endpoint and cost, paid by the
true retained current-denominator capacity rather than an advanced Path. -/
theorem raw_runs_native_linear_capacity (sh : Shape) (rows ell p : ℕ)
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
    (currentCapacity : current ≤ CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target payload)
    HoareTime (program (s:=s) (c:=c)).2
      (fun z => z=CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage payload) (frame.append (SharedBank.empty 7 2)) leaf)
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        ((CompactComplexNonleafRoleMergeCurrent.bank sh rows ell p rho left count slots right src dst
          (contracted (current-target) f) (v.append frame)).append (SharedBank.empty 7 2))
        leaf (SharedBank.empty 10 2))
      (constant c*volume rows sh ell p) := by
  let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
  let roles := fun j => CompactNativeRoleReservedBridge.role sh rows c ell hd f j
  let ws := fun j => CompactComplexStoppedGridHandoff.words (roles j)
  let ret := CompactComplexControllerExactReturn.returned ws current target payload
  let v := bank control queue scalar old tail (committed storage target) ret
  have hp : ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)=p := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  have hwidth : ∀ j,CompactSpectatorInheritedGrid.Width sh
      (CompactComplexSpectatorVolumeHeaders.roleRows c rows true) ell (p-2*sh.bits) (roles j) := by
    intro j i
    simpa only [CompactSpectatorInheritedGrid.Width,ButterflySpectatorSemantics.Width,
      ButterflySpectatorGeometry.Width,hp,roles,CompactNativeRoleReservedBridge.role,
      CompactNativeRoleGeometry.role,CompactNativeRoleHeaders.recordWidth] using
        (CompactNativeRoleReservedBridge.grouped_width sh rows c ell _ hd f hw _)
  have hcon := CompactComplexSourceReadyNonleafContraction.raw_runs_native_linear_capacity sh c rows ell p true
    hc hr hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage payload
    roles hwidth current target hle hcurrent htarget hroles
    (frame.append (SharedBank.empty 7 2)) leaf currentCapacity
  have hsret := CompactComplexControllerExactReturn.returned_source ws current target payload
  have hs : (v.append frame).head CompactComplexNonleafRoleEntry.source=0 ∧
      (v.append frame).tape CompactComplexNonleafRoleEntry.source=fun _ => blank := by
    have h := CompactComplexSourceReadyNonleafFinalBank.source control queue scalar old tail
      (committed storage target) ret frame
    exact ⟨h.1.trans (hsret.1.trans hsource.1),h.2.trans (hsret.2.trans hsource.2)⟩
  have hrs : ∀ j,(v.append frame).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      (v.append frame).tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh rows c ell hd (contracted (current-target) f) j)) := by
    intro j
    have h := CompactComplexSourceReadyNonleafFinalBank.role control queue scalar old tail
      (committed storage target) ret frame j
    have hr := CompactComplexControllerExactReturn.returned_role roles current target payload j
    refine ⟨h.1.trans hr.1,?_⟩
    rw [h.2,hr.2,words_tape]
    change NativeZeroPadding.word (NativeZeroPaddingArray.word
      (contracted (current-target) (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)))=_
    rw [contracted_role]
  have hm := CompactComplexNonleafRoleMergeCurrentBudget.runs_linear sh rows ell p rho left count slots right src dst
    hc hr hd hG hA hK (contracted (current-target) f) (contracted_width _ f hw) (v.append frame)
    (CompactComplexSourceReadyNonleafFinalBank.headers control queue scalar old tail (committed storage target) ret frame)
    hs hrs
  have hmerge := CompactComplexSourceReadyWorkspace.public_runs hm leaf (SharedBank.empty 10 2)
  have hcon' := hcon
  simp only [CompactComplexSourceReadyNonleafContraction.ready,entry_append] at hcon'
  have hseq := hcon'.seq hmerge
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact hseq.consequence
    (fun _ h => by simpa only [CompactComplexSourceReadyNonleafContraction.ready,entry_append] using h)
    (fun _ h => h) (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPath

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}

/-- Actual finalization with the unchanged endpoint and cost, paid by the
true retained current-denominator capacity rather than an advanced Path. -/
theorem runs_native_linear_capacity (sh : Shape) (rows ell p : ℕ)
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
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)))
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current ≤ CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target payload)
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      (contracted (current-target) f) (v.append frame) leaf
    HoareTime (program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage payload) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=(CompactComplexSourceReadyOrientation.output call w (contracted (current-target) f)).append scratch)
      (constant c*volume rows sh ell p) := by
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
  have hsrc := CompactComplexSourceReadyNonleafFinalPorts.source sh rows ell p rho left count slots right src dst
    (contracted (current-target) f) (v.append frame) leaf
  have hsave := CompactComplexSourceReadyNonleafFinalPorts.saved sh rows ell p rho left count slots right src dst target
    (contracted (current-target) f) control queue scalar old tail storage ret frame leaf pcStack
  have hsaved : Placement.active (FiniteReturnStackAt.placement (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)) w=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [FiniteReturnStackAt.active_bank]
    change FiniteReturnStack.bank (w.tape _) (w.head _)=_
    rw [hsave.1,hsave.2]
    exact hstack
  have hpost := CompactComplexSourceReadyOrientationInvariants.runs_linear
    (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack) call w older origin hsaved sh rows ell p hr
    (contracted (current-target) f) (CompactComplexSourceReadyNonleafFinalGeometry.contracted_width _ f hw) hsrc.1 hsrc.2
  have hpostFull := CompactComplexSourceReadyOrientedControls.widen_runs hpost scratch
  have hseq := hfull.seq hpostFull
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact hseq.consequence (fun _ h => h) (fun _ h => h) (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactNativeRoleRecombine (recombine)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyNonleafFinalPath.program
  CompactComplexSourceReadyNonleafOrientedFinal.program

/-- Actual finalization with the unchanged endpoint and cost, paid by the
true retained current-denominator capacity rather than an advanced Path. -/
theorem oriented_runs_native_linear_capacity (sh : Shape) (rows ell p : ℕ)
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
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)))
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (currentCapacity : current ≤ CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1) :
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
      (fun z => z=(CompactComplexSourceReadyOrientation.output call w joined).append scratch)
      (CompactComplexSourceReadyNonleafOrientedFinal.constant c*volume rows sh ell p) := by
  have h := CompactComplexSourceReadyNonleafOrientedFinal.runs_native_linear_capacity sh rows ell p
    hc hr hd hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage (payload data)
    (recombine sh rows c ell hd data) (CompactNativeRoleRecombine.width sh rows c ell _ hd data hw)
    current target hle hcurrent htarget (payload_source data) (payload_roles sh rows ell hd data)
    frame leaf pcStack call older origin hstack scratch currentCapacity
  simp_rw [CompactNativeRoleRecombine.role_recombine] at h
  rw [contracted_recombine] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexSourceReadySinkCorrections (data)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] seq HoareTime roleCount
  CompactComplexSourceReadySinkCorrections.program
  CompactComplexSourceReadyNonleafOrientedFinal.program

/-- Actual finalization with the unchanged endpoint and cost, paid by the
true retained current-denominator capacity rather than an advanced Path. -/
theorem compose_runs_capacity (v : Stage sh) (rows ell p : ℕ)
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
    HoareTime (program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=(CompactComplexSourceReadyOrientation.output call w joined).append scratch)
      ((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  have hsink := CompactComplexSourceReadySinkCorrections.compose_runs v rows ell p
    hslots hG hA hGK hpay hgroup control queue scalar tail storage (fun _ => blank) 0 before
    hw (frame.append (SharedBank.empty 7 2)) leaf scratch hblank
  rw [payload_family v hslots ell p before] at hsink
  have hfinal := CompactComplexSourceReadyCorrectedRoleRejoin.oriented_runs_native_linear_capacity sh rows ell p
    (by unfold roleCount; omega) hr hd hgroup hG hA (by omega) hP
    v.rho v.left v.f v.slots v.right v.source.val v.target.val
    control queue scalar tail storage (family v hslots ell p before)
    (family_width v hslots ell p (CompactNativeRoleHeaders.recordWidth sh p) before hw)
    current target hle hcurrent htarget frame leaf
    pcStack call older origin hstack scratch currentCapacity
  dsimp only [program]
  exact ProgramPairSequence.runs
    (CompactComplexSourceReadySinkCorrections.program (s:=s))
    (CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roleCount) pcStack) hsink hfinal

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal
