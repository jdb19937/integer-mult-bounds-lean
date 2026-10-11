module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedClassifierTablePath
public import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedClassifierTensor

/-! Width-only classifier execution combines with any genuinely guarded input
grid, including the parent's actual scalar prefix. No recursive-bound
replacement of the input grid is needed. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexCorrectedStoppedClassifierGuarded
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyOrientationInvariants (savedSlot oriented)
open CompactComplexSourceReadyOrientedControlsFrame (output)
open CompactComplexCorrectedStoppedClassifierTensor (classifier_source)
open CompactComplexSourceReadyCorrectedActualTable (savedStackSlot)
open CompactComplexSourceReadyCorrectedSavedReturnPath (path)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ}
local notation "RC" => CompactComplexSourceReadyScalarWorkspace.roles
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

private theorem numeric_ne (i : Fin 43) :
    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric (s:=10+s) (c:=RC) i)≠
      CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem control_ne (i : Fin 43) :
    CompactComplexNonleafRoleChildBank.control (s:=s) (c:=RC) i≠
      CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNonleafRoleChildBank.control,
    Fin.val_mk,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem storage_ne (i : Fin (10+s)) :
    CompactComplexNonleafRoleChildBank.storage (c:=RC) i≠
      CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem output_headers {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (publicTapes s RC) 2) (f : Fin N → ButterflyStreamData.Coefficient) :
    Placement.active headerPlacement (base (output call v f))=
      Placement.active headerPlacement (base v) := by
  have hslot (i : Fin 43) : headerPlacement (s:=10+s) (c:=RC)
      (Fin.castAdd (CompactComplexNonleafRoleEntry.tapes (10+s) RC-43) i)=
      CompactComplexNonleafRoleEntry.numeric i := by
    unfold headerPlacement
    exact InjectivePlacement.active_slot _ _ _ _
  apply congrArg₂ Tapes.mk <;> funext i
  · change (output call v f).head (Fin.castAdd 7 (headerPlacement (Fin.castAdd _ i)))=_
    rw [hslot]
    exact (CompactComplexSourceReadyOrientedControlsFrame.frame call v f _ (numeric_ne i)).1
  · change (output call v f).tape (Fin.castAdd 7 (headerPlacement (Fin.castAdd _ i)))=_
    rw [hslot]
    exact (CompactComplexSourceReadyOrientedControlsFrame.frame call v f _ (numeric_ne i)).2

private theorem ready_output {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (publicTapes s RC) 2) (f : Fin N → ButterflyStreamData.Coefficient) :
    CompactComplexSourceReadyOrientation.output call (ready v) f=ready (output call v f) := by
  simpa only [ready,CompactComplexSourceReadyLeafPhase.ready,CompactComplexSourceReadyWorkspace.bank]
    using CompactComplexSourceReadyOrientedControlsFrame.node_output call v
      (SharedBank.empty _ 2) (SharedBank.empty _ 2) f

/-- Actual tag0 classifier, stopped leaf, and saved-call pop jointly return
the original forward/inverse tensor, including the physical output source. -/
theorem classifier_return_guarded (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k levels frames count : ℕ} (dependency : Path sh.active left (k+1) levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s RC) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready v)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (f : Array sh rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : Width sh rows ell (p-2*sh.bits) f)
    (M : ℕ) (hg : Grid sh rows ell (p-2*sh.bits) n M f)
    (hguard : 4*(M*4^(arity^(k+1)))<2^(CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)))
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows)
    (hblankTail : ∀ z,origin≤z → older z=blank)
    (hactive : sh.active≤sh.axes)
    (hready : CompactComplexSourceReadyGuard.Ready v)
    (hdimension : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstop : ComplexRecursiveCallSchema.stopped sh.axes (k+1)=true)
    (hroles : CompactComplexNonleafChildAddress.roles∣rows) :

    let pre := output call v f
    let child := CompactComplexCorrectedStoppedChildGridSemantics.installed call rows ell
      (p-2*sh.bits) rho dependency.visit (oriented call f)
    let endpoint := setTape
      ((ready (CompactComplexSourceReadyStoppedLeafCount.returned pre
        (CompactSpectatorLeafAxis.word child) (CompactComplexDenominatorPolicy.leafTarget n (k+1)))).append scalar)
      (savedStackSlot pcStack) older origin
    let port := Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientation.source (s:=s) (c:=RC))
    ∃ t≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
          CompactComplexSourceReadyOrientationInvariants.constant+1)*
          CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1+
          (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)),
      path headerStack pcStack liveStack
        (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 0)
        ((ready v).append scalar) t (CompactComplexScheduledPCDecode.savedPC call) endpoint ∧
      endpoint.tape port=CompactSpectatorLeafAxis.word child ∧ endpoint.head port=0 ∧
      Grid sh rows ell (p-2*sh.bits) (n+arity^(k+1))
        (M*4^(arity^(k+1))) child ∧
      ∀ i,decoded sh rows ell (p-2*sh.bits) (n+arity^(k+1)) child i=
        CompactComplexCorrectedChildGridSemantics.tensor call
          (fun wire address => decoded sh rows ell (p-2*sh.bits) n f
            (CompactComplexNonleafChildAddress.inputIndex sh rows ell hroles rho dependency.visit i wire address))
          (CompactComplexNonleafChildAddress.outputWire sh rows ell hroles i)
          (CompactComplexNonleafChildAddress.outputAddress sh rows ell hroles rho dependency.visit i) := by
  let pre := output call v f
  have hs := classifier_source call v f hsource.2 hsource.1
  have hsaved := CompactComplexSourceReadyOrientationInvariants.retained_savedSlot pcStack call (ready v) f
  rw [ready_output] at hsaved
  have hstack' : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready pre)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) :=
    hsaved.trans hstack
  have hwidth : CompactNativeRoleHeaders.recordWidth sh p=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  have hw' := CompactComplexSourceReadyOrientationInvariants.oriented_width call sh rows ell
    (p-2*sh.bits) f hw
  have hphysical : ∀ i,((oriented call f) i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      ((oriented call f) i).2.length=CompactNativeRoleHeaders.recordWidth sh p := by
    intro i
    rw [hwidth]
    exact hw' i
  have hraw' := (output_headers call v f).trans hraw
  have hcurrent := CompactComplexSourceReadyOrientedControlsFrame.frame call v f
    CompactComplexNonleafRoleChildBank.current (storage_ne _)
  have htargetFrame := CompactComplexSourceReadyOrientedControlsFrame.frame call v f
    CompactComplexNonleafRoleChildBank.target (storage_ne _)
  have hcontrol := CompactComplexSourceReadyOrientedControlsFrame.frame call v f
    (CompactComplexNonleafRoleChildBank.control 1) (control_ne 1)
  obtain ⟨t₁,ht₁,hpath₁⟩ := CompactComplexSourceReadyCorrectedClassifierTablePath.child_path_width
    headerStack pcStack liveStack call v (SharedBank.empty _ 2) (SharedBank.empty _ 2) scalar
    older origin hstack dependency hr hG hA hactive f hw
    hsource.2 hsource.1 hready hdimension ⟨hexponentHead,hexponent⟩
  have hpEq : ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)=p := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  rw [hpEq] at ht₁
  rw [hstop,ite_eq_left rfl] at hpath₁
  obtain ⟨t₂,ht₂,hpath₂⟩ := CompactComplexSourceReadyCorrectedStoppedReturnPath.return_path
    headerStack pcStack liveStack call sh rows ell p rho dependency right src dst n pre scalar older origin
    hstack' (oriented call f) hG hA hr hp hphysical hraw' hs
    ⟨hcurrent.1.trans hlive.1,hcurrent.2.trans hlive.2⟩
    ⟨htargetFrame.1.trans htarget.1,htargetFrame.2.trans htarget.2⟩
    (hcontrol.2.trans hexponent) (hcontrol.1.trans hexponentHead)
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound hblankTail
  have hsem := CompactComplexCorrectedStoppedChildGridSemantics.installed_tensor call rows ell
    (p-2*sh.bits) n _ rho dependency.visit f (oriented call f) rfl hw hg hguard hroles
  have hphysicalSource := CompactComplexCorrectedStoppedChildGridSemantics.restored_installed_source
    pcStack call rows ell (p-2*sh.bits) rho dependency.visit (oriented call f) pre scalar
    (CompactComplexDenominatorPolicy.leafTarget n (k+1)) older origin
  refine ⟨t₁+t₂,Nat.add_le_add ht₁ ht₂,?_,hphysicalSource.1,hphysicalSource.2,hsem⟩
  dsimp only [CompactComplexSourceReadyCorrectedSavedReturnPath.path,
    CompactComplexSourceReadyCorrectedFinalTablePath.path,CompactComplexFixedNodePaths.nodePath]
    at hpath₁ hpath₂ ⊢
  exact FiniteFlowPath.append hpath₁ hpath₂

end
end IntegerMultBounds.Machine.CompactComplexCorrectedStoppedClassifierGuarded
