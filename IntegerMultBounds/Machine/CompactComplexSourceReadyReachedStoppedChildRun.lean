import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedClassifierTensor
import IntegerMultBounds.Machine.CompactComplexSourceReadySavedCallHistory

/-! A reached semantic call stack supplies the true top call and older bank.
The actual classifier, stopped tensor leaf and corrected decoded return then
reach the saved continuation with the older call list physically restored;
no occupied-word, pre-orientation or blank-tail premise is supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedChildRun
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

theorem stopped_child_return (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k levels frames count : ℕ} (dependency : Path sh.active left (k+1) levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s RC) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (origin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (hReached : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin (call::calls)
      ((ready v).append scalar))
    (f : Array sh rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : Width sh rows ell (p-2*sh.bits) f)
    (basePrecision C : ℕ) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hg : Grid sh rows ell (p-2*sh.bits) n
      (CompactRecursiveGridBudget.bound basePrecision C levels (frames+2*count)) f)
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
    (R usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows)
    (hactive : sh.active≤sh.axes)
    (hready : CompactComplexSourceReadyGuard.Ready v)
    (hdimension : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstop : ComplexRecursiveCallSchema.stopped sh.axes (k+1)=true)
    (hroles : CompactComplexNonleafChildAddress.roles∣rows) :

    let pre := output call v f
    let child := CompactComplexCorrectedStoppedChildGridSemantics.installed call rows ell
      (p-2*sh.bits) rho dependency.visit (oriented call f)
    ∃ older top,
    let endpoint := setTape
      ((ready (CompactComplexSourceReadyStoppedLeafCount.returned pre
        (CompactSpectatorLeafAxis.word child) (CompactComplexDenominatorPolicy.leafTarget n (k+1)))).append scalar)
      (savedStackSlot pcStack) older top
    let port := Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientation.source (s:=s) (c:=RC))
    CompactComplexSourceReadySavedCallHistory.Associated origin calls older top ∧
    (    ∃ t≤(CompactComplexSourceReadyOrientationInvariants.constant+
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
        (CompactRecursiveGridBudget.bound basePrecision C levels (frames+2*count)*4^(arity^(k+1))) child ∧
      ∀ i,decoded sh rows ell (p-2*sh.bits) (n+arity^(k+1)) child i=
        CompactComplexCorrectedChildGridSemantics.tensor call
          (fun wire address => decoded sh rows ell (p-2*sh.bits) n f
            (CompactComplexNonleafChildAddress.inputIndex sh rows ell hroles rho dependency.visit i wire address))
          (CompactComplexNonleafChildAddress.outputWire sh rows ell hroles i)
          (CompactComplexNonleafChildAddress.outputAddress sh rows ell hroles rho dependency.visit i)) ∧
    CompactComplexSourceReadySavedCallHistory.Reached pcStack origin calls endpoint ∧
    CompactComplexSavedStackTailInvariant.Invariant (savedStackSlot pcStack) endpoint := by
  dsimp only
  have hs := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack v scalar
  have hPublic := hReached
  unfold CompactComplexSourceReadySavedCallHistory.Reached at hPublic
  rw [hs.1,hs.2] at hPublic
  obtain ⟨older,top,hOlder,hBlank,ht,hh⟩ := CompactComplexSourceReadySavedCallHistory.top hPublic
  have hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready v)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (top+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [FiniteReturnStackAt.active_bank]
    simp only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,Fin.addCases_left]
    exact congrArg₂ FiniteReturnStack.bank ht hh
  have hr := CompactComplexCorrectedStoppedClassifierTensor.classifier_return_tensor
    headerStack pcStack liveStack call sh rows ell p rho dependency right src dst n v scalar
    older top hstack f hG hA hr hp hw basePrecision C hchunk hg hraw hsource hlive htarget
    hexponent hexponentHead R usedRows hpay hright hsrc hdst hb hu hroom hliveBound hBlank
    hactive hready hdimension hstop hroles
  dsimp only at hr
  refine ⟨older,top,hOlder,hr,?_,?_⟩
  · simpa only [CompactComplexSourceReadySavedCallHistory.Reached,setTape,Function.update_self] using hOlder
  · simpa only [CompactComplexSavedStackTailInvariant.Invariant,setTape,Function.update_self] using
      CompactComplexSavedStackTailInvariant.history_tail
        (CompactComplexSourceReadySavedCallHistory.physical hOlder)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedChildRun
