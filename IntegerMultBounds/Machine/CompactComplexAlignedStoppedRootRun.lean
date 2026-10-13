module

public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedChildRun
public import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedRoot
public import IntegerMultBounds.Machine.CompactComplexFixedNodeRootExit

/-! Actual stopped roots execute the classifier, forward leaf, identity
post-orientation and empty-stack halt on the unchanged prime-alphabet table. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedStoppedRootRun
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyWorkspace (bank leafTapes)
open CompactComplexSourceReadyOrientationInvariants (savedSlot oriented)
open CompactComplexSourceReadyOrientedControlsFrame (output)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexActualCallFullAlignment (localTapes)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
open CompactComplexSourceReadyStoppedLeafCount (returned)
variable {stackCount basisStateCount : ℕ}
local notation "roleCount" => CompactComplexSourceReadyScalarWorkspace.roles
open CompactComplexFixedNodeTable
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
  CompactComplexFixedNodeTable.returnDestination CompactComplexFixedNodeTable.eventDestination

def lifted (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime) :=
  (Alphabet.mapTapes encoding ((ready inputBank).append scalar)).append suffix

private theorem returned_empty (pcStack : Fin stackCount)
    (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime) (outputWord : ℤ → Fin 6) (outputLive : ℕ)
    (stackEmpty : (ready inputBank).tape (savedSlot pcStack)
      ((ready inputBank).head (savedSlot pcStack)-1)=blank) :
    (lifted (returned inputBank outputWord outputLive) scalar suffix).tape
      (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
      ((lifted (returned inputBank outputWord outputLive) scalar suffix).head
        (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)-1)=blank := by
  have retained := CompactComplexSourceReadyOrientedControlsStopped.returned_saved pcStack inputBank outputWord outputLive
  rw [FiniteReturnStackAt.active_bank,FiniteReturnStackAt.active_bank] at retained
  have retainedTape := congrArg (fun bank : Tapes 1 2 => bank.tape 0) retained
  have retainedHead := congrArg (fun bank : Tapes 1 2 => bank.head 0) retained
  simp only [FiniteReturnStack.bank] at retainedTape retainedHead
  simp only [lifted,CompactComplexSourceReadyAlignedActualTable.savedStackSlot,
    CompactComplexSourceReadyCorrectedActualTable.savedStackSlot_eq,Tapes.append,Fin.addCases_left,Alphabet.mapTapes]
  rw [retainedHead,retainedTape,stackEmpty]
  rfl

private theorem classifier_leaf_halts
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount)
    (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (axes nodeExponent : ℕ) (axesPositive : 0<axes)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits axes))
    (exponentReady : inputBank.head CompactComplexSourceReadyGuard.exponent=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits nodeExponent))
    (rootStopped : ComplexRecursiveCallSchema.stopped axes nodeExponent=true)
    (stackEmpty : (ready inputBank).tape (savedSlot pcStack)
      ((ready inputBank).head (savedSlot pcStack)-1)=blank)
    (outputWord : ℤ → Fin 6) (outputLive leafBudget : ℕ)
    (leafRun : HoareTime (CompactComplexSourceReadyOrientedControls.stopped (c:=roleCount) pcStack).2
      (fun bank => bank=(ready inputBank).append scalar)
      (fun bank => bank=(ready (returned inputBank outputWord outputLive)).append scalar) leafBudget) :
    ∃ elapsedSteps≤CompactComplexSourceReadyGuard.setupCost axes nodeExponent+
        CompactComplexSourceReadyGuard.cleanupCost axes nodeExponent+8+leafBudget+3,
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank outputWord outputLive) scalar suffix) elapsedSteps := by
  obtain ⟨classifierElapsed,classifierBound,classifierPath⟩ := CompactComplexAlignedStoppedChildRun.root_classifier_path
    basisProgram headerStack pcStack liveStack inputBank (SharedBank.empty leafTapes 2) (SharedBank.empty 10 2)
    scalar suffix stackEmpty axes nodeExponent axesPositive guardReady dimensionReady exponentReady
  rw [rootStopped] at classifierPath
  have leafLifted := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _ suffix leafRun
  obtain ⟨leafElapsed,leafBound,leafPath⟩ := CompactComplexFixedNodePaths.terminal_control_path
    (ht:=Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (stack:=CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (childReturn:=CompactComplexActualCallFullAlignment.childReturn basisProgram headerStack liveStack)
    (controls:=CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (event:=CompactComplexSourceReadyAlignedActualTable.event basisProgram headerStack pcStack liveStack)
    (isStopped:=CompactComplexSourceReadyAlignedActualTable.classify pcStack)
    1 (Or.inl rfl) _ _ _ leafLifted
  have completePath := FiniteFlowPath.append classifierPath leafPath
  have halts := CompactComplexFixedNodeRootExit.path_halts
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn basisProgram headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event basisProgram headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) _ _ _ completePath
    (returned_empty pcStack inputBank scalar suffix outputWord outputLive stackEmpty)
  exact ⟨classifierElapsed+leafElapsed+2,by omega,halts⟩

/-- Every physical transition of a positive stopped root, including both
empty-stack orientation branches and the final guard, is paid. The emitted
array is the actual forward leaf result, rather than an output oracle. -/
theorem positive_root_halts (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount)
    (shape : Shape) (rows polynomialExponent precision : ℕ) (chunkIndex : Fin shape.chunk)
    {childLeft childExponent levels frames count : ℕ} (dependency : Path shape.active childLeft (childExponent+1) levels frames count)
    (right sourceRole targetRole liveDenominator : ℕ) (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (stackEmpty : (ready inputBank).tape (savedSlot pcStack)
      ((ready inputBank).head (savedSlot pcStack)-1)=blank)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits shape.axes))
    (rootStopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (sourceArray : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape shape polynomialExponent precision) rows polynomialExponent)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (rowsPositive : 0<rows) (metadataFits : 2*shape.bits≤precision)
    (sourceWidth : ∀ tapeIndex,(sourceArray tapeIndex).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      (sourceArray tapeIndex).2.length=CompactNativeRoleHeaders.recordWidth shape precision)
    (rawHeaders : Placement.active headerPlacement (base inputBank)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw shape rows polynomialExponent precision chunkIndex.val childLeft (arity^childExponent) arity right sourceRole targetRole))
    (publicSourceReady : inputBank.head (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=0 ∧
      inputBank.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=CompactSpectatorLeafAxis.word sourceArray)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits liveDenominator))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (childExponent+1)))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (scalarRowLimit basePrecision usedRows : ℕ) (unitPayload : shape.payload=1)
    (rightFitsActive : right≤shape.active) (sourceRoleFits : sourceRole≤arity) (targetRoleFits : targetRole≤arity)
    (baselineFits : basePrecision≤precision-2*shape.bits) (rowsUsedBound : usedRows≤scalarRowLimit)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRowLimit≤shape.chunk)
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray
    ∃ elapsedSteps≤CompactComplexSourceReadyGuard.setupCost shape.axes (childExponent+1)+
        CompactComplexSourceReadyGuard.cleanupCost shape.axes (childExponent+1)+8+
        (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
          CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision*(arity^(childExponent+1))+3,
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank (CompactSpectatorLeafAxis.word result)
          (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))) scalar suffix) elapsedSteps := by
  dsimp only
  have leafRun := CompactComplexSourceReadyOrientedControlsStoppedRoot.positive_runs pcStack shape
    rows polynomialExponent precision chunkIndex dependency right sourceRole targetRole liveDenominator inputBank scalar stackEmpty
    sourceArray guardPositive axesPositive rowsPositive metadataFits sourceWidth rawHeaders publicSourceReady liveReady targetBlank
    exponentWord exponentHead scalarRowLimit basePrecision usedRows unitPayload rightFitsActive sourceRoleFits targetRoleFits
    baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  dsimp only at leafRun
  rw [CompactComplexSourceReadyStoppedInstalledResult.polynomial_leaf_result
    shape rows polynomialExponent precision chunkIndex dependency.visit sourceArray] at leafRun
  exact classifier_leaf_halts basisProgram headerStack pcStack liveStack inputBank scalar suffix shape.axes (childExponent+1)
    axesPositive guardReady dimensionReady ⟨exponentHead,exponentWord⟩ rootStopped stackEmpty _ _ _ leafRun

/-- The exponent-zero root uses the original scalar leaf branch and the
same literal classifier, emitted result and paid empty-stack halt. -/
theorem scalar_root_halts (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount)
    (shape : Shape) (rows polynomialExponent precision : ℕ) (chunkIndex : Fin shape.chunk)
    {childLeft levels frames count : ℕ} (dependency : Path shape.active childLeft 0 levels frames count)
    (right sourceRole targetRole liveDenominator : ℕ) (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (stackEmpty : (ready inputBank).tape (savedSlot pcStack)
      ((ready inputBank).head (savedSlot pcStack)-1)=blank)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits shape.axes))
    (rootStopped : ComplexRecursiveCallSchema.stopped shape.axes 0=true)
    (sourceArray : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape shape polynomialExponent precision) rows polynomialExponent)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (rowsPositive : 0<rows) (metadataFits : 2*shape.bits≤precision)
    (sourceWidth : ∀ tapeIndex,(sourceArray tapeIndex).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      (sourceArray tapeIndex).2.length=CompactNativeRoleHeaders.recordWidth shape precision)
    (rawHeaders : Placement.active headerPlacement (base inputBank)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw shape rows polynomialExponent precision chunkIndex.val childLeft 1 arity right sourceRole targetRole))
    (publicSourceReady : inputBank.head (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=0 ∧
      inputBank.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=CompactSpectatorLeafAxis.word sourceArray)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits liveDenominator))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (scalarRowLimit basePrecision usedRows : ℕ) (unitPayload : shape.payload=1)
    (rightFitsActive : right≤shape.active) (sourceRoleFits : sourceRole≤arity) (targetRoleFits : targetRole≤arity)
    (baselineFits : basePrecision≤precision-2*shape.bits) (rowsUsedBound : usedRows≤scalarRowLimit)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRowLimit≤shape.chunk)
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray
    ∃ elapsedSteps≤CompactComplexSourceReadyGuard.setupCost shape.axes 0+
        CompactComplexSourceReadyGuard.cleanupCost shape.axes 0+8+
        (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
          CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision+3,
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank (CompactSpectatorLeafAxis.word result)
          (CompactComplexDenominatorPolicy.leafTarget liveDenominator 0)) scalar suffix) elapsedSteps := by
  dsimp only
  have leafRun := CompactComplexSourceReadyOrientedControlsStoppedRoot.scalar_runs pcStack shape
    rows polynomialExponent precision chunkIndex dependency right sourceRole targetRole liveDenominator inputBank scalar stackEmpty
    sourceArray guardPositive axesPositive rowsPositive metadataFits sourceWidth rawHeaders publicSourceReady liveReady targetBlank
    exponentWord exponentHead scalarRowLimit basePrecision usedRows unitPayload rightFitsActive sourceRoleFits targetRoleFits
    baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  dsimp only at leafRun
  rw [CompactComplexSourceReadyStoppedInstalledResult.polynomial_leaf_result
    shape rows polynomialExponent precision chunkIndex dependency.visit sourceArray] at leafRun
  simp only [pow_zero,Nat.mul_one] at leafRun
  exact classifier_leaf_halts basisProgram headerStack pcStack liveStack inputBank scalar suffix shape.axes 0
    axesPositive guardReady dimensionReady ⟨exponentHead,exponentWord⟩ rootStopped stackEmpty _ _ _ leafRun

end
end IntegerMultBounds.Machine.CompactComplexAlignedStoppedRootRun
