module

public import IntegerMultBounds.Machine.CompactComplexUniformRootConstant
public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedRootRun

/-! The same actual positive and exponent-zero stopped-root traces have the
original uniform stage-factor bound with a fixed physical machine coefficient. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexUniformStoppedRootExecution
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

open CompactComplexAlignedStoppedRootRun (lifted)
open CompactComplexUniformRootConstant (constant)
open CompactComplexUniformRuntimeCoefficient (stageFactor)

/-- The same actual stopped root trace and emitted result retain every
physical transition with the original uniform stage-factor runtime. -/
theorem positive_root_halts (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
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
      (elapsedSteps : ℝ)≤constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision : ℝ)*stageFactor shape (childExponent+1) ∧
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank (CompactSpectatorLeafAxis.word result)
          (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))) scalar suffix) elapsedSteps := by
  obtain ⟨elapsedSteps,actualBound,actualRun⟩ := CompactComplexAlignedStoppedRootRun.positive_root_halts
      basisProgram headerStack pcStack liveStack shape
      rows polynomialExponent precision chunkIndex dependency right sourceRole targetRole liveDenominator inputBank scalar suffix
      stackEmpty guardReady dimensionReady rootStopped sourceArray guardPositive axesPositive rowsPositive metadataFits
      sourceWidth rawHeaders publicSourceReady liveReady targetBlank exponentWord exponentHead scalarRowLimit basePrecision usedRows
      unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  have costEquation := CompactComplexUniformStoppedRootBudget.aligned_cost_eq
    shape rows polynomialExponent precision (childExponent+1)
  have actualCostBound := actualBound.trans_eq costEquation
  have uniformBound := CompactComplexUniformStoppedRootBudget.cost_uniform rows polynomialExponent precision
    chunkIndex dependency rowsPositive guardPositive axesPositive rootStopped
  have actualUniformBound := (Nat.cast_le (α:=ℝ).mpr actualCostBound).trans uniformBound
  have commonBound := CompactComplexUniformRootConstant.stopped_bound packingLimit shape (childExponent+1)
    (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision)
  exact ⟨elapsedSteps,actualBound,actualUniformBound.trans commonBound,actualRun⟩

/-- The same actual stopped root trace and emitted result retain every
physical transition with the original uniform stage-factor runtime. -/
theorem scalar_root_halts (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
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
      (elapsedSteps : ℝ)≤constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision : ℝ)*stageFactor shape (0) ∧
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank (CompactSpectatorLeafAxis.word result)
          (CompactComplexDenominatorPolicy.leafTarget liveDenominator 0)) scalar suffix) elapsedSteps := by
  obtain ⟨elapsedSteps,actualBound,actualRun⟩ := CompactComplexAlignedStoppedRootRun.scalar_root_halts
      basisProgram headerStack pcStack liveStack shape
      rows polynomialExponent precision chunkIndex dependency right sourceRole targetRole liveDenominator inputBank scalar suffix
      stackEmpty guardReady dimensionReady rootStopped sourceArray guardPositive axesPositive rowsPositive metadataFits
      sourceWidth rawHeaders publicSourceReady liveReady targetBlank exponentWord exponentHead scalarRowLimit basePrecision usedRows
      unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  have costEquation := CompactComplexUniformStoppedRootBudget.aligned_cost_eq
    shape rows polynomialExponent precision (0)
  simp only [pow_zero,Nat.mul_one] at costEquation
  have actualCostBound := actualBound.trans_eq costEquation
  have uniformBound := CompactComplexUniformStoppedRootBudget.cost_uniform rows polynomialExponent precision
    chunkIndex dependency rowsPositive guardPositive axesPositive rootStopped
  have actualUniformBound := (Nat.cast_le (α:=ℝ).mpr actualCostBound).trans uniformBound
  have commonBound := CompactComplexUniformRootConstant.stopped_bound packingLimit shape (0)
    (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision)
  exact ⟨elapsedSteps,actualBound,actualUniformBound.trans commonBound,actualRun⟩

end
end IntegerMultBounds.Machine.CompactComplexUniformStoppedRootExecution
