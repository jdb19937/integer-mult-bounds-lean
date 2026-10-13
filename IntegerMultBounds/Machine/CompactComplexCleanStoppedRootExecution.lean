module

public import IntegerMultBounds.Machine.CompactComplexUniformStoppedRootExecution
public import IntegerMultBounds.Machine.CompactComplexStoppedRootWorkspaceClean
public import IntegerMultBounds.Machine.CompactComplexAlignedRootWorkspaceClean
public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedRootRun

/-! The same actual uniformly bounded stopped-root halting traces retain
explicit full node-workspace cleanliness. The original-source bank constructor
derives their input cleanliness, without a supplied cleanup execution. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexCleanStoppedRootExecution
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

open CompactComplexRootWorkspaceClean (Clean)
open CompactComplexStoppedRootWorkspaceClean (PublicClean)

/-- With the original blank scalar and basis suffixes, the actual stopped
endpoint is exactly the aligned bank whose scalar/basis cleanup is already
proved. The binary role/frame/leaf/work certificate applies to this bank. -/
theorem canonical_endpoint_eq (inputBank : Tapes (publicTapes stackCount roleCount) 2) :
    lifted inputBank (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
      (SharedBank.empty (localTapes roleCount) prime)=
    CompactComplexAlignedBoundaryPaths.alignedBank
      ((ready inputBank).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)) := rfl

/-- The actual halted stopped root retains its emitted word, installed
denominator, fixed uniform runtime and explicit node-workspace cleanup. -/
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
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows)
    (publicClean : PublicClean inputBank) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray
    ∃ elapsedSteps≤CompactComplexSourceReadyGuard.setupCost shape.axes (childExponent+1)+
        CompactComplexSourceReadyGuard.cleanupCost shape.axes (childExponent+1)+8+
        (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
          CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision*(arity^(childExponent+1))+3,
      (elapsedSteps : ℝ)≤constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision : ℝ)*stageFactor shape (childExponent+1) ∧
      Clean (ready (returned inputBank (CompactSpectatorLeafAxis.word result)
        (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1)))) ∧
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank (CompactSpectatorLeafAxis.word result)
          (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))) scalar suffix) elapsedSteps := by
  dsimp only
  obtain ⟨elapsedSteps,naturalBound,uniformBound,actualRun⟩ :=
    CompactComplexUniformStoppedRootExecution.positive_root_halts
      packingLimit basisProgram headerStack pcStack liveStack shape
      rows polynomialExponent precision chunkIndex dependency right sourceRole targetRole liveDenominator inputBank scalar suffix
      stackEmpty guardReady dimensionReady rootStopped sourceArray guardPositive axesPositive rowsPositive metadataFits
      sourceWidth rawHeaders publicSourceReady liveReady targetBlank exponentWord exponentHead scalarRowLimit basePrecision usedRows
      unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  have outputClean := CompactComplexStoppedRootWorkspaceClean.returned_clean inputBank publicClean
    (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray))
    (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))
  exact ⟨elapsedSteps,naturalBound,uniformBound,outputClean,actualRun⟩

/-- The actual halted stopped root retains its emitted word, installed
denominator, fixed uniform runtime and explicit node-workspace cleanup. -/
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
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows)
    (publicClean : PublicClean inputBank) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray
    ∃ elapsedSteps≤CompactComplexSourceReadyGuard.setupCost shape.axes 0+
        CompactComplexSourceReadyGuard.cleanupCost shape.axes 0+8+
        (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
          CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision+3,
      (elapsedSteps : ℝ)≤constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision : ℝ)*stageFactor shape (0) ∧
      Clean (ready (returned inputBank (CompactSpectatorLeafAxis.word result)
        (CompactComplexDenominatorPolicy.leafTarget liveDenominator (0)))) ∧
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=lifted inputBank scalar suffix)
        (fun bank => bank=lifted (returned inputBank (CompactSpectatorLeafAxis.word result)
          (CompactComplexDenominatorPolicy.leafTarget liveDenominator 0)) scalar suffix) elapsedSteps := by
  dsimp only
  obtain ⟨elapsedSteps,naturalBound,uniformBound,actualRun⟩ :=
    CompactComplexUniformStoppedRootExecution.scalar_root_halts
      packingLimit basisProgram headerStack pcStack liveStack shape
      rows polynomialExponent precision chunkIndex dependency right sourceRole targetRole liveDenominator inputBank scalar suffix
      stackEmpty guardReady dimensionReady rootStopped sourceArray guardPositive axesPositive rowsPositive metadataFits
      sourceWidth rawHeaders publicSourceReady liveReady targetBlank exponentWord exponentHead scalarRowLimit basePrecision usedRows
      unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  have outputClean := CompactComplexStoppedRootWorkspaceClean.returned_clean inputBank publicClean
    (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray))
    (CompactComplexDenominatorPolicy.leafTarget liveDenominator (0))
  exact ⟨elapsedSteps,naturalBound,uniformBound,outputClean,actualRun⟩

end
end IntegerMultBounds.Machine.CompactComplexCleanStoppedRootExecution
