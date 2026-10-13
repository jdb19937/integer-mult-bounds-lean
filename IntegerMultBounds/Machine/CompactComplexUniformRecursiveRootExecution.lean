module

public import IntegerMultBounds.Machine.CompactComplexUniformRuntimeCoefficient
public import IntegerMultBounds.Machine.CompactComplexAlignedNonleafClassifierPrefix
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary

/-! One coefficient selected before every shape, depth, input and history
bounds the same literal halted root trace and exact corrected tensor output.
Stopped-root integration and the final named milestone interface are separate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexUniformRecursiveRootExecution
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyReachedDormantFrameInvariant (protectedSlots)
open CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction (PackingFamily)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexAlignedReachedNodeEntryPath (originalBank entryCost)
open CompactComplexAlignedReachedFinalReturn (rootEndpoint rootFinalCost)
open CompactComplexAlignedBoundaryPaths (alignedBank)
open CompactComplexSourceReadyCompletedChildBoundary (joined)
open CompactSpectatorInheritedGrid (half decoded Grid Width)
open CompactSpectatorVisitGeometry (Array)
open CompactGlobalRowPadding (rowsAt)
open CompactRecursiveDependencyBudget (Path)
open RecursiveInterchangeRows (pack)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget
  CompactComplexSourceReadyGuard.guardConstant
  CompactComplexSourceReadyNonleafTargetSplit.constant
  NativeEndpointCharacterCanonicalRoles.constant NativeUniformPolynomialRotationRoles.constant
  CompactComplexEndpointRoleExchange.constant CompactComplexSourceReadyNonleafFinalPath.constant
open CompactComplexSourceReadyRecursiveRootExecution (rootBoundaryCoefficient)
variable {stackCount basisStateCount : ℕ} {shape : Shape}


/-- The complete runtime coefficient depends only on the fixed packing limit,
not on node geometry, inputs, exponents, banks or saved-call histories. -/
def constant (packingLimit : ℕ) : ℝ :=
  CompactComplexUniformRuntimeCoefficient.machineConstant
    (CompactComplexActualProviderRuntime.uniformBasisConstant packingLimit)

theorem constant_positive (packingLimit : ℕ) : 0<constant packingLimit :=
  CompactComplexUniformRuntimeCoefficient.machine_constant_positive _
    (CompactComplexActualProviderRuntime.uniform_basis_constant_positive packingLimit).le

/-- The same literal nonstopped root halts with exact original tensor output
and the uniform stage-factor bound using the fixed coefficient above. -/
theorem root_runs
    (phaseCoordinate : Fin shape.chunk) (activeFits : shape.active≤shape.axes)
    (pair : BinaryRowProgram.Op (Fin arity))
    (polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (largeAxes : arity^1000<shape.axes) (activePositive : 0<shape.active)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) (unitPayload : shape.payload=1)
    (packingFamily : PackingFamily phaseCoordinate activeFits pair polynomialExponent inputPrecision packingLimit
      guardPositive guardFitsChunk)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+guardBits≤shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤shape.chunk)
    (precisionReserve : baselinePrecision+2*shape.bits≤ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive≤baselinePrecision) (baselineFitsPrecision : baselinePrecision ≤ inputPrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume entryReturned rowCount : ℕ}
    (entryPath : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels)
    (nodeNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+2)=false)
    (initialLive : ℕ) (originalCoefficients : Array shape rowCount polynomialExponent)
    (inputWidth : Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (inputGrid : Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))
      originalCoefficients)
    (controlBank : Tapes 43 2) (queueBank : Tapes 1 2) (scalarHeaders : ActiveRepairRankHeadersCommands.State)
    (tailBank : Tapes 22 2) (originalStorage : Tapes (10+stackCount) 2) (auxiliaryBank : Tapes 2 2)
    (countBlank : originalStorage.head ⟨0,by omega⟩=0 ∧ originalStorage.tape ⟨0,by omega⟩=(fun _ => blank))
    (currentReady : originalStorage.head ⟨7,by omega⟩=1 ∧ originalStorage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits initialLive))
    (targetBlank : originalStorage.head ⟨8,by omega⟩=0 ∧ originalStorage.tape ⟨8,by omega⟩=(fun _ => blank))
    (clockBlank : auxiliaryBank.head 1=0 ∧ auxiliaryBank.tape 1=(fun _ => blank))
    (auxiliaryFree : CompactComplexSourceReadyPrefixReadiness.BlankAfter auxiliaryBank 0)
    (exponentReady : controlBank.head 1=1 ∧ controlBank.tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (childExponent+2)))
    (control28Blank : controlBank.head 28=0 ∧ controlBank.tape 28=(fun _ => blank))
    (control29Blank : controlBank.head 29=0 ∧ controlBank.tape 29=(fun _ => blank))
    (initialLedger : initialLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (stackOrigin : ℤ)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin []
      (originalStorage.tape (Fin.natAdd 10 pcStack)) (originalStorage.head (Fin.natAdd 10 pcStack)))
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (originalProtectedTails : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,originalStorage.head storagePort≤cell → originalStorage.tape storagePort cell=blank) :
    let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsPositive : 0<rowCount/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
    let stageSlots : stage.slots=25^3 := rfl
    let stagePacked := packingFamily entryPath rowCount rowsPadded childRowsPositive
    ∃ childPathBudget : ComplexRecursiveCallSchema.Call → ℕ,
    ∃ elapsedSteps,∃ outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2,
    ∃ outputArray : Array shape rowCount polynomialExponent,
      elapsedSteps≤(4*CompactComplexSourceReadyGuard.guardConstant+5)*
          CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision+
        entryCost shape rowCount polynomialExponent metadataPrecision+
        CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
          packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked+
        rootFinalCost (shape:=shape) rowCount polynomialExponent metadataPrecision+2 ∧
      (elapsedSteps : ℝ)≤constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision : ℝ)*
        CompactComplexUniformRuntimeCoefficient.stageFactor shape (childExponent+1) ∧
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program basisProgram headerStack pcStack liveStack).2
        (fun bank => bank=originalBank stage rowCount polynomialExponent metadataPrecision originalCoefficients
          controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank)
        (fun bank => bank=alignedBank (outputBank.append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) elapsedSteps ∧
      outputBank.tape CompactComplexSourceReadyOrientation.source=CompactSpectatorLeafAxis.word outputArray ∧
      outputBank.head CompactComplexSourceReadyOrientation.source=0 ∧
      (∀ index,(outputArray index).1.length=half shape inputPrecision+1 ∧
        (outputArray index).2.length=half shape inputPrecision+1) ∧
      Grid shape rowCount polynomialExponent inputPrecision
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)*
          4^(2*arity^(childExponent+2))) outputArray ∧
      ∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
        decoded shape rowCount polynomialExponent inputPrecision
          (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) outputArray
          (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
        ComplexEndpoints.fullFrame (arity^(childExponent+1))
          (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
            (pack rawRow (FlatCoordinateLayout.index
              (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex)))
          (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor) := by
  obtain ⟨runtimeConstant,constantPositive,fixedConstantEq,childPathBudget,elapsedSteps,outputBank,outputArray,
    naturalBound,runtimeBound,rootRun,outputSource,outputHead,outputWidth,outputGrid,outputTensor⟩ :=
    CompactComplexSourceReadyRecursiveRootExecution.exists_root_execution_with_runtime
      phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision
      growthConstant baselineLive packingLimit guardPositive guardFitsChunk basisProgram headerStack pcStack liveStack basisConstant
      basisRuns largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom
      precisionReserve baselineFits baselineFitsPrecision growthReserve denominatorRoom childExponent entryPath rowsPadded
      nodeNonstopped initialLive originalCoefficients inputWidth inputGrid controlBank queueBank scalarHeaders tailBank originalStorage
      auxiliaryBank countBlank currentReady targetBlank clockBlank auxiliaryFree exponentReady control28Blank control29Blank
      initialLedger stackOrigin savedAssociated pcHeaderDistinct pcLiveDistinct headerLiveDistinct originalProtectedTails
  have uniformBound := CompactComplexUniformRuntimeCoefficient.root_runtime_coefficient_bound
    runtimeConstant constantPositive.le shape axesPositive guardPositive childExponent
    (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent
      (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)) nodeNonstopped
  have actualUniformBound := runtimeBound.trans uniformBound
  rw [fixedConstantEq] at actualUniformBound
  exact ⟨childPathBudget,elapsedSteps,outputBank,outputArray,naturalBound,actualUniformBound,rootRun,
    outputSource,outputHead,outputWidth,outputGrid,outputTensor⟩

end
end IntegerMultBounds.Machine.CompactComplexUniformRecursiveRootExecution
