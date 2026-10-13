module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveNodeExecution
public import IntegerMultBounds.Machine.CompactComplexAlignedNonleafClassifierPrefix
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary

/-! The literal empty-root input executes classification, corrected entry,
the internally constructed arbitrary-depth schedule and physical root halt.
Its emitted source is the same normalized array used in tensor semantics. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveRootExecution
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
variable {stackCount basisStateCount : ℕ} {shape : Shape}


/-- The symbolic sum keeps physical machine constants opaque in conversions. -/
def rootBoundaryFactor (classifierCoefficient entryCoefficient finalCoefficient : ℕ) :=
  classifierCoefficient+entryCoefficient+finalCoefficient+2

/-- All original root classifier, entry, finalization and halt charges have
one fixed native-volume coefficient, separate from the actual event budget. -/
def rootBoundaryCoefficient := rootBoundaryFactor
  (4*CompactComplexSourceReadyGuard.guardConstant+5)
  (CompactComplexSourceReadyNonleafTargetSplit.constant roles+
    NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+2)
  (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+
    2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+
    CompactComplexSourceReadyNonleafFinalPath.constant roles+9)

private theorem entry_boundary_algebra (splitCoefficient canonicalCoefficient nativeVolume : ℕ)
    (volumePositive : 0<nativeVolume) :
    splitCoefficient*nativeVolume+1+canonicalCoefficient*nativeVolume+1 ≤
      (splitCoefficient+canonicalCoefficient+2)*nativeVolume := by
  nlinarith only [volumePositive]

private theorem root_boundary_algebra (classifierCoefficient entryCoefficient finalCoefficient
    nativeVolume entryCharge finalCharge : ℕ)
    (entryBound : entryCharge≤entryCoefficient*nativeVolume)
    (finalBound : finalCharge≤finalCoefficient*nativeVolume)
    (haltBound : 2≤2*nativeVolume) :
    classifierCoefficient*nativeVolume+entryCharge+finalCharge+2 ≤
      rootBoundaryFactor classifierCoefficient entryCoefficient finalCoefficient*nativeVolume := by
  unfold rootBoundaryFactor
  nlinarith only [entryBound,finalBound,haltBound]

private theorem root_entry_le (shape : Shape) (rows ell precision : ℕ)
    (volumePositive : 0<CompactNativeRoleTransferBudget.volume rows shape ell precision) :
    entryCost shape rows ell precision≤
      (CompactComplexSourceReadyNonleafTargetSplit.constant roles+
        NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+2)*
          CompactNativeRoleTransferBudget.volume rows shape ell precision :=
  entry_boundary_algebra
    (CompactComplexSourceReadyNonleafTargetSplit.constant roles)
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
    (CompactNativeRoleTransferBudget.volume rows shape ell precision) volumePositive

private theorem root_boundary_le (shape : Shape) (rows ell precision : ℕ) (rowsPositive : 0<rows) :
    (4*CompactComplexSourceReadyGuard.guardConstant+5)*CompactNativeRoleTransferBudget.volume rows shape ell precision+
      entryCost shape rows ell precision+rootFinalCost (shape:=shape) rows ell precision+2≤
    rootBoundaryCoefficient*CompactNativeRoleTransferBudget.volume rows shape ell precision := by
  have volumePositive := Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape ell precision)
  change 0<CompactNativeRoleTransferBudget.volume rows shape ell precision at volumePositive
  have finalBound := CompactComplexAlignedReachedFinalReturn.root_final_cost_linear (shape:=shape) rows ell precision rowsPositive
  have entryBound := root_entry_le shape rows ell precision volumePositive
  have haltBound := Nat.le_mul_of_pos_right 2 volumePositive
  exact root_boundary_algebra
    (4*CompactComplexSourceReadyGuard.guardConstant+5)
    (CompactComplexSourceReadyNonleafTargetSplit.constant roles+
      NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+2)
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+
      2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+
      CompactComplexSourceReadyNonleafFinalPath.constant roles+9)
    (CompactNativeRoleTransferBudget.volume rows shape ell precision)
    (entryCost shape rows ell precision) (rootFinalCost (shape:=shape) rows ell precision)
    entryBound finalBound haltBound

/-- An arbitrary-depth nonstopped root halts on the unchanged aligned table
and emits the genuine corrected tensor at every original array address.
All costs, including the classifier and empty-stack exit, are charged to
the actual recursive schedule budget; its uniform estimate is separate. -/
theorem exists_root_execution_with_runtime
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
    ∃ runtimeConstant : ℝ,0<runtimeConstant ∧
    runtimeConstant=CompactComplexActualProviderRuntime.uniformBasisConstant packingLimit ∧
    ∃ childPathBudget : ComplexRecursiveCallSchema.Call → ℕ,
    ∃ elapsedSteps,∃ outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2,
    ∃ outputArray : Array shape rowCount polynomialExponent,
      elapsedSteps≤(4*CompactComplexSourceReadyGuard.guardConstant+5)*
          CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision+
        entryCost shape rowCount polynomialExponent metadataPrecision+
        CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
          packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked+
        rootFinalCost (shape:=shape) rowCount polynomialExponent metadataPrecision+2 ∧
      (elapsedSteps : ℝ)≤
        ((rootBoundaryCoefficient : ℝ)+CompactComplexActualProviderRuntime.localCoefficient shape runtimeConstant childExponent+
          if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
            (ComplexRank25.rankSum : ℝ)/roles*CompactComplexActualProviderRuntime.pathCoefficient shape runtimeConstant childExponent)*
          (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision : ℝ) ∧
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
  dsimp only
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
  let stage := parent phaseCoordinate entryPath.visit activeFits pair
  let stageSlots : stage.slots=25^3 := rfl
  have rolesPositive : 0<roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
    rolesPositive chunkPositive (by omega)
  have rowsPositive : 0<rowCount := by rw [rowsPadded]; exact rowGuards.2.1
  have childRowsPositive : 0<rowCount/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
  have rolesDivideRows : roles∣rowCount := by rw [rowsPadded]; exact rowGuards.1
  obtain ⟨initialState,entryBank,entryData,initialProtectedTails⟩ := CompactComplexSourceReadyReachedNodeEntry.initial_state
    stage stageSlots rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive
    rolesDivideRows originalCoefficients entryPath baselineFitsPrecision (by omega) inputWidth inputGrid
    controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady clockBlank auxiliaryFree
    exponentReady control28Blank control29Blank initialLedger pcStack stackOrigin [] savedAssociated headerStack liveStack originalProtectedTails
  obtain ⟨runtimeConstant,constantPositive,fixedConstantEq,childPathBudget,scheduleBound,scheduleExists⟩ :=
    CompactComplexSourceReadyRecursiveNodeExecution.exists_execution_values_with_runtime
    phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit
    guardPositive guardFitsChunk basisProgram headerStack pcStack liveStack basisConstant basisRuns largeAxes activePositive
    axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom precisionReserve baselineFits
    growthReserve denominatorRoom childExponent entryPath rowsPadded
  obtain ⟨finalLive,finalBoundary,eventElapsed,actualTrace,eventBound,minimumCoverage,targetCoverage,networkValues⟩ :=
    scheduleExists stackOrigin [] initialLive initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails
  obtain ⟨sinkTensor,outputWidth,outputGrid,roleValues,outputTensor⟩ :=
    CompactComplexSourceReadyReachedStoppedNodeNormalizedValues.normalize_of_schedule
      phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack originalCoefficients inputWidth inputGrid
      baselineFitsPrecision stageSlots rolesDivideRows initialState entryData finalLive finalBoundary eventElapsed actualTrace
      (by simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using networkValues)
      activePositive precisionReserve growthReserve childChunkRoom baselineFits denominatorRoom
  have initialTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry initialState.reached
    stageSlots initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank scalarHeaders tailBank
    originalStorage auxiliaryBank entryBank
  have terminalTarget : finalBoundary.state.reached.targetValue=
      CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1) := by
    rw [finalBoundary.targetRetained,initialTarget]
    rfl
  have joinedNormalized := CompactComplexSourceReadyNormalizedBoundary.joined_eq_normalized
    finalBoundary.state.reached stageSlots rolesDivideRows
  rw [terminalTarget] at joinedNormalized
  let outputArray := joined finalBoundary.state.reached stageSlots rolesDivideRows
  let outputBank := rootEndpoint finalBoundary.state.reached stageSlots rolesDivideRows
  have outputSource := CompactComplexAlignedReachedFinalReturn.root_endpoint_source finalBoundary.state.reached stageSlots rolesDivideRows
  have stackEmpty : originalStorage.tape (Fin.natAdd 10 pcStack)
      (originalStorage.head (Fin.natAdd 10 pcStack)-1)=blank := by
    rcases CompactComplexSourceReadySavedCallHistory.cases_stack savedAssociated with
      ⟨_,emptyTape,_⟩ | ⟨call,rest,older,top,impossible,_⟩
    · rw [emptyTape]
    · cases impossible
  obtain ⟨classifierElapsed,classifierBound,classifierPath⟩ := CompactComplexAlignedNonleafClassifierPrefix.root_runs
    basisProgram headerStack pcStack liveStack stage entryPath originalCoefficients rowsPositive (by omega) axesPositive activeFits
    controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank exponentReady stackEmpty nodeNonstopped
  obtain ⟨entryElapsed,entryBound,physicalEntry⟩ := CompactComplexAlignedReachedNodeEntryPath.runs
    phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack originalCoefficients inputWidth baselineFitsPrecision
    baselineFits controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank currentReady targetBlank initialLedger
    guardPositive guardFitsChunk rowsPositive rolesDivideRows unitPayload stageSlots denominatorRoom axesPositive initialState entryBank
  have physicalPrefix := FiniteFlowPath.append classifierPath physicalEntry
  let prefixBudget := (4*CompactComplexSourceReadyGuard.guardConstant+5)*
    CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision+
    entryCost shape rowCount polynomialExponent metadataPrecision
  obtain ⟨elapsedSteps,totalBound,rootRun⟩ := CompactComplexAlignedReachedFinalReturn.root_halts_of_execution
    entryPath basisProgram initialState finalBoundary actualTrace stageSlots rolesDivideRows rowsPositive childRowsPositive
    (by omega) axesPositive guardFitsChunk unitPayload baselineFits precisionReserve denominatorRoom
    (originalBank stage rowCount polynomialExponent metadataPrecision originalCoefficients
      controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank)
    (classifierElapsed+entryElapsed) prefixBudget (Nat.add_le_add classifierBound entryBound) physicalPrefix
  have actualTimeBound := totalBound.trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left eventBound prefixBudget) _) _)
  have boundaryBound := root_boundary_le shape rowCount polynomialExponent metadataPrecision rowsPositive
  have boundaryReal := Nat.cast_le (α:=ℝ).mpr boundaryBound
  push_cast at boundaryReal
  have actualTimeReal := Nat.cast_le (α:=ℝ).mpr actualTimeBound
  push_cast at actualTimeReal
  refine ⟨runtimeConstant,constantPositive,fixedConstantEq,childPathBudget,elapsedSteps,outputBank,outputArray,
    actualTimeBound,?_,rootRun,outputSource.1,outputSource.2,?_,?_,?_⟩
  · dsimp only [prefixBudget] at actualTimeReal
    push_cast at actualTimeReal
    nlinarith only [actualTimeReal,boundaryReal,scheduleBound]
  · simpa only [outputArray,joinedNormalized] using outputWidth
  · simpa only [outputArray,joinedNormalized] using outputGrid
  · simpa only [outputArray,joinedNormalized] using outputTensor

/-- Compatibility projection of the same runtime-certified literal root run. -/
theorem exists_root_execution
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
    exists_root_execution_with_runtime phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision
      growthConstant baselineLive packingLimit guardPositive guardFitsChunk basisProgram headerStack pcStack liveStack basisConstant
      basisRuns largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom
      precisionReserve baselineFits baselineFitsPrecision growthReserve denominatorRoom childExponent entryPath rowsPadded
      nodeNonstopped initialLive originalCoefficients inputWidth inputGrid controlBank queueBank scalarHeaders tailBank originalStorage
      auxiliaryBank countBlank currentReady targetBlank clockBlank auxiliaryFree exponentReady control28Blank control29Blank
      initialLedger stackOrigin savedAssociated pcHeaderDistinct pcLiveDistinct headerLiveDistinct originalProtectedTails
  exact ⟨childPathBudget,elapsedSteps,outputBank,outputArray,naturalBound,rootRun,outputSource,outputHead,
    outputWidth,outputGrid,outputTensor⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveRootExecution
