module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedNodeEntryReturn
public import IntegerMultBounds.Machine.CompactComplexAlignedNonleafClassifierPrefix
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildTensor
public import IntegerMultBounds.Machine.CompactComplexAlignedReachedNodeEntryPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget
public import IntegerMultBounds.Machine.CompactComplexAlignedReachedFinalReturn

/-! Original nonleaf classification, corrected entry, stopped-child schedule,
finalization and genuine saved-PC return on the same aligned table. The literal
returned source computes the saved call's forward or inverse full tensor on
the original unoriented input, retaining raw rows and spectator coordinates. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyClassifiedStoppedNode
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorInheritedGrid (Grid Width decoded half)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyReachedStoppedNodeNormalizedValues (normalized)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (address)
open CompactComplexChildHeadersData (parent)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexSourceReadyReachedStoppedSchedule (totalBudget)
open Networks
open RecursiveInterchangeRows (pack)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexRolePhaseSite.roleEncoding totalBudget

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {olderCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (call : Networks.ComplexRecursiveCallSchema.Call)
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active ≤ shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

theorem exists_classified_node_return
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount)
    (originalCoefficients : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)) originalCoefficients)
    (baselineFitsPrecision : baselinePrecision  ≤  inputPrecision)
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
    (initialLedger : initialLive ≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin (call::olderCalls)
      (originalStorage.tape (Fin.natAdd 10 pcStack)) (originalStorage.head (Fin.natAdd 10 pcStack)))
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (originalProtectedTails : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,originalStorage.head storagePort ≤ cell →
      originalStorage.tape storagePort cell=blank)
    (activePositive : 0 < shape.active)
    (nodeNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+2)=false)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1) ≤ shape.bits)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits ≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits ≤ shape.chunk)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard+1 ≤ shape.chunk)
    (rowsPositive : 0 < rowCount) (childRowsPositive : 0 < rowCount/roles) (rolesDivideRows : roles∣rowCount)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1 < (parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits ≤ (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)) (baselineFits : baselineLive ≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk)
    (axesPositive : 0 < shape.axes) (chunkPositive : 0 < shape.chunk) :
    ∃ initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::olderCalls)) 0 initialLive,
      initialState.bank=CompactComplexSourceReadyReachedEventInvariant.canonical
        (CompactComplexCorrectedEntryGeometryReadiness.permanent (parent phaseCoordinate entryPath.visit activeFits pair)
          parentSlots rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          initialLive (childExponent+1) rolesDivideRows (oriented call originalCoefficients) controlBank queueBank scalarHeaders tailBank originalStorage)
        auxiliaryBank ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
        (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots rowCount polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) rolesDivideRows (oriented call originalCoefficients)
        (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::olderCalls)) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ eventElapsed,
        Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state eventElapsed ∧
        eventElapsed ≤ totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
          childRowsPositive parentSlots parentPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1) ≤ finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1) ≤ finalLive ∧
      ∃ older top elapsed,
        CompactComplexSourceReadySavedCallHistory.Associated origin olderCalls older top ∧
        elapsed ≤ ((CompactComplexSourceReadyOrientationInvariants.constant+
          4*CompactComplexSourceReadyGuard.guardConstant+1)*
          CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+1)+
          CompactComplexAlignedReachedNodeEntryPath.entryCost shape rowCount polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
          totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
            childRowsPositive parentSlots parentPacked+
          CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape) rowCount polynomialExponent
            (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
          (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5) ∧
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
          (CompactComplexAlignedReachedNodeEntryPath.originalBank (parent phaseCoordinate entryPath.visit activeFits pair)
            rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
            originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank) elapsed
          (CompactComplexScheduledPCDecode.savedPC call)
          (CompactComplexAlignedBoundaryPaths.alignedBank
            ((CompactComplexSourceReadyWorkspace.ready
              (CompactComplexAlignedPoppedReturnReadiness.popped
                (CompactComplexSourceReadyCompletedChildBoundary.completed finalBoundary.state.reached parentSlots rolesDivideRows call)
                pcStack older top)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) ∧
        let resultBank := CompactComplexAlignedPoppedReturnReadiness.popped
          (CompactComplexSourceReadyCompletedChildBoundary.completed finalBoundary.state.reached parentSlots rolesDivideRows call)
          pcStack older top
        let sourcePort := Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles))
        let resultArray := oriented call
          (normalized rowCount polynomialExponent finalLive
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
              parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data))
        resultBank.head sourcePort=0 ∧
        resultBank.tape sourcePort=CompactSpectatorLeafAxis.word resultArray ∧
        Width shape rowCount polynomialExponent inputPrecision resultArray ∧
        Grid shape rowCount polynomialExponent inputPrecision
          (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
          (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
            (frameVolume+2*entryReturned)*4^(2*arity^(childExponent+2))) resultArray ∧
        (∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          nativeField inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
            resultArray rawRow polynomialIndex globalAnchor =
          if call.inverse then (ComplexEndpoints.fullFrame (arity^(childExponent+1))).symm
            (slice phaseCoordinate entryPath.visit globalAnchor
              (nativeField inputPrecision initialLive originalCoefficients rawRow polynomialIndex))
            (address phaseCoordinate entryPath.visit globalAnchor)
          else ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (slice phaseCoordinate entryPath.visit globalAnchor
              (nativeField inputPrecision initialLive originalCoefficients rawRow polynomialIndex))
            (address phaseCoordinate entryPath.visit globalAnchor)) := by
  have dependencyFitsChunk : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant ≤ shape.chunk := by
    have availableRoom := childChunkRoom
    omega
  have strictGuardPositive : 0 < shape.guard := by omega
  obtain ⟨orientedWidth,orientedGrid,classifierElapsed,classifierBound,classifierPath⟩ :=
    CompactComplexAlignedNonleafClassifierPrefix.runs basisProgram headerStack pcStack liveStack call
      (parent phaseCoordinate entryPath.visit activeFits pair) entryPath originalCoefficients inputWidth inputGrid
      baselineFitsPrecision dependencyFitsChunk rowsPositive strictGuardPositive axesPositive activeFits
      controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank exponentReady origin olderCalls
      savedAssociated nodeNonstopped
  obtain ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
      minimumCoverage,targetCoverage,networkValues,tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor,
      older,top,nodeElapsed,olderAssociated,nodeBound,nodePath,sourceValues⟩ :=
    CompactComplexSourceReadyStoppedNodeEntryReturn.exists_node_entry_return call phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack (oriented call originalCoefficients)
      orientedWidth orientedGrid baselineFitsPrecision controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank
      countBlank currentReady targetBlank clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger
      savedAssociated pcHeaderDistinct pcLiveDistinct headerLiveDistinct originalProtectedTails activePositive childStopped
      axesFit childChunkRoom scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload
      parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  let normalizedArray := normalized rowCount polynomialExponent finalLive
    (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
    (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
      parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      finalBoundary.state.reached.data)
  have widthEquality : half shape inputPrecision+1 =
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) shape.bits := by
    unfold CompactSpectatorInheritedGrid.half ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  have normalizedStoredWidth : Width shape rowCount polynomialExponent inputPrecision normalizedArray := by
    intro index
    simpa only [normalizedArray,widthEquality] using normalizedWidth index
  obtain ⟨resultGrid,resultWidth,resultDecoded⟩ :=
    CompactComplexSourceReadyNonleafOrientedSemantics.post_grid call entryPath baselinePrecision growthConstant
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
      baselineFitsPrecision dependencyFitsChunk
      (normalized rowCount polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
        (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
          parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          finalBoundary.state.reached.data)) normalizedStoredWidth normalizedGrid
  refine ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
    minimumCoverage,targetCoverage,older,top,classifierElapsed+nodeElapsed,
    olderAssociated,?_,FiniteFlowPath.append classifierPath nodePath,sourceValues.1,sourceValues.2,
    resultWidth,resultGrid,?_⟩
  · omega
  · intro rawRow polynomialIndex globalAnchor
    exact CompactComplexSourceReadyNonleafChildTensor.normalized_native_tensor call rowCount polynomialExponent
      inputPrecision initialLive finalLive phaseCoordinate entryPath.visit entryPath baselinePrecision growthConstant
      baselineFitsPrecision dependencyFitsChunk originalCoefficients inputWidth inputGrid rolesDivideRows
      (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
        parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)
      normalizedStoredWidth normalizedGrid normalizedTensor rawRow polynomialIndex globalAnchor

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyClassifiedStoppedNode
