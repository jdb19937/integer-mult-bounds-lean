module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeNormalizedValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget
public import IntegerMultBounds.Machine.CompactComplexAlignedReachedFinalReturn

/-! A complete stopped-child node event schedule, physical finalization and
saved-PC return from original input readiness. The popped source contains the
literal post-oriented normalized array whose full tensor semantics are retained. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeFinalizedValues
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorInheritedGrid (Grid Width decoded half)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyReachedStoppedNodeNormalizedValues (normalized)
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

/-- Finalize an arbitrary actual recursive schedule and pop its saved call.
The trace provides target coverage, and its reached frame provides the physical
capacity. This endpoint does not depend on any child stopping hypothesis. -/
theorem finalize_of_schedule
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (rolesDivideRows : roles∣rowCount)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::olderCalls)) 0 initialLive)
    (initialTarget : initialState.reached.targetValue=
      CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
    (finalLive : ℕ) (finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::olderCalls)) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive)
    (elapsedSteps : ℕ)
    (actualTrace : Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps)
    (rowsPositive : 0 < rowCount) (childRowsPositive : 0 < rowCount/roles)
    (axesPositive : 0 < shape.axes) (guardPositive : 1 ≤ shape.guard)
    (guardFitsChunk : shape.guard+1 ≤ shape.chunk)
    (unitPayload : shape.payload=1)
    (baselineFits : baselineLive ≤ baselinePrecision)
    (precisionReserve : baselinePrecision+2*shape.bits ≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk) :
        ∃ older top finalElapsed,
          CompactComplexSourceReadySavedCallHistory.Associated origin olderCalls older top ∧
          finalElapsed≤elapsedSteps+CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape)
            rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
            (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5) ∧
          CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
            (CompactComplexSourceReadyReachedEventTrace.cursorPC 0)
            (CompactComplexSourceReadyReachedEventTrace.physicalBank initialState) finalElapsed
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
          resultBank.head sourcePort=0 ∧
          resultBank.tape sourcePort=CompactSpectatorLeafAxis.word
            (CompactComplexSourceReadyOrientationInvariants.oriented call
              (normalized rowCount polynomialExponent finalLive
                (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
                (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                  parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                  finalBoundary.state.reached.data))) := by
  have metadataFits : 2*shape.bits≤ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  have terminalTarget : finalBoundary.state.reached.targetValue=
      CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1) := by
    exact finalBoundary.targetRetained.trans initialTarget
  have currentCapacity : finalLive≤CompactSpectatorInheritedGrid.half shape
      ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)+1 := by
    rw [CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits]
    exact CompactComplexSourceReadyReachedCursorGuards.current_capacity entryPath finalBoundary.state
      baselineFits precisionReserve denominatorRoom
  have targetCoverage := (CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage actualTrace).2
  have targetBelowCurrent : finalBoundary.state.reached.targetValue≤finalLive := by
    rw [terminalTarget]
    exact targetCoverage
  obtain ⟨older,top,returnElapsed,olderAssociated,returnBound,returnPath⟩ :=
    CompactComplexAlignedReachedFinalReturn.runs basisProgram headerStack pcStack liveStack origin olderCalls call
      finalBoundary.state.reached parentSlots rowsPositive rolesDivideRows childRowsPositive guardPositive axesPositive
      guardFitsChunk unitPayload metadataFits targetBelowCurrent currentCapacity
  have eventPath := CompactComplexSourceReadyReachedEventTrace.execution_physical actualTrace
  have finalPCEqual : CompactComplexSourceReadyReachedEventTrace.cursorPC schedule.length=
      CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 3 := by
    exact CompactComplexSourceReadyReachedEventTrace.cursorPCFor_final _ _
  rw [finalPCEqual] at eventPath
  have wholePath := FiniteFlowPath.append eventPath returnPath
  refine ⟨older,top,elapsedSteps+returnElapsed,olderAssociated,?_,wholePath,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add_left returnBound elapsedSteps
  · have sourceNormalized := CompactComplexSourceReadyNormalizedBoundary.popped_normalized_source
      finalBoundary.state.reached parentSlots rolesDivideRows call older top
    rw [terminalTarget] at sourceNormalized
    exact sourceNormalized


theorem exists_node_finalized_values
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
          initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage)
        auxiliaryBank ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
        (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots rowCount polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) rolesDivideRows originalCoefficients
        (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::olderCalls)) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
        elapsedSteps ≤ totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
          childRowsPositive parentSlots parentPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1) ≤ finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1) ≤ finalLive ∧
        (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
            finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
          Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^(childExponent+1)))
            (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
              initialLive initialState.reached.data row polynomialIndex globalAnchor)) ∧
        (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision finalLive
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
              parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data) row polynomialIndex globalAnchor=
            fun wire => Networks.ComplexEndpoints.fullFrame (arity^(childExponent+1))
              (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision initialLive
                (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivideRows originalCoefficients)
                row polynomialIndex globalAnchor wire)) ∧
        (∀ index,((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).1.length=half shape inputPrecision+1 ∧
          ((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).2.length=half shape inputPrecision+1) ∧
        Grid shape rowCount polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) ((CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))*4^(2*arity^(childExponent+2))) (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) ∧
        (∀ scalarRole index,decoded shape (rowCount/roles) polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
          (CompactNativeRoleReservedBridge.role shape rowCount roles polynomialExponent rolesDivideRows (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data))
            (roleIndex scalarRole)) index=
          decoded shape (rowCount/roles) polynomialExponent inputPrecision finalLive
            ((CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data) scalarRole) index) ∧
        (∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          decoded shape rowCount polynomialExponent inputPrecision
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
            (normalized rowCount polynomialExponent finalLive
              (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
              (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                finalBoundary.state.reached.data))
            (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
          ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
              (pack rawRow (FlatCoordinateLayout.index
                (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex)))
            (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor)) ∧
        ∃ older top finalElapsed,
          CompactComplexSourceReadySavedCallHistory.Associated origin olderCalls older top ∧
          finalElapsed≤elapsedSteps+CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape)
            rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
            (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5) ∧
          CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
            (CompactComplexSourceReadyReachedEventTrace.cursorPC 0)
            (CompactComplexSourceReadyReachedEventTrace.physicalBank initialState) finalElapsed
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
          resultBank.head sourcePort=0 ∧
          resultBank.tape sourcePort=CompactSpectatorLeafAxis.word
            (CompactComplexSourceReadyOrientationInvariants.oriented call
              (normalized rowCount polynomialExponent finalLive
                (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
                (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                  parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                  finalBoundary.state.reached.data))) := by
  obtain ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
      minimumCoverage,targetCoverage,networkValues,tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor⟩ :=
    CompactComplexSourceReadyReachedStoppedNodeNormalizedValues.exists_node_normalized_values phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack originalCoefficients inputWidth inputGrid
      baselineFitsPrecision controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady
      clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger savedAssociated pcHeaderDistinct
      pcLiveDistinct headerLiveDistinct originalProtectedTails activePositive childStopped axesFit childChunkRoom scalarChunkRoom
      guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked precisionReserve
      baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  refine ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
    minimumCoverage,targetCoverage,networkValues,tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor,?_⟩
  have initialTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    initialState.reached parentSlots initialLive (childExponent+1) rolesDivideRows originalCoefficients
    controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank entryBank
  exact finalize_of_schedule call phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack
    parentSlots rolesDivideRows initialState initialTarget finalLive finalBoundary elapsedSteps actualTrace
    rowsPositive childRowsPositive axesPositive guardPositive guardFitsChunk unitPayload baselineFits precisionReserve denominatorRoom

/-- Original input readiness, the mixed recursive schedule, literal tensor
normalization and the physical saved-call return on its actual terminal bank. -/
theorem exists_node_finalized_values_of_provider
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
    (axesFit : 0+arity^(childExponent+1) ≤ shape.bits)
    (nonstoppedAxesFit : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false →
      0+2*arity^(childExponent+1) ≤ shape.bits)
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
    (childSlots : ∀ call : Networks.ComplexRecursiveCallSchema.Call,
      (CompactComplexChildHeadersData.child phaseCoordinate entryPath.visit activeFits pair call.slot).slots=arity)
    (childRowsDivisible : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false →
      roles∣rowCount/roles)
    (childEventBudget childPathBudget : Networks.ComplexRecursiveCallSchema.Call → ℕ)
    (provider : ∀ childNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false,
      CompactComplexSourceReadyRecursiveChildProvider.Provider
      (parentRows:=rowCount) (polynomialExponent:=polynomialExponent) (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=(call::olderCalls)) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate entryPath activeFits pair basisProgram childSlots (childRowsDivisible childNonstopped) childEventBudget childPathBudget)
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
          initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage)
        auxiliaryBank ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
        (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots rowCount polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) rolesDivideRows originalCoefficients
        (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=(call::olderCalls)) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
        elapsedSteps ≤ CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget guardPositive guardFitsChunk
          childRowsPositive parentSlots parentPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1) ≤ finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1) ≤ finalLive ∧
        (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
            finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
          Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^(childExponent+1)))
            (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
              initialLive initialState.reached.data row polynomialIndex globalAnchor)) ∧
        (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision finalLive
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
              parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data) row polynomialIndex globalAnchor=
            fun wire => Networks.ComplexEndpoints.fullFrame (arity^(childExponent+1))
              (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision initialLive
                (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivideRows originalCoefficients)
                row polynomialIndex globalAnchor wire)) ∧
        (∀ index,((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).1.length=half shape inputPrecision+1 ∧
          ((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).2.length=half shape inputPrecision+1) ∧
        Grid shape rowCount polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) ((CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))*4^(2*arity^(childExponent+2))) (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) ∧
        (∀ scalarRole index,decoded shape (rowCount/roles) polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
          (CompactNativeRoleReservedBridge.role shape rowCount roles polynomialExponent rolesDivideRows (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data))
            (roleIndex scalarRole)) index=
          decoded shape (rowCount/roles) polynomialExponent inputPrecision finalLive
            ((CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data) scalarRole) index) ∧
        (∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          decoded shape rowCount polynomialExponent inputPrecision
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
            (normalized rowCount polynomialExponent finalLive
              (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
              (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                finalBoundary.state.reached.data))
            (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
          ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
              (pack rawRow (FlatCoordinateLayout.index
                (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex)))
            (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor)) ∧
        ∃ older top finalElapsed,
          CompactComplexSourceReadySavedCallHistory.Associated origin olderCalls older top ∧
          finalElapsed≤elapsedSteps+CompactComplexAlignedReachedFinalReturn.finalCost (shape:=shape)
            rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+
            (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5) ∧
          CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
            (CompactComplexSourceReadyReachedEventTrace.cursorPC 0)
            (CompactComplexSourceReadyReachedEventTrace.physicalBank initialState) finalElapsed
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
          resultBank.head sourcePort=0 ∧
          resultBank.tape sourcePort=CompactSpectatorLeafAxis.word
            (CompactComplexSourceReadyOrientationInvariants.oriented call
              (normalized rowCount polynomialExponent finalLive
                (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
                (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                  parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                  finalBoundary.state.reached.data))) := by
  obtain ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
      minimumCoverage,targetCoverage,networkValues⟩ :=
    CompactComplexSourceReadyReachedStoppedNodeSchedule.exists_node_schedule_of_provider phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack originalCoefficients inputWidth inputGrid
      baselineFitsPrecision controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady
      clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger savedAssociated pcHeaderDistinct
      pcLiveDistinct headerLiveDistinct originalProtectedTails activePositive axesFit nonstoppedAxesFit childChunkRoom scalarChunkRoom
      guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked
      childSlots childRowsDivisible childEventBudget childPathBudget provider precisionReserve
      baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  obtain ⟨tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor⟩ :=
    CompactComplexSourceReadyReachedStoppedNodeNormalizedValues.normalize_of_schedule
      phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack originalCoefficients inputWidth inputGrid
      baselineFitsPrecision parentSlots rolesDivideRows initialState entryData finalLive finalBoundary elapsedSteps actualTrace
      networkValues activePositive precisionReserve growthReserve childChunkRoom baselineFits denominatorRoom
  refine ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
    minimumCoverage,targetCoverage,networkValues,tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor,?_⟩
  have initialTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    initialState.reached parentSlots initialLive (childExponent+1) rolesDivideRows originalCoefficients
    controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank entryBank
  exact finalize_of_schedule call phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack
    parentSlots rolesDivideRows initialState initialTarget finalLive finalBoundary elapsedSteps actualTrace
    rowsPositive childRowsPositive axesPositive guardPositive guardFitsChunk unitPayload baselineFits precisionReserve denominatorRoom

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeFinalizedValues
