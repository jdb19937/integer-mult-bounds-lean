module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNodeEntry
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedScheduleValues

/-! Actual node-input ports and original coefficients construct the reached
entry state and complete its scalar/stopped event schedule. Entry bank, emitted
source data, terminal network values, frames, target and paid event budget are
derived together; no initial Reached or post-event semantics are inputs. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeSchedule
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexSourceReadyReachedStoppedSchedule (totalBudget)
open CompactComplexSourceReadyChildEventSemantics (stored)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount
  totalBudget
section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- A complete actual event schedule from original node input readiness,
with exact compiler-network output on the chosen physical terminal bank. -/
theorem exists_node_schedule
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount)
    (originalCoefficients : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)) originalCoefficients)
    (baselineFitsPrecision : baselinePrecision ≤ inputPrecision)
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
    (initialLedger : initialLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls
      (originalStorage.tape (Fin.natAdd 10 pcStack)) (originalStorage.head (Fin.natAdd 10 pcStack)))
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (originalProtectedTails : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,originalStorage.head storagePort≤cell →
      originalStorage.tape storagePort cell=blank)
    (activePositive : 0<shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤shape.chunk)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<rowCount) (childRowsPositive : 0<rowCount/roles) (rolesDivideRows : roles∣rowCount)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits≤(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) :
    ∃ initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive,
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
      (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
        elapsedSteps≤totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
          childRowsPositive parentSlots parentPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1)≤finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)≤finalLive ∧
        ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
            finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
          Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^(childExponent+1)))
            (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
              initialLive initialState.reached.data row polynomialIndex globalAnchor) := by
  obtain ⟨initialState,entryBank,entryData,entryTails⟩ :=
    CompactComplexSourceReadyReachedNodeEntry.initial_state (parent phaseCoordinate entryPath.visit activeFits pair)
      parentSlots rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive
      rolesDivideRows originalCoefficients entryPath baselineFitsPrecision
      (by have chunkRoom := childChunkRoom; omega) inputWidth inputGrid
      controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady clockBlank auxiliaryFree
      exponentReady control28Blank control29Blank initialLedger pcStack origin savedCalls savedAssociated headerStack liveStack
      originalProtectedTails
  obtain ⟨finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,minimumCoverage,targetCoverage,networkValues⟩ :=
    CompactComplexSourceReadyReachedStoppedScheduleValues.exists_execution_values phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack initialState pcHeaderDistinct pcLiveDistinct
      headerLiveDistinct entryTails activePositive childStopped axesFit childChunkRoom scalarChunkRoom guardPositive guardFitsChunk
      rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve
      denominatorRoom axesPositive chunkPositive
  exact ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
    minimumCoverage,targetCoverage,networkValues⟩

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeSchedule
