module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren
public import IntegerMultBounds.Machine.CompactComplexActualProviderRuntime

/-! Complete mixed-node execution with the child provider discharged by
exponent induction. Budgets are chosen from static geometry before the
dynamic entry state; every event runs on the original aligned table. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveNodeExecution
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexSourceReadyReachedDormantFrameInvariant (protectedSlots)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction
  (PackingFamily exists_fixed_provider)
open CompactGlobalRowPadding (rowsAt)
open CompactRecursiveDependencyBudget (Path)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget

variable {stackCount basisStateCount : ℕ} {shape : Shape}

/-- Arbitrary-depth actual schedules exist with fixed static budgets, exact
compiler values, target coverage and settled frames. No child execution or
child tensor assertion is a premise. The certified uniform runtime estimate
on these actual budgets remains a separate obligation. -/
theorem exists_execution_values_with_runtime
    (phaseCoordinate : Fin shape.chunk) (activeFits : shape.active≤shape.axes)
    (pair : BinaryRowProgram.Op (Fin arity))
    (polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount)
    (basisConstant : ℝ)
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
    (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume entryReturned rowCount : ℕ}
    (entryPath : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels) :
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsPositive : 0<rowCount/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
    let parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3 := rfl
    let parentPacked := packingFamily entryPath rowCount rowsPadded childRowsPositive
    ∃ runtimeConstant : ℝ,0<runtimeConstant ∧
    ∃ childPathBudget : ComplexRecursiveCallSchema.Call → ℕ,
    (CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
      packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked : ℝ)≤
      (CompactComplexActualProviderRuntime.localCoefficient shape runtimeConstant childExponent+
        if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
          (ComplexRank25.rankSum : ℝ)/roles*CompactComplexActualProviderRuntime.pathCoefficient shape runtimeConstant childExponent)*
        (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent
          (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) : ℝ) ∧
    ∀ (origin : ℤ) (savedCalls : List ComplexRecursiveCallSchema.Call) (initialLive : ℕ)
      (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
        (polynomialExponent:=polynomialExponent)
        (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
        (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
        (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
        (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
        (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
      (_pcHeaderDistinct : pcStack≠headerStack) (_pcLiveDistinct : pcStack≠liveStack)
      (_headerLiveDistinct : headerStack≠liveStack)
      (_initialProtectedTails : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
        ∀ cell,initialState.reached.storage.head storagePort≤cell →
          initialState.reached.storage.tape storagePort cell=blank),
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair)
      (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
    ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
      elapsedSteps≤CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
        packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked ∧
      CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1)≤finalLive ∧
      CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)≤finalLive ∧
      ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
        stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision
          finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
        FramedCircuit.run (ComplexFramedExecution.network (arity^(childExponent+1)))
          (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision
            initialLive initialState.reached.data row polynomialIndex globalAnchor) := by
  dsimp only
  have rolesPositive : 0<roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
    rolesPositive chunkPositive (by omega)
  have rowsPositive : 0<rowCount := by rw [rowsPadded]; exact rowGuards.2.1
  have childRowsPositive : 0<rowCount/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
  have rolesDivideRows : roles∣rowCount := by rw [rowsPadded]; exact rowGuards.1
  let parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3 := rfl
  let parentPacked := packingFamily entryPath rowCount rowsPadded childRowsPositive
  obtain ⟨runtimeConstant,constantPositive,localBounds,runtimeProviders⟩ :=
    CompactComplexActualProviderRuntime.exists_runtime_provider phaseCoordinate activeFits pair polynomialExponent inputPrecision
      packingLimit guardPositive guardFitsChunk baselinePrecision growthConstant baselineLive basisProgram headerStack pcStack liveStack
      basisConstant basisRuns largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom
      precisionReserve baselineFits growthReserve denominatorRoom
  obtain ⟨childEventBudget,childPathBudget,uniformProvider,runtimeCertificate⟩ := runtimeProviders childExponent entryPath rowsPadded
  have scheduleBound := CompactComplexActualProviderRuntime.schedule_coefficient_bound phaseCoordinate entryPath activeFits pair
    packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked runtimeConstant childPathBudget rolesDivideRows
    (localBounds entryPath rowsPadded) runtimeCertificate
  refine ⟨runtimeConstant,constantPositive,childPathBudget,scheduleBound,?_⟩
  intro origin savedCalls initialLive initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails
  have doubleChildFit := CompactComplexRecursivePathRows.two_child_volumes_fit entryPath chunkPositive
  have singleChildFit : 0+arity^(childExponent+1)≤shape.bits := by omega
  have actualExecution := CompactComplexSourceReadyReachedRecursiveSchedule.exists_execution_values
    phaseCoordinate entryPath activeFits pair packingLimit basisProgram basisConstant basisRuns headerStack liveStack
    initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails activePositive singleChildFit
    (fun _ => doubleChildFit) childChunkRoom scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive
    rolesDivideRows unitPayload parentSlots parentPacked (fun _ => rfl) (fun _ => by rw [rowsPadded]; exact rowGuards.2.2.1)
    childEventBudget childPathBudget (fun _ => uniformProvider origin savedCalls)
    precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  simpa only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using actualExecution

/-- Compatibility projection of the same runtime-certified actual schedule. -/
theorem exists_execution_values
    (phaseCoordinate : Fin shape.chunk) (activeFits : shape.active≤shape.axes)
    (pair : BinaryRowProgram.Op (Fin arity))
    (polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount)
    (basisConstant : ℝ)
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
    (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume entryReturned rowCount : ℕ}
    (entryPath : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels) :
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsPositive : 0<rowCount/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
    let parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3 := rfl
    let parentPacked := packingFamily entryPath rowCount rowsPadded childRowsPositive
    ∃ childPathBudget : ComplexRecursiveCallSchema.Call → ℕ,
    ∀ (origin : ℤ) (savedCalls : List ComplexRecursiveCallSchema.Call) (initialLive : ℕ)
      (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
        (polynomialExponent:=polynomialExponent)
        (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
        (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
        (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
        (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
        (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
      (_pcHeaderDistinct : pcStack≠headerStack) (_pcLiveDistinct : pcStack≠liveStack)
      (_headerLiveDistinct : headerStack≠liveStack)
      (_initialProtectedTails : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
        ∀ cell,initialState.reached.storage.head storagePort≤cell →
          initialState.reached.storage.tape storagePort cell=blank),
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair)
      (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
    ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
      elapsedSteps≤CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
        packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked ∧
      CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1)≤finalLive ∧
      CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)≤finalLive ∧
      ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
        stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision
          finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
        FramedCircuit.run (ComplexFramedExecution.network (arity^(childExponent+1)))
          (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision
            initialLive initialState.reached.data row polynomialIndex globalAnchor) := by
  obtain ⟨runtimeConstant,constantPositive,childPathBudget,scheduleBound,execution⟩ := exists_execution_values_with_runtime
    phaseCoordinate activeFits pair polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit
    guardPositive guardFitsChunk basisProgram headerStack pcStack liveStack basisConstant basisRuns largeAxes activePositive
    axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom precisionReserve baselineFits
    growthReserve denominatorRoom childExponent entryPath rowsPadded
  exact ⟨childPathBudget,execution⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveNodeExecution
