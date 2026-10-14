module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedSchedule
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedRecursiveSchedule
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarFrameStep
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedFrameStep

/-! The stopped-child case specializes the same mixed recursive schedule
without strengthening its original public entry contracts. Conditional
nonstopped readiness and recursive child certificates are vacuous here; the
original stopped budgets and full-network values remain exact. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedScheduleValues
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexCompletedLiveLower (schedule Event childTarget)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyReachedEventTrace (State Step Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture captured advance)
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyReachedStoppedSchedule (scalarBudget stoppedBudget eventBudget totalBudget)
open CompactComplexSourceReadyChildEventSemantics (stored)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

attribute [local irreducible] scalarBudget stoppedBudget eventBudget totalBudget

/-- Every actual event is supplied by the checked scalar or stopped algorithm.
The initial bank and clean tails are genuine entry prerequisites; the saved
Ledger is derived once from that bank and transported through FrameState. -/
theorem exists_execution_values
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (initialProtectedTails : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,initialState.reached.storage.head storagePort≤cell →
      initialState.reached.storage.tape storagePort cell=blank)
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
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) :
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
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
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
          Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^(childExponent+1)))
            (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
              initialLive initialState.reached.data row polynomialIndex globalAnchor) := by
  have impossibleNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false → False := by
    intro childNonstopped
    have classifierConflict := childStopped.symm.trans childNonstopped
    cases classifierConflict
  let childSlots : ∀ call : Networks.ComplexRecursiveCallSchema.Call,
      (CompactComplexChildHeadersData.child phaseCoordinate entryPath.visit activeFits pair call.slot).slots=arity :=
    fun _ => rfl
  let childRowsDivisible : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false →
      roles∣rowCount/roles := fun childNonstopped => False.elim (impossibleNonstopped childNonstopped)
  let childEventBudget : Networks.ComplexRecursiveCallSchema.Call → ℕ := fun _ => 0
  let childPathBudget : Networks.ComplexRecursiveCallSchema.Call → ℕ := fun _ => 0
  have provider : ∀ childNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false,
      CompactComplexSourceReadyRecursiveChildProvider.Provider
        (parentRows:=rowCount) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
        (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
        (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) (headerStack:=headerStack) (liveStack:=liveStack)
        phaseCoordinate entryPath activeFits pair basisProgram childSlots (childRowsDivisible childNonstopped)
        childEventBudget childPathBudget :=
    fun childNonstopped => False.elim (impossibleNonstopped childNonstopped)
  obtain ⟨finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,minimumCoverage,targetCoverage,networkValues⟩ :=
    CompactComplexSourceReadyReachedRecursiveSchedule.exists_execution_values phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack initialState pcHeaderDistinct pcLiveDistinct
      headerLiveDistinct initialProtectedTails activePositive axesFit
      (fun childNonstopped => False.elim (impossibleNonstopped childNonstopped))
      childChunkRoom scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload
      parentSlots parentPacked childSlots childRowsDivisible childEventBudget childPathBudget provider
      precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  have budgetFunctionEquation :
      CompactComplexSourceReadyReachedRecursiveSchedule.eventBudget phaseCoordinate entryPath activeFits pair
        packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked =
      eventBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
        childRowsPositive parentSlots parentPacked := by
    funext event
    cases event with
    | scalar group =>
      unfold CompactComplexSourceReadyReachedRecursiveSchedule.eventBudget eventBudget
        CompactComplexSourceReadyReachedRecursiveSchedule.scalarBudget scalarBudget
      rfl
    | child call =>
      simp only [CompactComplexSourceReadyReachedRecursiveSchedule.eventBudget,eventBudget,childStopped,ite_true]
      unfold CompactComplexSourceReadyReachedRecursiveSchedule.stoppedBudget stoppedBudget
      rfl
  have budgetEquation :
      CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
        packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked =
      totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
        childRowsPositive parentSlots parentPacked := by
    unfold CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget totalBudget
    exact congrArg (fun budget : Event → ℕ => (schedule.map budget).sum) budgetFunctionEquation
  rw [budgetEquation] at timeBound
  exact ⟨finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,minimumCoverage,targetCoverage,networkValues⟩

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedScheduleValues
