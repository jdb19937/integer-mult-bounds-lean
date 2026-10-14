module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventFrameState
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarFrameStep
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedFrameStep

/-! Existence of the complete actual event schedule when all its recursive
children stop. Concrete scalar and stopped-child routines construct each
step, preserving real saved frames and the target captured at node entry.
The terminal trace has the sum of the actual scalar and stopped-event budgets. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedSchedule
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
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

/-- Pure indexed iteration is proved with a symbolic event count before any
actual schedule or dependent reached banks are specialized. -/
private theorem indexed_loop (Boundary : ℕ → ℕ → Type)
    (Trace : ∀ {eventIndex live},Boundary eventIndex live → ℕ → Prop)
    (eventCount initialLive : ℕ) (initialBoundary : Boundary 0 initialLive)
    (initialTrace : Trace initialBoundary 0)
    (next : ∀ eventIndex sourceLive (before : Boundary eventIndex sourceLive) priorSteps,
      Trace before priorSteps → eventIndex<eventCount →
      ∃ targetLive,∃ after : Boundary (eventIndex+1) targetLive,∃ totalSteps,Trace after totalSteps) :
    ∃ finalLive,∃ finalBoundary : Boundary eventCount finalLive,∃ totalSteps,Trace finalBoundary totalSteps := by
  have prefixes : ∀ eventIndex,eventIndex≤eventCount →
      ∃ live,∃ boundary : Boundary eventIndex live,∃ elapsedSteps,Trace boundary elapsedSteps :=
    Nat.rec (motive:=fun eventIndex => eventIndex≤eventCount →
      ∃ live,∃ boundary : Boundary eventIndex live,∃ elapsedSteps,Trace boundary elapsedSteps)
      (fun _ => ⟨initialLive,initialBoundary,0,initialTrace⟩)
      (fun eventIndex priorPrefix prefixBound => by
        obtain ⟨sourceLive,before,priorSteps,priorTrace⟩ := priorPrefix (by omega)
        exact next eventIndex sourceLive before priorSteps priorTrace (by omega))
  exact prefixes eventCount le_rfl

/-- Local budget accumulation is proved on abstract lists before specializing
any static compiler schedule or block-cost expression. -/
private theorem budget_prefix_successor (events : List Event) (budget : Event → ℕ)
    (eventIndex : ℕ) (eventBound : eventIndex<events.length) :
    ((events.take (eventIndex+1)).map budget).sum=
      ((events.take eventIndex).map budget).sum+budget events[eventIndex] := by
  rw [List.take_succ_eq_append_getElem eventBound,List.map_append,List.sum_append]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- Actual scalar lifecycle and its unchanged-table transition. -/
def scalarBudget (group : GroupIndex) :=
  CompactComplexScalarCountLifecycle.roleTimeConstant (block group)*
    (rowCount*2^shape.bits*2^polynomialExponent)*(ButterflyGuard.halfWidth metadataPrecision shape.bits+2)+1

/-- Both original basis passes, physical child entry, stopped body, real
saved-PC pop and complete parent restoration, including every table edge. -/
def stoppedBudget (packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (call : Networks.ComplexRecursiveCallSchema.Call) :=
  let stage := parent phaseCoordinate entryPath.visit activeFits pair
  let basisPC := CompactComplexRolePhaseSite.pc call.site
  let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) polynomialExponent
    metadataPrecision guardPositive guardFitsChunk childRowsPositive
  let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
    basisInput polynomialExponent (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
      basisPC false (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent)
        (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
  (CompactComplexActualCallRoleAlignment.cost roles stage rowCount polynomialExponent metadataPrecision passTime+
    1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) rowCount polynomialExponent metadataPrecision+1)+
    (CompactComplexAlignedStoppedReturnPath.prefixCost (rowCount/roles) shape polynomialExponent metadataPrecision childExponent+
      CompactComplexAlignedStoppedReturnPath.returnCost phaseCoordinate entryPath.visit activeFits pair call packingLimit
        guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked)

def eventBudget (packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) : Event → ℕ
  | .scalar group => scalarBudget (shape:=shape) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) group
  | .child call => stoppedBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
      childRowsPositive parentSlots parentPacked call

def totalBudget (packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) :=
  (schedule.map (eventBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
    childRowsPositive parentSlots parentPacked)).sum

attribute [local irreducible] scalarBudget stoppedBudget eventBudget totalBudget

/-- Every actual event is supplied by the checked scalar or stopped algorithm.
The initial bank and clean tails are genuine entry prerequisites; the saved
Ledger is derived once from that bank and transported through FrameState. -/
theorem exists_execution
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
        CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)≤finalLive := by
  let snapshot := capture initialState headerStack liveStack
  let Boundary : ℕ → ℕ → Type := fun eventIndex live =>
    FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) snapshot initialState.reached.targetValue eventIndex live
  let budget : Event → ℕ := eventBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
    childRowsPositive parentSlots parentPacked
  let Trace : ∀ {eventIndex live},Boundary eventIndex live → ℕ → Prop :=
    fun {eventIndex live} boundary elapsedSteps =>
      Execution basisProgram headerStack liveStack initialLive initialState boundary.state elapsedSteps ∧
      elapsedSteps≤((schedule.take eventIndex).map budget).sum
  let initialBoundary : Boundary 0 initialLive := captured initialState headerStack liveStack initialProtectedTails
  have zeroCounter : CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned 0
      (arity^(childExponent+1))=entryReturned := by
    simp only [CompactComplexSourceReadySiblingGuards.returnedCursor,List.take_zero,
      CompactComplexCompletedLiveLower.childNames,List.length_nil,Nat.zero_mul,Nat.add_zero]
  have entryPathForCursor : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
      dependencyLevels frameVolume
      (CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned 0 (arity^(childExponent+1))) := by
    rw [zeroCounter]
    exact entryPath
  have entryLedger := CompactComplexSourceReadySiblingChildProgress.entryTargetLedger entryPathForCursor initialState.reached
    precisionReserve baselineFits denominatorRoom
  have actualNext : ∀ eventIndex sourceLive (before : Boundary eventIndex sourceLive) priorSteps,
      Trace before priorSteps → eventIndex<schedule.length →
      ∃ targetLive,∃ after : Boundary (eventIndex+1) targetLive,∃ totalSteps,Trace after totalSteps := by
    intro eventIndex sourceLive before priorSteps priorTrace eventBound
    cases eventEquation : schedule[eventIndex] with
    | scalar group =>
      obtain ⟨afterState,afterData,targetRetained,afterSettled,eventSteps,eventTimeBound,eventStep⟩ :=
        CompactComplexSourceReadyReachedEventScalarFrameStep.scalar_step basisProgram entryPath headerStack liveStack
          group eventBound eventEquation before.state snapshot before.settled childRowsPositive (by omega)
          chunkPositive activePositive precisionReserve (Nat.zero_le _) (scalarChunkRoom group) growthReserve
          baselineFits denominatorRoom
      let afterBoundary : Boundary (eventIndex+1) (sourceLive+(block group).length) :=
        advance before afterState targetRetained afterSettled
      have eventBudgetBound : eventSteps≤budget (Event.scalar group) := by
        simpa only [budget,eventBudget,scalarBudget] using eventTimeBound
      have prefixBudget := budget_prefix_successor schedule budget eventIndex eventBound
      rw [eventEquation] at prefixBudget
      have accumulatedBudget : priorSteps+eventSteps≤((schedule.take (eventIndex+1)).map budget).sum := by
        rw [prefixBudget]
        exact Nat.add_le_add priorTrace.2 eventBudgetBound
      exact ⟨_,afterBoundary,priorSteps+eventSteps,Execution.snoc priorTrace.1 eventStep,accumulatedBudget⟩
    | child call =>
      have savedLedger := before.saved_ledger entryLedger
      obtain ⟨afterState,targetRetained,afterSettled,eventSteps,eventTimeBound,eventStep⟩ :=
        CompactComplexSourceReadyReachedEventStoppedFrameStep.stopped_child_frame_step phaseCoordinate entryPath activeFits pair
          packingLimit basisProgram basisConstant basisRuns headerStack liveStack call eventBound eventEquation before.state
          pcHeaderDistinct pcLiveDistinct headerLiveDistinct snapshot before.settled rfl rfl rfl activePositive childStopped
          axesFit childChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload
          parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
          initialLive nodeLeft (childExponent+2) savedLedger
      let afterBoundary : Boundary (eventIndex+1)
          (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)) :=
        advance before afterState targetRetained afterSettled
      have eventBudgetBound : eventSteps≤budget (Event.child call) := by
        simpa only [budget,eventBudget,stoppedBudget] using eventTimeBound
      have prefixBudget := budget_prefix_successor schedule budget eventIndex eventBound
      rw [eventEquation] at prefixBudget
      have accumulatedBudget : priorSteps+eventSteps≤((schedule.take (eventIndex+1)).map budget).sum := by
        rw [prefixBudget]
        exact Nat.add_le_add priorTrace.2 eventBudgetBound
      exact ⟨_,afterBoundary,priorSteps+eventSteps,Execution.snoc priorTrace.1 eventStep,accumulatedBudget⟩
  have initialTrace : Trace initialBoundary 0 :=
    ⟨Execution.nil,by simpa only [List.take_zero,List.map_nil,List.sum_nil] using (Nat.le_refl 0)⟩
  obtain ⟨finalLive,finalBoundary,elapsedSteps,actualTrace⟩ :=
    indexed_loop Boundary Trace schedule.length initialLive initialBoundary initialTrace actualNext
  have coverage := CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage actualTrace.1
  have terminalBudget := actualTrace.2
  rw [List.take_length] at terminalBudget
  have totalBound : elapsedSteps≤totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
      childRowsPositive parentSlots parentPacked := by
    simpa only [totalBudget,budget] using terminalBudget
  exact ⟨finalLive,finalBoundary,elapsedSteps,actualTrace.1,totalBound,coverage⟩

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedSchedule
