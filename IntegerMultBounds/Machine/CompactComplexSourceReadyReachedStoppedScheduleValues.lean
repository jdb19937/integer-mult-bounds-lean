module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedSchedule
public import IntegerMultBounds.Machine.CompactComplexEventInstructionPrefix
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarFrameStep
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedFrameStep

/-! An actual complete stopped-child schedule carries the original compiler's
full-network values on its very same terminal reached bank. Concrete event
routines simultaneously construct physical steps, semantic values, settled
frames and the immutable target. The actual summed event budget is retained. -/

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
open CompactComplexActualInterleavedNetwork (expand instructions)
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
  let Values : ∀ {eventIndex live},Boundary eventIndex live → Prop :=
    fun {eventIndex live} boundary =>
      ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
        stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
          live boundary.state.reached.data row polynomialIndex globalAnchor=
        Networks.FramedFactorExecution.run (expand (arity^(childExponent+1)) (schedule.take eventIndex))
          (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            initialLive initialState.reached.data row polynomialIndex globalAnchor)
  let Trace : ∀ {eventIndex live},Boundary eventIndex live → ℕ → Prop :=
    fun {eventIndex live} boundary elapsedSteps =>
      Execution basisProgram headerStack liveStack initialLive initialState boundary.state elapsedSteps ∧
      elapsedSteps≤((schedule.take eventIndex).map budget).sum ∧ Values boundary
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
        exact Nat.add_le_add priorTrace.2.1 eventBudgetBound
      have scalarValues := CompactComplexSourceReadyReachedEventScalarValues.scalar_state_values
        entryPath phaseCoordinate group eventBound eventEquation before.state afterState afterData
        activePositive precisionReserve (Nat.zero_le _) growthReserve (scalarChunkRoom group)
      have prefixValues : Values afterBoundary := by
        intro row polynomialIndex globalAnchor
        have prefixStep := CompactComplexEventInstructionPrefix.schedule_prefix_run_step
          (arity^(childExponent+1)) eventIndex eventBound
          (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            initialLive initialState.reached.data row polynomialIndex globalAnchor)
        rw [eventEquation] at prefixStep
        exact (scalarValues row polynomialIndex globalAnchor).trans
          ((congrArg (Networks.FramedFactorExecution.run (instructions (arity^(childExponent+1)) (Event.scalar group)))
            (priorTrace.2.2 row polynomialIndex globalAnchor)).trans prefixStep.symm)
      exact ⟨_,afterBoundary,priorSteps+eventSteps,Execution.snoc priorTrace.1 eventStep,accumulatedBudget,prefixValues⟩
    | child call =>
      have savedLedger := before.saved_ledger entryLedger
      obtain ⟨afterState,targetRetained,afterSettled,eventSteps,eventTimeBound,eventStep,childValues⟩ :=
        CompactComplexSourceReadyReachedEventStoppedFrameStep.stopped_child_frame_step_values phaseCoordinate entryPath activeFits pair
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
        exact Nat.add_le_add priorTrace.2.1 eventBudgetBound
      have prefixValues : Values afterBoundary := by
        intro row polynomialIndex globalAnchor
        have prefixStep := CompactComplexEventInstructionPrefix.schedule_prefix_run_step
          (arity^(childExponent+1)) eventIndex eventBound
          (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            initialLive initialState.reached.data row polynomialIndex globalAnchor)
        rw [eventEquation] at prefixStep
        exact (childValues row polynomialIndex globalAnchor).trans
          ((congrArg (Networks.FramedFactorExecution.run (instructions (arity^(childExponent+1)) (Event.child call)))
            (priorTrace.2.2 row polynomialIndex globalAnchor)).trans prefixStep.symm)
      exact ⟨_,afterBoundary,priorSteps+eventSteps,Execution.snoc priorTrace.1 eventStep,accumulatedBudget,prefixValues⟩
  have initialTrace : Trace initialBoundary 0 :=
    ⟨Execution.nil,by simpa only [List.take_zero,List.map_nil,List.sum_nil] using (Nat.le_refl 0),by
      intro row polynomialIndex globalAnchor
      exact (CompactComplexEventInstructionPrefix.prefix_run_zero (arity^(childExponent+1)) schedule _).symm⟩
  obtain ⟨finalLive,finalBoundary,elapsedSteps,actualTrace⟩ :=
    indexed_loop Boundary Trace schedule.length initialLive initialBoundary initialTrace actualNext
  have coverage := CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage actualTrace.1
  have terminalBudget := actualTrace.2.1
  rw [List.take_length] at terminalBudget
  have totalBound : elapsedSteps≤totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
      childRowsPositive parentSlots parentPacked := by
    simpa only [totalBudget,budget] using terminalBudget
  refine ⟨finalLive,finalBoundary,elapsedSteps,actualTrace.1,totalBound,coverage.1,coverage.2,?_⟩
  intro row polynomialIndex globalAnchor
  exact (actualTrace.2.2 row polynomialIndex globalAnchor).trans
    (CompactComplexEventInstructionPrefix.schedule_prefix_terminal (arity^(childExponent+1)) _)

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedScheduleValues
