module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildProvider
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedSchedule
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedScheduleValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventFrameState
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventScalarFrameStep
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedFrameStep

/-! The actual mixed scalar and recursive child schedule. Scalar and stopped
steps use their original routines; nonstopped steps invoke a named recursive
completed-child induction hypothesis on the real forward entry. The original
ancestor frame, target and exact sum of paid event budgets are retained. This
theorem does not supply the induction hypothesis or assert all-depth existence. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedRecursiveSchedule
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

def eventBudget (packingLimit : ℕ) (childPathBudget : Networks.ComplexRecursiveCallSchema.Call → ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) : Event → ℕ
  | .scalar group => scalarBudget (shape:=shape) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) group
  | .child call =>
    if Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then
      stoppedBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
        childRowsPositive parentSlots parentPacked call
    else CompactComplexSourceReadyRecursiveChildProvider.eventBudget phaseCoordinate entryPath activeFits pair
      packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked childPathBudget call

def totalBudget (packingLimit : ℕ) (childPathBudget : Networks.ComplexRecursiveCallSchema.Call → ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) :=
  (schedule.map (eventBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget guardPositive guardFitsChunk
    childRowsPositive parentSlots parentPacked)).sum

attribute [local irreducible] scalarBudget stoppedBudget eventBudget totalBudget
  CompactComplexSourceReadyRecursiveChildProvider.basisCost
  CompactComplexSourceReadyRecursiveChildProvider.forwardBudget
  CompactComplexSourceReadyRecursiveChildProvider.returnBudget
  CompactComplexSourceReadyRecursiveChildProvider.eventBudget

/-- One actual schedule cursor retains the original captured ancestor and target. -/
def Boundary (headerStack liveStack : Fin stackCount)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
    (eventIndex live : ℕ) : Type :=
  FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
    (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
    (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
    (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
    (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
    initialState.reached.targetValue eventIndex live

/-- Paid execution and original compiler-prefix values, with the event cost
function kept symbolic while each concrete branch is kernel checked. -/
def Trace (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
    (budget : Event → ℕ) {eventIndex live : ℕ}
    (boundary : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState eventIndex live)
    (elapsedSteps : ℕ) : Prop :=
  Execution basisProgram headerStack liveStack initialLive initialState boundary.state elapsedSteps ∧
    elapsedSteps≤((schedule.take eventIndex).map budget).sum ∧
    CompactComplexSourceReadyReachedScheduleValues.PrefixValues phaseCoordinate entryPath.visit initialState boundary.state

/-- Append one actual paid step and its exact local values without expanding
any concrete routine, stage cost or recursive child certificate. -/
theorem extend_trace (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
    (budget : Event → ℕ) {eventIndex sourceLive targetLive priorSteps eventSteps : ℕ}
    (before : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState eventIndex sourceLive)
    (after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState (eventIndex+1) targetLive)
    (eventBound : eventIndex<schedule.length)
    (priorTrace : Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget before priorSteps)
    (actualStep : Step basisProgram headerStack liveStack before.state after.state eventSteps)
    (localBudget : eventSteps≤budget schedule[eventIndex])
    (localValues : ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
      stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
        targetLive after.state.reached.data row polynomialIndex globalAnchor=
      Networks.FramedFactorExecution.run (instructions (arity^(childExponent+1)) schedule[eventIndex])
        (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
          sourceLive before.state.reached.data row polynomialIndex globalAnchor)) :
    Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget after
      (priorSteps+eventSteps) := by
  unfold Trace at priorTrace ⊢
  have prefixBudget := budget_prefix_successor schedule budget eventIndex eventBound
  refine ⟨Execution.snoc priorTrace.1 actualStep,?_,?_⟩
  · rw [prefixBudget]
    exact Nat.add_le_add priorTrace.2.1 localBudget
  · exact CompactComplexSourceReadyReachedScheduleValues.successor phaseCoordinate entryPath.visit
      initialState before.state after.state eventBound priorTrace.2.2 localValues

attribute [local irreducible] Trace

section Runtime
variable
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
    (axesFit : 0+2*arity^(childExponent+1)≤shape.bits)
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
    (childSlots : ∀ call : Networks.ComplexRecursiveCallSchema.Call,
      (CompactComplexChildHeadersData.child phaseCoordinate entryPath.visit activeFits pair call.slot).slots=arity)
    (childRowsDivisible : roles∣rowCount/roles)
    (childEventBudget childPathBudget : Networks.ComplexRecursiveCallSchema.Call → ℕ)
    (provider : CompactComplexSourceReadyRecursiveChildProvider.Provider
      (parentRows:=rowCount) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate entryPath activeFits pair basisProgram childSlots childRowsDivisible childEventBudget childPathBudget)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)

include basisRuns pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails activePositive axesFit
  childChunkRoom scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows
  unitPayload parentSlots parentPacked childSlots childRowsDivisible childEventBudget childPathBudget provider
  precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive packingLimit basisConstant

/-- The concrete scalar routine extends the named execution trace. -/
theorem scalar_successor
    (budget : Event → ℕ) {eventIndex sourceLive priorSteps : ℕ}
    (before : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState eventIndex sourceLive)
    (priorTrace : Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget before priorSteps)
    (eventBound : eventIndex<schedule.length)
    (group : GroupIndex) (eventEquation : schedule[eventIndex]=Event.scalar group)
    (budgetEquation : budget (Event.scalar group)=scalarBudget (shape:=shape) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision) group) :
    ∃ targetLive,∃ after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState
      (eventIndex+1) targetLive,∃ totalSteps,
      Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget after totalSteps := by
  obtain ⟨afterState,afterData,targetRetained,afterSettled,eventSteps,eventTimeBound,eventStep⟩ :=
    CompactComplexSourceReadyReachedEventScalarFrameStep.scalar_step basisProgram entryPath headerStack liveStack
      group eventBound eventEquation before.state (capture initialState headerStack liveStack) before.settled
      childRowsPositive (by omega) chunkPositive activePositive precisionReserve (Nat.zero_le _)
      (scalarChunkRoom group) growthReserve baselineFits denominatorRoom
  let after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState
      (eventIndex+1) (sourceLive+(block group).length) := advance before afterState targetRetained afterSettled
  have paid : eventSteps≤budget schedule[eventIndex] := by
    rw [eventEquation,budgetEquation]
    simpa only [scalarBudget] using eventTimeBound
  have scalarValues := CompactComplexSourceReadyReachedEventScalarValues.scalar_state_values
    entryPath phaseCoordinate group eventBound eventEquation before.state afterState afterData
    activePositive precisionReserve (Nat.zero_le _) growthReserve (scalarChunkRoom group)
  refine ⟨_,after,priorSteps+eventSteps,extend_trace phaseCoordinate entryPath activeFits pair
    basisProgram headerStack liveStack initialState budget before after eventBound priorTrace eventStep paid ?_⟩
  dsimp only [after,advance]
  rw [eventEquation]
  exact scalarValues

/-- The concrete stopped-child routine extends the named execution trace. -/
theorem stopped_successor
    (budget : Event → ℕ) {eventIndex sourceLive priorSteps : ℕ}
    (before : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState eventIndex sourceLive)
    (priorTrace : Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget before priorSteps)
    (eventBound : eventIndex<schedule.length)
    (call : Networks.ComplexRecursiveCallSchema.Call) (eventEquation : schedule[eventIndex]=Event.child call)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (entryLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision initialLive
      initialState.reached.targetValue nodeLeft (childExponent+2))
    (budgetEquation : budget (Event.child call)=stoppedBudget phaseCoordinate entryPath activeFits pair
      packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked call) :
    ∃ targetLive,∃ after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState
      (eventIndex+1) targetLive,∃ totalSteps,
      Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget after totalSteps := by
  have savedLedger := before.saved_ledger entryLedger
  obtain ⟨afterState,targetRetained,afterSettled,eventSteps,eventTimeBound,eventStep,childValues⟩ :=
    CompactComplexSourceReadyReachedEventStoppedFrameStep.stopped_child_frame_step_values phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack call eventBound eventEquation before.state
      pcHeaderDistinct pcLiveDistinct headerLiveDistinct (capture initialState headerStack liveStack) before.settled
      rfl rfl rfl activePositive childStopped (by omega) childChunkRoom guardPositive guardFitsChunk rowsPositive
      childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve
      denominatorRoom axesPositive chunkPositive initialLive nodeLeft (childExponent+2) savedLedger
  let after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState
      (eventIndex+1) (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1))
        sourceLive (childExponent+1)) := advance before afterState targetRetained afterSettled
  have paid : eventSteps≤budget schedule[eventIndex] := by
    rw [eventEquation,budgetEquation]
    simpa only [stoppedBudget] using eventTimeBound
  refine ⟨_,after,priorSteps+eventSteps,extend_trace phaseCoordinate entryPath activeFits pair
    basisProgram headerStack liveStack initialState budget before after eventBound priorTrace eventStep paid ?_⟩
  dsimp only [after,advance]
  rw [eventEquation]
  exact childValues

/-- The actual recursive provider and parent return extend the named trace. -/
theorem nonstopped_successor
    (budget : Event → ℕ) {eventIndex sourceLive priorSteps : ℕ}
    (before : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState eventIndex sourceLive)
    (priorTrace : Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget before priorSteps)
    (eventBound : eventIndex<schedule.length)
    (call : Networks.ComplexRecursiveCallSchema.Call) (eventEquation : schedule[eventIndex]=Event.child call)
    (childNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false)
    (entryLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision initialLive
      initialState.reached.targetValue nodeLeft (childExponent+2))
    (budgetEquation : budget (Event.child call)=CompactComplexSourceReadyRecursiveChildProvider.eventBudget
      phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive
      parentSlots parentPacked childPathBudget call) :
    ∃ targetLive,∃ after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState
      (eventIndex+1) targetLive,∃ totalSteps,
      Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget after totalSteps := by
  have savedLedger := before.saved_ledger entryLedger
  obtain ⟨after,eventSteps,eventTimeBound,eventStep,childValues⟩ :=
    CompactComplexSourceReadyRecursiveChildProvider.step (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate entryPath activeFits pair packingLimit basisProgram basisConstant basisRuns call eventBound eventEquation
      childNonstopped (capture initialState headerStack liveStack) initialState.reached.targetValue before
      guardPositive guardFitsChunk childRowsPositive parentSlots childSlots childRowsDivisible childEventBudget childPathBudget provider
      rfl rfl rfl headerLiveDistinct pcHeaderDistinct pcLiveDistinct rowsPositive rolesDivideRows axesPositive chunkPositive
      activePositive unitPayload precisionReserve baselineFits growthReserve denominatorRoom axesFit childChunkRoom
      initialLive nodeLeft (childExponent+2) savedLedger parentPacked
  have paid : eventSteps≤budget schedule[eventIndex] := by
    rw [eventEquation,budgetEquation]
    exact eventTimeBound
  refine ⟨_,after,priorSteps+eventSteps,extend_trace phaseCoordinate entryPath activeFits pair
    basisProgram headerStack liveStack initialState budget before after eventBound priorTrace eventStep paid ?_⟩
  rw [eventEquation]
  exact childValues

/-- Only the original event and stopping classifier choose the proved branch. -/
theorem event_successor {eventIndex sourceLive priorSteps : ℕ}
    (before : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState eventIndex sourceLive)
    (priorTrace : Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState
        (eventBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked) before priorSteps)
    (eventBound : eventIndex<schedule.length)
    (entryLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision initialLive
        initialState.reached.targetValue nodeLeft (childExponent+2))
 :
    ∃ targetLive,∃ after : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState
        (eventIndex+1) targetLive,∃ totalSteps,
        Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState
        (eventBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked) after totalSteps := by
  cases eventEquation : schedule[eventIndex] with
  | scalar group =>
    exact scalar_successor phaseCoordinate entryPath activeFits pair packingLimit basisProgram basisConstant basisRuns headerStack liveStack
        initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails activePositive axesFit childChunkRoom
        scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked
        childSlots childRowsDivisible childEventBudget childPathBudget provider precisionReserve baselineFits growthReserve denominatorRoom
        axesPositive chunkPositive
        _ before priorTrace eventBound group eventEquation (by simp only [eventBudget])
  | child call =>
    by_cases childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true
    · exact stopped_successor phaseCoordinate entryPath activeFits pair packingLimit basisProgram basisConstant basisRuns headerStack liveStack
        initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails activePositive axesFit childChunkRoom
        scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked
        childSlots childRowsDivisible childEventBudget childPathBudget provider precisionReserve baselineFits growthReserve denominatorRoom
        axesPositive chunkPositive
        _ before priorTrace eventBound call eventEquation childStopped entryLedger
        (by simp only [eventBudget,childStopped,ite_true])
    · have childNonstopped := Bool.eq_false_of_not_eq_true childStopped
      exact nonstopped_successor phaseCoordinate entryPath activeFits pair packingLimit basisProgram basisConstant basisRuns headerStack liveStack
        initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails activePositive axesFit childChunkRoom
        scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked
        childSlots childRowsDivisible childEventBudget childPathBudget provider precisionReserve baselineFits growthReserve denominatorRoom
        axesPositive chunkPositive
        _ before priorTrace eventBound call eventEquation childNonstopped entryLedger
        (by simp only [eventBudget,childNonstopped,Bool.false_eq_true,ite_false])

/-- The actual mixed schedule exists under its explicit recursive induction
hypothesis, retaining exact paid time and original full-network semantics. -/
theorem exists_execution_values :

    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
        elapsedSteps≤totalBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget guardPositive guardFitsChunk
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
  let budget := eventBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked
  let initialBoundary : Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState 0 initialLive :=
    captured initialState headerStack liveStack initialProtectedTails
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
  have initialTrace : Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState
      budget initialBoundary 0 := by
    unfold Trace
    refine ⟨Execution.nil,?_,
      CompactComplexSourceReadyReachedScheduleValues.initial phaseCoordinate entryPath.visit initialState⟩
    simp only [List.take_zero,List.map_nil,List.sum_nil]
    exact Nat.le_refl 0
  obtain ⟨finalLive,finalBoundary,elapsedSteps,actualTrace⟩ := indexed_loop
    (Boundary phaseCoordinate entryPath activeFits pair headerStack liveStack initialState)
    (Trace phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack initialState budget)
    schedule.length initialLive initialBoundary initialTrace
    (fun eventIndex sourceLive before priorSteps priorTrace eventBound =>
      event_successor phaseCoordinate entryPath activeFits pair packingLimit basisProgram basisConstant basisRuns headerStack liveStack
      initialState pcHeaderDistinct pcLiveDistinct headerLiveDistinct initialProtectedTails activePositive axesFit childChunkRoom
      scalarChunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked
      childSlots childRowsDivisible childEventBudget childPathBudget provider precisionReserve baselineFits growthReserve denominatorRoom
      axesPositive chunkPositive
        before priorTrace eventBound entryLedger)
  unfold Trace at actualTrace
  have coverage := CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage actualTrace.1
  have terminalBudget := actualTrace.2.1
  rw [List.take_length] at terminalBudget
  have totalBound : elapsedSteps≤totalBudget phaseCoordinate entryPath activeFits pair packingLimit childPathBudget
      guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked := by
    simpa only [totalBudget,budget] using terminalBudget
  refine ⟨finalLive,finalBoundary,elapsedSteps,actualTrace.1,totalBound,coverage.1,coverage.2,?_⟩
  exact CompactComplexSourceReadyReachedScheduleValues.terminal phaseCoordinate entryPath.visit
    initialState finalBoundary.state actualTrace.2.2

end Runtime
end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedRecursiveSchedule
