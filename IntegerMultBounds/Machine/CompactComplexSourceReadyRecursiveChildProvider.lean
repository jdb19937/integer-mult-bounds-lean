module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildEvent
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingChildEntryPath

/-! The recursive child provider is an explicit induction interface with fixed
numerical budgets. Given certificates on any actual forwarded parent, the real
forward/entry program and complete nonleaf event execute without a supplied
prefix-execution or return-grid oracle. This module does not discharge the
provider at arbitrary recursion depth. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildProvider
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event childTarget)
open CompactComplexSourceReadyReachedEventTrace (State Step physicalBank)
open CompactComplexSourceReadyReachedEventFrameState (FrameState)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyCompletedNonleafChild (CompletedChild resultArray returnedBank)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Event
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
    parentLevels parentFrames parentReturned eventIndex parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    parentLevels parentFrames parentReturned)
  (activeFits : shape.active≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  {pcStack headerStack liveStack : Fin stackCount} {origin : ℤ} {savedCalls : List ComplexRecursiveCallSchema.Call}

/-- Recursive induction hypothesis on actual scheduled forward parent banks.
Budget functions are fixed parameters, rather than existential allowances. -/
def Provider
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (childSlots : ∀ call : ComplexRecursiveCallSchema.Call,
      (CompactComplexChildHeadersData.child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (childEventBudget childPathBudget : ComplexRecursiveCallSchema.Call → ℕ) : Prop :=
  ∀ (eventIndex parentLive : ℕ) (forwardBank : Tapes (nodeTapes stackCount roles) 2),
    ∀ forwardReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
      metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive parentLevels parentFrames
      (returnedCursor parentReturned eventIndex (arity^(childExponent+1)))
      (CompactComplexActualScalarOrdinal.scalarGroups (schedule.take eventIndex)).length parentLive pcStack origin savedCalls forwardBank,
    ∀ (call : ComplexRecursiveCallSchema.Call) (eventBound : eventIndex<schedule.length)
      (eventEquation : schedule[eventIndex]=Event.child call)
      (childNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false)
      (snapshot : Snapshot stackCount) (forwardSettled : Settled snapshot forwardReached.storage forwardReached.aux)
      (snapshotHeaderStack : snapshot.headerStack=headerStack) (snapshotLiveStack : snapshot.liveStack=liveStack)
      (snapshotPcStack : snapshot.pcStack=pcStack)
      (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack),
    Nonempty (CompletedChild (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair forwardReached call basisProgram (childSlots call) childRowsDivisible
      (childEventBudget call) (childPathBudget call))

section Costs
variable (packingLimit : ℕ) (guardPositive : 1≤ shape.guard) (guardFitsChunk : shape.guard+1≤ shape.chunk)
  (childRowsPositive : 0<parentRows/roles)
  (parentSlots : (parent phaseCoordinate parentPath.visit activeFits pair).slots=25^3)
  (parentPacked : ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate parentPath.visit activeFits pair).slots),
    1<(parent phaseCoordinate parentPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
    (ActivePrefixStagePairData.changePair
      (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
        (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)

/-- The same original basis program's paid selected forward or inverse pass. -/
def basisCost (call : ComplexRecursiveCallSchema.Call) (reverse : Bool) :=
  let stage := parent phaseCoordinate parentPath.visit activeFits pair
  let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (parentRows/roles)
    polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive
  let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput polynomialExponent
    (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots (CompactComplexRolePhaseSite.pc call.site) reverse
      (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent) (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
  CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent metadataPrecision passTime

/-- Actual forward basis, child-entry body, and their two paid table joins. -/
def forwardBudget (call : ComplexRecursiveCallSchema.Call) :=
  basisCost phaseCoordinate parentPath activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked call false+1+
    CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) parentRows polynomialExponent metadataPrecision+1

/-- Actual restoration, inverse basis, and their paid return/table joins. -/
def returnBudget (call : ComplexRecursiveCallSchema.Call) :=
  CompactComplexSourceReadyChildReturnPath.timeConstant roles*CompactNativeRoleTransferBudget.volume parentRows shape polynomialExponent metadataPrecision+1+
    basisCost phaseCoordinate parentPath activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked call true+1

/-- Complete parent event cost under the fixed recursive child path budget. -/
def eventBudget (childPathBudget : ComplexRecursiveCallSchema.Call → ℕ) (call : ComplexRecursiveCallSchema.Call) :=
  forwardBudget phaseCoordinate parentPath activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked call+
    (childPathBudget call+returnBudget phaseCoordinate parentPath activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked call)

end Costs

theorem step
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (call : ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (childNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false)
    (snapshot : Snapshot stackCount) (savedTarget : ℕ)
    (before : FrameState (stage:=parent phaseCoordinate parentPath.visit activeFits pair) (rowCount:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=parentLevels) (frameVolume:=parentFrames)
      (entryReturned:=parentReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) snapshot savedTarget eventIndex parentLive)
    (guardPositive : 1≤ shape.guard) (guardFitsChunk : shape.guard+1≤ shape.chunk) (childRowsPositive : 0<parentRows/roles)
    (parentSlots : (parent phaseCoordinate parentPath.visit activeFits pair).slots=25^3)
    (childSlots : ∀ call : ComplexRecursiveCallSchema.Call,
      (CompactComplexChildHeadersData.child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (childEventBudget childPathBudget : ComplexRecursiveCallSchema.Call → ℕ)
    (provider : Provider (parentRows:=parentRows) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant)
      (baselineLive:=baselineLive) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair basisProgram childSlots childRowsDivisible childEventBudget childPathBudget)
    (snapshotHeaderStack : snapshot.headerStack=headerStack) (snapshotLiveStack : snapshot.liveStack=liveStack)
    (snapshotPcStack : snapshot.pcStack=pcStack)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (rowsPositive : 0<parentRows) (rolesDivideRows : roles∣parentRows)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) (activePositive : 0<shape.active) (unitPayload : shape.payload=1)
    (precisionReserve : baselinePrecision+2*shape.bits≤ metadataPrecision) (baselineFits : baselineLive≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤ shape.chunk)
    (axesFit : 0+2*arity^(childExponent+1)≤ shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤ shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedTargetLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      before.state.reached.targetValue ledgerLeft ledgerExponent)
    (parentPacked : ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate parentPath.visit activeFits pair).slots),
      1<(parent phaseCoordinate parentPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
          (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) :
    ∃ after : FrameState (stage:=parent phaseCoordinate parentPath.visit activeFits pair) (rowCount:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=parentLevels) (frameVolume:=parentFrames)
      (entryReturned:=parentReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) snapshot savedTarget (eventIndex+1)
        (childTarget (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) parentLive (childExponent+1)),
      ∃ elapsedSteps≤ eventBudget phaseCoordinate parentPath activeFits pair packingLimit guardPositive guardFitsChunk
        childRowsPositive parentSlots parentPacked childPathBudget call,
        Step basisProgram headerStack liveStack before.state after.state elapsedSteps ∧
        ∀ (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
          stored phaseCoordinate parentPath.visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            (childTarget (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) parentLive (childExponent+1))
            after.state.reached.data row polynomialIndex globalAnchor=
          FramedFactorExecution.run [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
            (stored phaseCoordinate parentPath.visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
              parentLive before.state.reached.data row polynomialIndex globalAnchor) := by
  have occurrenceEquation : schedule.get (⟨eventIndex,eventBound⟩ : Fin schedule.length)=Event.child call := by
    simpa only [List.get_eq_getElem] using eventEquation
  obtain ⟨forwardReached,forwardData,forwardTarget,_basisTimeBound,entryElapsed,entryTimeBound,entryExecution⟩ :=
    CompactComplexAlignedSiblingChildEntryPath.child_paths phaseCoordinate parentPath activeFits pair
      headerStack pcStack liveStack origin savedCalls before.state.bank (⟨eventIndex,eventBound⟩ : Fin schedule.length)
      before.state.reached call packingLimit basisProgram basisConstant basisRuns occurrenceEquation pcHeaderDistinct pcLiveDistinct
      guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked
      precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive ledgerLive ledgerLeft ledgerExponent savedTargetLedger
  have forwardFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields forwardReached _ before.state.reached.aux rfl
  have forwardStorage : forwardReached.storage=before.state.reached.storage := by
    simpa only [replacementCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using forwardFields.1
  have forwardSettled : Settled snapshot forwardReached.storage forwardReached.aux := by
    rw [forwardStorage,forwardFields.2]
    exact before.settled
  obtain ⟨certificate⟩ := provider eventIndex parentLive _ forwardReached call eventBound eventEquation childNonstopped
    snapshot forwardSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack headerLiveDistinct pcHeaderDistinct pcLiveDistinct
  have entryExecutionActual : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (CompactComplexScheduledPCLayout.eventPC ⟨eventIndex,eventBound⟩) (physicalBank before.state) entryElapsed
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
      (CompactComplexAlignedBoundaryPaths.alignedBank
        ((CompactComplexSourceReadyWorkspace.ready
          (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
            forwardReached call headerStack liveStack)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) := entryExecution
  obtain ⟨afterState,targetRetained,settled,elapsedSteps,timeBound,actualStep,exactValues⟩ :=
    CompactComplexSourceReadyCompletedNonleafChildEvent.step phaseCoordinate parentPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns call eventBound eventEquation childNonstopped before.state
      guardPositive guardFitsChunk childRowsPositive parentSlots forwardReached forwardData forwardTarget (childSlots call)
      childRowsDivisible certificate entryElapsed
      (forwardBudget phaseCoordinate parentPath activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked call)
      entryTimeBound entryExecutionActual snapshot before.settled snapshotHeaderStack snapshotLiveStack snapshotPcStack
      headerLiveDistinct pcHeaderDistinct pcLiveDistinct rowsPositive rolesDivideRows axesPositive chunkPositive activePositive
      unitPayload precisionReserve baselineFits growthReserve denominatorRoom axesFit chunkRoom ledgerLive ledgerLeft ledgerExponent
      savedTargetLedger parentPacked
  let after := CompactComplexSourceReadyReachedEventFrameState.advance before afterState targetRetained settled
  refine ⟨after,elapsedSteps,timeBound,actualStep,exactValues⟩

end Event
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildProvider
