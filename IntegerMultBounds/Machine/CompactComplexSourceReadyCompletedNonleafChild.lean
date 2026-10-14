module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnRun
public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildSnapshotTransport

/-! A completed nonleaf child certificate stores the actual node execution
and tensor identity once. Its returned bank and result array are definitions of
the same terminal frame, not independent witnesses. Target, progress and actual
captured-frame settlement are derived from this execution certificate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChild
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadyCompletedChildBoundary (completed result)
open CompactComplexAlignedPoppedReturnReadiness (popped)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexCompletedLiveLower (schedule Event)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (address)
open Networks
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexRolePhaseSite.roleEncoding
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

section Parent
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
    parentLevels parentFrames parentReturned eventIndex parentPrefix parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    parentLevels parentFrames parentReturned)
  (activeFits : shape.active≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  {pcStack headerStack liveStack : Fin stackCount} {origin : ℤ} {savedCalls : List ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
    metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive parentLevels parentFrames
    (returnedCursor parentReturned eventIndex (arity^(childExponent+1))) parentPrefix parentLive pcStack origin savedCalls parentBank)
  (call : ComplexRecursiveCallSchema.Call)
  (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
/-- Share the actual indexed State type without expanding its full bank invariant. -/
def ChildState (eventIndexValue liveValue : ℕ) :=
  State (stage:=child phaseCoordinate parentPath.visit activeFits pair call.slot)
    (rowCount:=parentRows/roles) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=parentLevels+1) (frameVolume:=parentFrames+arity^(childExponent+2))
    (entryReturned:=parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1))
    (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls) eventIndexValue liveValue

/-- Share the terminal frame type with its genuine captured initial State. -/
def ChildBoundary
    (initialChild : ChildState (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      phaseCoordinate parentPath activeFits pair call 0 parentLive) (finalLive : ℕ) :=
  FrameState (stage:=child phaseCoordinate parentPath.visit activeFits pair call.slot)
    (rowCount:=parentRows/roles) (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=parentLevels+1) (frameVolume:=parentFrames+arity^(childExponent+2))
    (entryReturned:=parentReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1))
    (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=call::savedCalls)
    (capture initialChild headerStack liveStack) initialChild.reached.targetValue schedule.length finalLive

/-- Literal initial corrected-entry condition, shared by the result fields. -/
def EntryCondition
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (initialChild : ChildState (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      phaseCoordinate parentPath activeFits pair call 0 parentLive)
    : Prop :=
  initialChild.bank=canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent
        (child phaseCoordinate parentPath.visit activeFits pair call.slot) childSlots (parentRows/roles)
        polynomialExponent metadataPrecision parentLive childExponent childRowsDivisible
        (CompactComplexSourceReadyOrientationInvariants.oriented call (selectedArray parentReached call))
        (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        parentReached.scalar
        (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
        (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack))
      (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)

/-- Actual classifier-through-saved-return path on the computed terminal bank. -/
def PhysicalCondition
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (initialChild : ChildState (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      phaseCoordinate parentPath activeFits pair call 0 parentLive)
    {finalLive : ℕ}
    (finalBoundary : ChildBoundary (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      (parentLive:=parentLive) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair call initialChild finalLive)
    (older : ℤ → Fin 6) (top : ℤ) (elapsedSteps : ℕ) : Prop :=
  CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
    (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
    (CompactComplexAlignedBoundaryPaths.alignedBank
      ((CompactComplexSourceReadyWorkspace.ready
        (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
          parentReached call headerStack liveStack)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))
    elapsedSteps (CompactComplexScheduledPCDecode.savedPC call)
    (CompactComplexAlignedBoundaryPaths.alignedBank
      ((CompactComplexSourceReadyWorkspace.ready
        (popped (completed finalBoundary.state.reached childSlots childRowsDivisible call) pcStack older top)).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))

/-- Directional tensor semantics of the same computed terminal result. -/
def TensorCondition
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (initialChild : ChildState (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      phaseCoordinate parentPath activeFits pair call 0 parentLive)
    {finalLive : ℕ}
    (finalBoundary : ChildBoundary (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      (parentLive:=parentLive) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair call initialChild finalLive) : Prop :=
  ∀ (rawRow : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      nativeField (metadataPrecision-2*shape.bits) (parentLive+2*arity^(childExponent+1))
        (result finalBoundary.state.reached childSlots childRowsDivisible call) rawRow polynomialIndex globalAnchor=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^childExponent)).symm
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor
          (nativeField (metadataPrecision-2*shape.bits) parentLive (selectedArray parentReached call) rawRow polynomialIndex))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor)
      else ComplexEndpoints.fullFrame (arity^childExponent)
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor
          (nativeField (metadataPrecision-2*shape.bits) parentLive (selectedArray parentReached call) rawRow polynomialIndex))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentPath.visit call) globalAnchor)

section Certificate

/-- Actual internal execution, represented with already compiled dependent
pairs so no large custom recursor is generated. Named methods hide this layout. -/
def TraceWitness
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (childRowsDivisible : roles∣parentRows/roles) (eventBudget : ℕ) :=
  Σ initialChild : ChildState (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      phaseCoordinate parentPath activeFits pair call 0 parentLive,
  Σ finalLive : ℕ,
  Σ finalBoundary : ChildBoundary (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      (parentLive:=parentLive) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair call initialChild finalLive,
  Σ eventElapsed : ℕ,
    PLift (Execution basisProgram headerStack liveStack parentLive initialChild finalBoundary.state eventElapsed ∧
      eventElapsed≤eventBudget ∧ EntryCondition (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call childSlots childRowsDivisible initialChild)

namespace TraceWitness
variable {childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity}
  {childRowsDivisible : roles∣parentRows/roles} {eventBudget : ℕ}
  (trace : TraceWitness (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget)

def initialChild := trace.1

def finalLive := trace.2.1

def finalBoundary := trace.2.2.1

def eventElapsed := trace.2.2.2.1

theorem childTrace : Execution basisProgram headerStack liveStack parentLive trace.initialChild trace.finalBoundary.state trace.eventElapsed :=
  trace.2.2.2.2.down.1

theorem eventTimeBound : trace.eventElapsed≤eventBudget := trace.2.2.2.2.down.2.1

theorem initialEntryBank : EntryCondition (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call childSlots childRowsDivisible trace.initialChild :=
  trace.2.2.2.2.down.2.2

/-- Named construction API for the internal execution certificate. -/
def make
    (initialChild : ChildState (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      phaseCoordinate parentPath activeFits pair call 0 parentLive) (finalLive : ℕ)
    (finalBoundary : ChildBoundary (stackCount:=stackCount) (shape:=shape) (parentRows:=parentRows)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (baselineLive:=baselineLive)
      (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls)
      (parentLive:=parentLive) (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair call initialChild finalLive) (eventElapsed : ℕ)
    (childTrace : Execution basisProgram headerStack liveStack parentLive initialChild finalBoundary.state eventElapsed)
    (eventTimeBound : eventElapsed≤eventBudget)
    (initialEntryBank : EntryCondition (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call childSlots childRowsDivisible initialChild) :
    TraceWitness (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget :=
  ⟨initialChild,finalLive,finalBoundary,eventElapsed,⟨⟨childTrace,eventTimeBound,initialEntryBank⟩⟩⟩

end TraceWitness

/-- The public completed-child certificate uses already compiled dependent
pairs internally; named projections and make keep this layout out of its API. -/
def CompletedChild
    (childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity)
    (childRowsDivisible : roles∣parentRows/roles) (eventBudget pathBudget : ℕ) :=
  Σ traceWitness : TraceWitness (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget,
  Σ older : ℤ → Fin 6,
  Σ top : ℤ,
  Σ elapsedSteps : ℕ,
    PLift (CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls older top ∧
      elapsedSteps≤pathBudget ∧ PhysicalCondition (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots
    childRowsDivisible traceWitness.initialChild traceWitness.finalBoundary older top elapsedSteps ∧ TensorCondition (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call childSlots
    childRowsDivisible traceWitness.initialChild traceWitness.finalBoundary)

end Certificate

variable {childSlots : (child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=NativeEndpointCharacterRoles.arity}
  {childRowsDivisible : roles∣parentRows/roles} {eventBudget pathBudget : ℕ}
  (completion : CompletedChild (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call basisProgram
    childSlots childRowsDivisible eventBudget pathBudget)

namespace CompletedChild

/-- Named projection of the actual internal node execution. -/
def traceWitness := completion.1

def older := completion.2.1

def top := completion.2.2.1

def elapsedSteps := completion.2.2.2.1

theorem olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls completion.older completion.top :=
  completion.2.2.2.2.down.1

theorem pathTimeBound : completion.elapsedSteps≤pathBudget := completion.2.2.2.2.down.2.1

theorem physical : PhysicalCondition (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible
    completion.traceWitness.initialChild completion.traceWitness.finalBoundary completion.older completion.top completion.elapsedSteps :=
  completion.2.2.2.2.down.2.2.1

theorem actualChildTensor : TensorCondition (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call childSlots childRowsDivisible
    completion.traceWitness.initialChild completion.traceWitness.finalBoundary := completion.2.2.2.2.down.2.2.2

/-- Named construction combines the same execution, popped endpoint and
actual tensor result, without independently chosen banks or arrays. -/
def make
    (traceWitness : TraceWitness (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget)
    (older : ℤ → Fin 6) (top : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls older top)
    (elapsedSteps : ℕ) (pathTimeBound : elapsedSteps≤pathBudget)
    (physical : PhysicalCondition (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots
    childRowsDivisible traceWitness.initialChild traceWitness.finalBoundary older top elapsedSteps)
    (actualChildTensor : TensorCondition (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair parentReached call childSlots
    childRowsDivisible traceWitness.initialChild traceWitness.finalBoundary) :
    CompletedChild (headerStack:=headerStack) (liveStack:=liveStack)
      phaseCoordinate parentPath activeFits pair parentReached call basisProgram childSlots childRowsDivisible eventBudget pathBudget :=
  ⟨traceWitness,older,top,elapsedSteps,⟨⟨olderAssociated,pathTimeBound,physical,actualChildTensor⟩⟩⟩

/-- Public projection through the small internal execution witness. -/
def initialChild := completion.traceWitness.initialChild

def finalLive := completion.traceWitness.finalLive

def finalBoundary := completion.traceWitness.finalBoundary

def eventElapsed := completion.traceWitness.eventElapsed

theorem childTrace : Execution basisProgram headerStack liveStack parentLive completion.initialChild completion.finalBoundary.state completion.eventElapsed :=
  completion.traceWitness.childTrace

theorem eventTimeBound : completion.eventElapsed≤eventBudget := completion.traceWitness.eventTimeBound

theorem initialEntryBank : EntryCondition (headerStack:=headerStack) (liveStack:=liveStack)
    phaseCoordinate parentPath activeFits pair parentReached call childSlots childRowsDivisible completion.initialChild :=
  completion.traceWitness.initialEntryBank

/-- The literal directional array computed by the terminal node frame. -/
def resultArray := result completion.finalBoundary.state.reached childSlots childRowsDivisible call

/-- The literal completed bank with that execution's actual saved-PC pop. -/
def returnedBank := popped (completed completion.finalBoundary.state.reached childSlots childRowsDivisible call)
  pcStack completion.older completion.top

/-- Actual original target descriptor plus retained frame proves the exact
returned target; no target-value assertion is a constructor field. -/
theorem terminal_target : completion.finalBoundary.state.reached.targetValue=parentLive+2*arity^(childExponent+1) := by
  have originalTarget := CompactComplexSourceReadyReachedEntryTarget.target_of_corrected_entry
    completion.initialChild.reached childSlots parentLive childExponent childRowsDivisible
    (CompactComplexSourceReadyOrientationInvariants.oriented call (selectedArray parentReached call))
    (CompactComplexSourceReadyRecursiveChildReadiness.childControl phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildReadiness.childQueue phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    parentReached.scalar
    (CompactComplexSourceReadyRecursiveChildReadiness.childTail phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childStorage phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    (CompactComplexSourceReadyRecursiveChildCleanTails.childAuxiliary phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack)
    completion.initialEntryBank
  exact completion.finalBoundary.targetRetained.trans originalTarget

/-- Genuine schedule execution derives both true-live ledgers and coverage. -/
def progress
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (precisionReserve : baselinePrecision+2*shape.bits≤ metadataPrecision) (baselineFits : baselineLive≤ baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤ shape.chunk) :
    CompactComplexChildAlignmentBudget.Progress shape metadataPrecision parentLive completion.finalLive
      (parentLive+2*arity^(childExponent+1)) :=
  CompactComplexSourceReadyReachedNonleafProgress.progress parentPath call parentReached completion.childTrace
    eventBound eventEquation precisionReserve baselineFits denominatorRoom

/-- The same terminal frame settles against its actual captured original
child-entry bank, after the physical source correction is accounted for. -/
theorem completed_settled
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack) (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack)
    (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) :
    Settled (CompactComplexSourceReadyCapturedChildFrames.snapshot phaseCoordinate parentPath.visit activeFits pair
      parentReached call headerStack liveStack) completion.finalBoundary.state.reached.storage completion.finalBoundary.state.reached.aux := by
  exact CompactComplexSourceReadyRecursiveChildSnapshotTransport.settled_on_actual_child_snapshot
    phaseCoordinate parentPath activeFits pair parentReached call headerStack liveStack ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerLiveDistinct pcHeaderDistinct pcLiveDistinct
    completion.initialChild.reached childSlots childRowsDivisible completion.initialEntryBank
    completion.finalBoundary.state.reached.storage completion.finalBoundary.state.reached.aux completion.finalBoundary.settled

end CompletedChild

export CompletedChild (resultArray returnedBank terminal_target progress completed_settled)

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChild
