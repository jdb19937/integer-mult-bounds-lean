module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedFinalizationReadiness
public import IntegerMultBounds.Machine.CompactComplexAlignedFinalCapacityPath
public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames
public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness
public import IntegerMultBounds.Machine.CompactComplexAlignedSavedReturnPath
public import IntegerMultBounds.Machine.CompactComplexAlignedRootFinal
public import IntegerMultBounds.Machine.CompactComplexRootWorkspaceClean
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedCursorGuards
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventFrameState

/-! Genuine finalization and saved-PC pop from a reached terminal bank.
Both paths execute the unchanged aligned table and share the computed completed
child bank; the older saved-call association comes from its actual PC tape. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedReachedFinalReturn
noncomputable section
open Networks.Shared50ModularControl (prime)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyCompletedChildBoundary (before completed)
open CompactComplexAlignedBoundaryPaths (alignedBank)
open CompactComplexAlignedScalarEventPath (path)
open CompactComplexAlignedPoppedReturnReadiness (popped)
variable {s q : ℕ} {shape : CompactGadgetReservationShape.Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- Corrected sink, contraction, rejoin and orientation cost, including the
actual final control edge. -/
def finalCost (rows ell metadataPrecision : ℕ) : ℕ :=
  ((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor *
      CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision + 1 +
    (NativeUniformPolynomialRotationRoles.constant * CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision + 1 +
      (NativeUniformPolynomialRotationRoles.constant * CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision + 1 +
        CompactComplexEndpointRoleExchange.constant * CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision))) + 1 +
    CompactComplexSourceReadyNonleafOrientedFinal.constant roles *
      CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) + 1

section Reached
variable {stage : ActivePrefixStageParameters.Stage shape}
    {rows ell metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      dependencyLevels frameVolume returnedVolume scalarPrefix current : ℕ}
    (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (stackOrigin : ℤ) (savedCalls : List Call) (call : Call)
    {nodeBank : Tapes (nodeTapes s roles) 2}
    (reached : Reached stage rows ell metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix current
      pcStack stackOrigin (call :: savedCalls) nodeBank)
    (slotsCorrect : stage.slots = NativeEndpointCharacterRoles.arity)
    (rowsPositive : 0 < rows) (rowsDivisible : roles ∣ rows) (groupPositive : 0 < rows / roles)
    (guardPositive : 0 < shape.guard) (axesPositive : 0 < shape.axes)
    (guardFits : shape.guard + 1 ≤ shape.chunk) (payloadOne : shape.payload = 1)
    (precisionEnough : 2 * shape.bits ≤ metadataPrecision)
    (targetBelowCurrent : reached.targetValue ≤ current)
    (currentCapacity : current ≤ CompactSpectatorInheritedGrid.half shape (metadataPrecision - 2 * shape.bits) + 1)

include rowsPositive groupPositive guardPositive axesPositive guardFits payloadOne
  precisionEnough targetBelowCurrent currentCapacity

/-- Actual reached readiness and the actual saved-call top suffice to execute
finalization to the very bank used by completed-child return proofs. -/
theorem final_path : ∃ time ≤ finalCost (shape := shape) rows ell metadataPrecision,
    path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount
        CompactComplexCompletedLiveLower.schedule.length 3)
      (alignedBank (CompactComplexSourceReadyScalarWorkspace.ready nodeBank)) time 0
      (alignedBank ((CompactComplexSourceReadyWorkspace.ready
        (completed reached slotsCorrect rowsDivisible call)).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) := by
  obtain ⟨older, top, olderAssociated, olderBlank, tapeEquation, headEquation⟩ :=
    CompactComplexSourceReadySavedCallHistory.top
      (CompactComplexAlignedReturnedDormantFrames.parent_saved_associated reached)
  have stackEquation : FiniteReturnStack.bank (reached.storage.tape (Fin.natAdd 10 pcStack))
      (reached.storage.head (Fin.natAdd 10 pcStack)) =
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (top + CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) :=
    congrArg₂ FiniteReturnStack.bank tapeEquation headEquation
  have leafBlank : ∀ port : Fin 67,
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2).head
        ⟨port.val, lt_of_lt_of_le port.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩ = 0 ∧
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2).tape
        ⟨port.val, lt_of_lt_of_le port.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩ = (fun _ => blank) :=
    fun _ => ⟨rfl, rfl⟩
  obtain ⟨time, timeBound, finalPath⟩ := CompactComplexAlignedBoundaryPaths.tag3_path_capacity
    P headerStack liveStack stage rows ell metadataPrecision slotsCorrect rowsPositive rowsDivisible groupPositive
    guardPositive axesPositive guardFits payloadOne precisionEnough reached.control reached.queue reached.scalar
    reached.tail reached.storage (before reached)
    (CompactComplexSourceReadyReachedFinalizationReadiness.before_width reached)
    current reached.targetValue targetBelowCurrent reached.live reached.target reached.aux
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) pcStack call older top stackEquation
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2) currentCapacity leafBlank
  refine ⟨time, timeBound, ?_⟩
  have inputEquation := CompactComplexSourceReadyReachedFinalizationReadiness.actual_final_input reached
  have outputEquation := CompactComplexSourceReadyCompletedChildBoundary.completed_endpoint reached slotsCorrect rowsDivisible call
  rw [inputEquation]
  rw [← outputEquation]
  exact finalPath

/-- Finalization and genuine guard/pop execute consecutively on the same
computed completed bank, with both paid costs and the older call association. -/
theorem runs : ∃ older top time,
    CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls older top ∧
    time ≤ finalCost (shape := shape) rows ell metadataPrecision +
      (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3) + 5) ∧
    path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount
        CompactComplexCompletedLiveLower.schedule.length 3)
      (alignedBank (CompactComplexSourceReadyScalarWorkspace.ready nodeBank)) time
      (CompactComplexScheduledPCDecode.savedPC call)
      (alignedBank ((CompactComplexSourceReadyWorkspace.ready
        (popped (completed reached slotsCorrect rowsDivisible call) pcStack older top)).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) := by
  obtain ⟨finalTime, finalBound, finalPath⟩ := final_path P headerStack pcStack liveStack stackOrigin savedCalls call
    reached slotsCorrect rowsPositive rowsDivisible groupPositive guardPositive axesPositive guardFits payloadOne
    precisionEnough targetBelowCurrent currentCapacity
  obtain ⟨older, top, olderAssociated, popPath⟩ :=
    CompactComplexAlignedSavedReturnPath.public_associated_return_path P headerStack pcStack liveStack call
      (completed reached slotsCorrect rowsDivisible call)
      (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
      (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime) stackOrigin savedCalls
      (CompactComplexSourceReadyCompletedChildBoundary.completed_saved reached slotsCorrect rowsDivisible call)
  refine ⟨older, top, finalTime +
    (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3) + 5),
    olderAssociated, Nat.add_le_add_right finalBound _, ?_⟩
  exact FiniteFlowPath.append finalPath popPath

end Reached
/-- Root corrected sink, exact-capacity contraction/rejoin and empty-stack
post-orientation, including the original tag-three control edge. -/
def rootFinalCost (rows ell metadataPrecision : ℕ) : ℕ :=
  ((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
      CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+1+
    (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+1+
      (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+1+
        CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision)))+1+
    (CompactComplexSourceReadyNonleafFinalPath.constant roles*
      CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+4))+1

private theorem paid_root_cost_linear (sinkConstant rotationConstant exchangeConstant finalConstant nativeVolume : ℕ)
    (volumePositive : 0<nativeVolume) :
    ((sinkConstant*nativeVolume+1+(rotationConstant*nativeVolume+1+
      (rotationConstant*nativeVolume+1+exchangeConstant*nativeVolume)))+1+
      (finalConstant*nativeVolume+4))+1≤
      (sinkConstant+2*rotationConstant+exchangeConstant+finalConstant+9)*nativeVolume := by
  nlinarith

/-- The actual empty-root final path retains a fixed linear native-volume
cost; the original physical programs and guard steps remain charged. -/
theorem root_final_cost_linear (rows ell metadataPrecision : ℕ) (rowsPositive : 0<rows) :
    rootFinalCost (shape:=shape) rows ell metadataPrecision≤
      (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+
        2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+
        CompactComplexSourceReadyNonleafFinalPath.constant roles+9)*
          CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision :=
  paid_root_cost_linear _ _ _ _ _
    (Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape ell metadataPrecision))

section Root
variable {stage : ActivePrefixStageParameters.Stage shape}
    {rows ell metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      dependencyLevels frameVolume returnedVolume scalarPrefix current : ℕ}
    {pcStack : Fin s} {stackOrigin : ℤ} {nodeBank : Tapes (nodeTapes s roles) 2}
    (reached : Reached stage rows ell metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix current pcStack stackOrigin [] nodeBank)
    (slotsCorrect : stage.slots=NativeEndpointCharacterRoles.arity) (rowsDivisible : roles∣rows)

/-- The actual root output uses the terminal joined array directly. Root
post-orientation is identity because its real saved-call stack is empty. -/
def rootEndpoint := CompactComplexSourceReadyNonleafFinalPorts.endpoint shape rows ell metadataPrecision
  stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val
  (CompactComplexSourceReadyCompletedChildBoundary.joined reached slotsCorrect rowsDivisible)
  (CompactComplexSourceReadyCompletedChildBoundary.returnEntry reached slotsCorrect)
  (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)

/-- The literal root endpoint contains precisely the joined terminal array,
with the source head restored to zero. -/
theorem root_endpoint_source :
    (rootEndpoint reached slotsCorrect rowsDivisible).tape CompactComplexSourceReadyOrientation.source=
      CompactSpectatorLeafAxis.word
        (CompactComplexSourceReadyCompletedChildBoundary.joined reached slotsCorrect rowsDivisible) ∧
    (rootEndpoint reached slotsCorrect rowsDivisible).head CompactComplexSourceReadyOrientation.source=0 := by
  exact CompactComplexSourceReadyNonleafFinalPorts.source shape rows ell metadataPrecision
    stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val
    (CompactComplexSourceReadyCompletedChildBoundary.joined reached slotsCorrect rowsDivisible)
    (CompactComplexSourceReadyCompletedChildBoundary.returnEntry reached slotsCorrect)
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)

/-- The same literal root endpoint reclaims every role payload, private
entry frame, complete leaf workspace and work suffix with origin heads. -/
theorem root_endpoint_clean :
    CompactComplexRootWorkspaceClean.Clean (rootEndpoint reached slotsCorrect rowsDivisible) :=
  CompactComplexRootWorkspaceClean.endpoint_clean shape rows ell metadataPrecision
    stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val
    (CompactComplexSourceReadyCompletedChildBoundary.joined reached slotsCorrect rowsDivisible)
    (CompactComplexSourceReadyCompletedChildBoundary.returnEntry reached slotsCorrect)

/-- The actual root saved association supplies its literal empty guard cell. -/
theorem root_stack_empty : reached.storage.tape (Fin.natAdd 10 pcStack)
    (reached.storage.head (Fin.natAdd 10 pcStack)-1)=blank := by
  have associated := CompactComplexAlignedReturnedDormantFrames.parent_saved_associated reached
  rcases CompactComplexSourceReadySavedCallHistory.cases_stack associated with
    ⟨_,emptyTape,_⟩ | ⟨call,rest,older,top,impossible,_⟩
  · rw [emptyTape]
  · cases impossible

/-- Actual reached root readiness and live capacity execute the original
root final branch to its unchanged joined endpoint and empty return guard. -/
theorem root_path
    (P : Program ActivePrefixStageNative.tapes q prime) (headerStack liveStack : Fin s)
    (rowsPositive : 0<rows) (groupPositive : 0<rows/roles)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (payloadOne : shape.payload=1)
    (precisionEnough : 2*shape.bits≤metadataPrecision)
    (targetBelowCurrent : reached.targetValue≤current)
    (currentCapacity : current≤CompactSpectatorInheritedGrid.half shape (metadataPrecision-2*shape.bits)+1) :
    ∃ time≤rootFinalCost (shape:=shape) rows ell metadataPrecision,
      path P headerStack pcStack liveStack
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount
          CompactComplexCompletedLiveLower.schedule.length 3)
        (alignedBank (CompactComplexSourceReadyScalarWorkspace.ready nodeBank)) time 0
        (alignedBank ((rootEndpoint reached slotsCorrect rowsDivisible).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) ∧
      (alignedBank ((rootEndpoint reached slotsCorrect rowsDivisible).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).tape
        (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
        ((alignedBank ((rootEndpoint reached slotsCorrect rowsDivisible).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).head
            (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)-1)=blank := by
  have leafBlank : ∀ port : Fin 67,
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2).head
        ⟨port.val,lt_of_lt_of_le port.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2).tape
        ⟨port.val,lt_of_lt_of_le port.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank) :=
    fun _ => ⟨rfl,rfl⟩
  have actualPath := CompactComplexAlignedRootFinal.tag3_path_capacity P headerStack liveStack stage rows ell metadataPrecision
    slotsCorrect rowsPositive rowsDivisible groupPositive guardPositive axesPositive guardFits payloadOne precisionEnough
    reached.control reached.queue reached.scalar reached.tail reached.storage (before reached)
    (CompactComplexSourceReadyReachedFinalizationReadiness.before_width reached) current reached.targetValue
    targetBelowCurrent reached.live reached.target reached.aux
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) pcStack (root_stack_empty reached)
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2) currentCapacity leafBlank
  obtain ⟨time,timeBound,physical,emptyGuard⟩ := actualPath
  have actualInput := CompactComplexSourceReadyReachedFinalizationReadiness.actual_final_input reached
  refine ⟨time,timeBound,?_,emptyGuard⟩
  rw [actualInput]
  exact physical

end Root

section RootExecution
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexCompletedLiveLower (schedule)
variable {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft childExponent rows ell metadataPrecision baselinePrecision growthConstant baselineLive
    dependencyLevels frameVolume entryReturned initialLive finalLive elapsedSteps : ℕ}
  {pcStack headerStack liveStack : Fin s} {stackOrigin : ℤ}
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+1)
    dependencyLevels frameVolume entryReturned)
  (P : Program ActivePrefixStageNative.tapes q prime)
  (initialState : State (stage:=stage) (rowCount:=rows) (polynomialExponent:=ell) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
    (childExponent:=childExponent) (pcStack:=pcStack) (origin:=stackOrigin) (savedCalls:=[]) 0 initialLive)
  (finalBoundary : FrameState (stage:=stage) (rowCount:=rows) (polynomialExponent:=ell) (metadataPrecision:=metadataPrecision)
    (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0) (baselineLive:=baselineLive)
    (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
    (childExponent:=childExponent) (pcStack:=pcStack) (origin:=stackOrigin) (savedCalls:=[])
    (capture initialState headerStack liveStack) initialState.reached.targetValue schedule.length finalLive)
  (actualTrace : Execution P headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps)

include entryPath actualTrace

/-- The original entry Path and actual terminal cursor derive capacity.
Execution coverage and the retained real entry target derive its ordering;
no advanced Path or terminal denominator inequality is an input. -/
theorem root_path_of_execution
    (slotsCorrect : stage.slots=NativeEndpointCharacterRoles.arity) (rowsDivisible : roles∣rows)
    (rowsPositive : 0<rows) (groupPositive : 0<rows/roles)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (payloadOne : shape.payload=1)
    (baselineFits : baselineLive≤baselinePrecision) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk) :
    ∃ time≤rootFinalCost (shape:=shape) rows ell metadataPrecision,
      path P headerStack pcStack liveStack
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 3)
        (alignedBank (CompactComplexSourceReadyScalarWorkspace.ready finalBoundary.state.bank)) time 0
        (alignedBank ((rootEndpoint finalBoundary.state.reached slotsCorrect rowsDivisible).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) ∧
      (alignedBank ((rootEndpoint finalBoundary.state.reached slotsCorrect rowsDivisible).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).tape
        (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
        ((alignedBank ((rootEndpoint finalBoundary.state.reached slotsCorrect rowsDivisible).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).head
            (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)-1)=blank := by
  have precisionEnough : 2*shape.bits≤metadataPrecision := by omega
  have actualCapacity := CompactComplexSourceReadyReachedCursorGuards.current_capacity entryPath finalBoundary.state
    baselineFits precisionReserve denominatorRoom
  have inheritedCapacity : finalLive≤CompactSpectatorInheritedGrid.half shape (metadataPrecision-2*shape.bits)+1 := by
    rw [CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq precisionEnough]
    exact actualCapacity
  have coverage := CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage actualTrace
  have targetBelowCurrent : finalBoundary.state.reached.targetValue≤finalLive := by
    rw [finalBoundary.targetRetained]
    exact initialState.reached.target_growth.trans coverage.2
  exact root_path finalBoundary.state.reached slotsCorrect rowsDivisible P headerStack liveStack
    rowsPositive groupPositive guardPositive axesPositive guardFits payloadOne precisionEnough targetBelowCurrent inheritedCapacity

/-- An actual classifier/entry prefix, actual event execution, root
finalization and the genuine empty-stack guard halt the unchanged fixed
program. The prefix is an already established physical path, not a recursive
execution callback or invented root call. -/
theorem root_halts_of_execution
    (slotsCorrect : stage.slots=NativeEndpointCharacterRoles.arity) (rowsDivisible : roles∣rows)
    (rowsPositive : 0<rows) (groupPositive : 0<rows/roles)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (payloadOne : shape.payload=1)
    (baselineFits : baselineLive≤baselinePrecision) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (originalBank : Tapes (CompactComplexActualCallFullAlignment.tapes s roles) prime)
    (prefixElapsed prefixBudget : ℕ) (prefixBound : prefixElapsed≤prefixBudget)
    (entryPrefix : path P headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
      originalBank prefixElapsed (CompactComplexSourceReadyReachedEventTrace.cursorPC 0)
      (alignedBank (CompactComplexSourceReadyScalarWorkspace.ready initialState.bank))) :
    ∃ time≤prefixBudget+elapsedSteps+rootFinalCost (shape:=shape) rows ell metadataPrecision+2,
      HoareTime (CompactComplexSourceReadyAlignedActualTable.program P headerStack pcStack liveStack).2
        (fun bank => bank=originalBank)
        (fun bank => bank=alignedBank ((rootEndpoint finalBoundary.state.reached slotsCorrect rowsDivisible).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) time := by
  obtain ⟨finalElapsed,finalBound,finalPath,emptyGuard⟩ := root_path_of_execution entryPath P initialState finalBoundary actualTrace
    slotsCorrect rowsDivisible rowsPositive groupPositive guardPositive axesPositive guardFits payloadOne baselineFits precisionReserve denominatorRoom
  have eventPath := CompactComplexSourceReadyReachedEventTrace.execution_physical actualTrace
  have finalCursor : CompactComplexSourceReadyReachedEventTrace.cursorPC schedule.length=
      CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 3 :=
    CompactComplexSourceReadyReachedEventTrace.cursorPCFor_final _ _
  rw [finalCursor] at eventPath
  have completePath := FiniteFlowPath.append (FiniteFlowPath.append entryPrefix eventPath) finalPath
  have rootHalts := CompactComplexFixedNodeRootExit.path_halts
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) _ _ _ completePath emptyGuard
  refine ⟨prefixElapsed+elapsedSteps+finalElapsed+2,?_,rootHalts⟩
  omega

end RootExecution

end
end IntegerMultBounds.Machine.CompactComplexAlignedReachedFinalReturn
