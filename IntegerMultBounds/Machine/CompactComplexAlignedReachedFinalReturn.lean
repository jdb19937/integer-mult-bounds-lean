module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedFinalizationReadiness
public import IntegerMultBounds.Machine.CompactComplexAlignedFinalCapacityPath
public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames
public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness
public import IntegerMultBounds.Machine.CompactComplexAlignedSavedReturnPath

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
end
end IntegerMultBounds.Machine.CompactComplexAlignedReachedFinalReturn
