module

public import IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEntryPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant

/-! Actual forward-basis and physical child-entry paths after counted siblings.
The current reached bank uses its counted cursor, while the original node-entry
Path and retained target certificate govern the unchanged aligned table. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedSiblingChildEntryPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexActualCallFullAlignment (localTapes tapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData basis_reached)
open CompactComplexAlignedChildEntryPath (BasisRuns path)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule CompactComplexRolePhaseSite.roleCount

private theorem child_path {stackCount basisStateCount : ℕ}
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventPosition : Fin schedule.length) (eventEquation : schedule.get eventPosition=Event.child call)
    (beforeBank afterBank : Tapes (tapes stackCount roles) prime) (timeBudget : ℕ)
    (execution : HoareTime (CompactComplexActualCallFullAlignment.child basisProgram headerStack pcStack liveStack call).2
      (fun bank => bank=beforeBank) (fun bank => bank=afterBank) timeBudget) :
    ∃ elapsedSteps≤timeBudget+1,path basisProgram headerStack pcStack liveStack
      (CompactComplexScheduledPCLayout.eventPC eventPosition) beforeBank elapsedSteps
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0) afterBank := by
  apply CompactComplexFixedNodePaths.child_prefix_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn basisProgram headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event basisProgram headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) eventPosition call eventEquation
    beforeBank afterBank timeBudget
  exact execution

section Parent
variable {stackCount basisStateCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  (headerStack pcStack liveStack : Fin stackCount) (origin : ℤ)
  (savedCalls : List Networks.ComplexRecursiveCallSchema.Call)
  (parentBank : Tapes (nodeTapes stackCount roles) 2)
  (eventPosition : Fin schedule.length)
  (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
    parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
    baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventPosition.val (arity^(childExponent+1))) scalarPrefix parentLive
    pcStack origin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call)

/-- The original forward basis and physical entry execute at the actual
scheduled sibling occurrence. Its target certificate is retained from node
entry, and the forward reached witness keeps that exact target value. -/
theorem child_paths (packingLimit : ℕ)
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (eventEquation : schedule.get eventPosition=Event.child call)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<parentRows) (childRowsPositive : 0<parentRows/roles) (rolesDivideRows : roles∣parentRows)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f →
      ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input
          (parent phaseCoordinate entryPath.visit activeFits pair) (parentRows/roles) polynomialExponent
          metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      parentReached.targetValue ledgerLeft ledgerExponent) :
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (parentRows/roles) polynomialExponent
      metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let afterBasis := basisArray stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive
      guardFitsChunk childRowsPositive parentSlots basisPC false
      (parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
      basisInput polynomialExponent (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
        basisPC false (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent)
          (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ forwardReached : Reached stage parentRows polynomialExponent metadataPrecision (childExponent+2)
      baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventPosition.val (arity^(childExponent+1))) scalarPrefix parentLive
      pcStack origin savedCalls (canonical (replacementCaller parentReached selectedRole afterBasis) parentReached.aux),
      forwardReached.data=replacementData parentReached selectedRole afterBasis ∧
      forwardReached.targetValue=parentReached.targetValue ∧
      (CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent metadataPrecision passTime : ℝ)≤
        basisConstant*ActivePrefixStageInverseBudget.scale basisInput ∧
      ∃ elapsedSteps≤CompactComplexActualCallRoleAlignment.cost roles stage parentRows polynomialExponent
          metadataPrecision passTime+1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape)
          parentRows polynomialExponent metadataPrecision+1,
        path basisProgram headerStack pcStack liveStack (CompactComplexScheduledPCLayout.eventPC eventPosition)
          (CleanSubbank.bank (Alphabet.mapTapes encoding (ready parentBank))) elapsedSteps
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
          (CleanSubbank.bank (Alphabet.mapTapes encoding
            (ready (CompactComplexSourceReadyWorkspace.ready
              (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate entryPath activeFits pair
                forwardReached call headerStack liveStack))))) := by
  dsimp only
  obtain ⟨basisReached,basisData⟩ := basis_reached parentReached (CompactComplexRolePhaseSite.role call.site)
    guardPositive guardFitsChunk childRowsPositive parentSlots (CompactComplexRolePhaseSite.pc call.site) false
  have storageFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields basisReached _ parentReached.aux rfl
  have storagePreserved : basisReached.storage=parentReached.storage := by
    simpa only [replacementCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank]
      using storageFields.1
  let forwardReached := { basisReached with
    targetValue := parentReached.targetValue
    target := by rw [storagePreserved];exact parentReached.target
    target_growth := parentReached.target_growth }
  obtain ⟨basisExecution,basisTimeBound⟩ := basisRuns stackCount shape _ parentRows polynomialExponent metadataPrecision
    (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventPosition.val (arity^(childExponent+1))) scalarPrefix parentLive
    pcStack origin savedCalls parentBank parentReached (CompactComplexRolePhaseSite.role call.site)
    guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots
    (CompactComplexRolePhaseSite.pc call.site) false parentPacked
  refine ⟨forwardReached,basisData,rfl,basisTimeBound,?_⟩
  have entryExecution := CompactComplexSourceReadySiblingChildEntryPath.child_entry_runs phaseCoordinate entryPath
    activeFits pair forwardReached call headerStack liveStack ledgerLive ledgerLeft ledgerExponent savedLedger
    eventPosition.isLt (by simpa only [List.get_eq_getElem] using eventEquation) pcHeaderDistinct pcLiveDistinct
    precisionReserve growthReserve baselineFits denominatorRoom childRowsPositive guardPositive axesPositive chunkPositive
  have extendedEntry := hoare_extend_eq entryExecution (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  have liftedEntry := CompactComplexSourceReadyAlignedActualTable.lift_runs
    (CompactComplexSourceReadyActualTable.child headerStack pcStack liveStack call).2
    _ _ (SharedBank.empty (localTapes roles) prime) extendedEntry
  have combinedExecution := basisExecution.seq liftedEntry
  exact child_path basisProgram headerStack pcStack liveStack call eventPosition eventEquation _ _ _ combinedExecution

end Parent
end
end IntegerMultBounds.Machine.CompactComplexAlignedSiblingChildEntryPath
