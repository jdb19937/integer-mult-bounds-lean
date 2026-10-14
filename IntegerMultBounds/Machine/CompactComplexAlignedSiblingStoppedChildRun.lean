module

public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedChildRun
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildInvariant

/-! A stopped child at an actual event uses the original node-entry Path
and counted sibling cursor. Derived child readiness and its genuine child
dependency ledger execute the classifier, orientations, leaf and saved return
on the unchanged aligned prime table. Parent restoration is a separate step. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedChildRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadySiblingChildInvariant (childPublic)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexChildHeadersData (parent child)
open CompactComplexCompletedLiveLower (Event schedule)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount schedule CompactComplexCallReturn.addressCount
  CompactComplexCallReturn.addressWidth CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

private theorem returned_oriented {stackCount coefficientCount : ℕ}
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (sourceArray : Fin coefficientCount → ButterflyStreamData.Coefficient)
    (resultWord : ℤ → Fin 6) (resultLive : ℕ) :
    CompactComplexSourceReadyStoppedLeafCount.returned
      (CompactComplexSourceReadyOrientedControlsFrame.output call inputBank sourceArray) resultWord resultLive=
      CompactComplexSourceReadyStoppedLeafCount.returned inputBank resultWord resultLive := by
  unfold CompactComplexSourceReadyOrientedControlsFrame.output CompactComplexSourceReadyStoppedLeafCount.returned
  split_ifs
  · simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
      CompactComplexSourceReadyLeafPhase.source,SharedPlacementAlphabet.setTape_setTape]
  · rfl

section Parent
variable {stackCount basisStateCount : ℕ} {shape : Shape}
    {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex : ℕ}
    {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
    (phaseCoordinate : Fin shape.chunk)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
      dependencyLevels frameVolume entryReturned)
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackCount} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackCount roles) 2}
    (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
      parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
      scalarPrefix parentLive pcStack origin calls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- The actual scheduled stopped child executes from its physical entry to
its decoded original saved PC. Selected width/grid, headers, live ledger and
saved history are derived by scheduled_child_entered, counting siblings once. -/
theorem stopped_prefix (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childRowsPositive : 0<parentRows/roles) (guardPositive : 0<shape.guard)
    (axesPositive : 0<shape.axes) (unitPayload : shape.payload=1)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true) :
    let entryBank := childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack
    let childResult := CompactComplexCorrectedStoppedChildGridSemantics.installed call (parentRows/roles) polynomialExponent
      (metadataPrecision-2*shape.bits) phaseCoordinate (Visit.child entryPath.visit call.slot)
      (oriented call (selectedArray parentReached call))
    let completedBank := CompactComplexSourceReadyStoppedLeafCount.returned entryBank
      (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
    ∃ olderWord olderHead,
      CompactComplexSourceReadySavedCallHistory.Associated origin calls olderWord olderHead ∧
      ∃ elapsedSteps≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume (parentRows/roles) shape polynomialExponent metadataPrecision+1+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
          CompactComplexSourceReadyOrientationInvariants.constant+1)*
          CompactNativeRoleTransferBudget.volume (parentRows/roles) shape polynomialExponent metadataPrecision*(arity^(childExponent+1)))+1+
          (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)),
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
          ((Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
            ((CompactComplexSourceReadyStoppedLeaf.ready entryBank).append
              (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).append
            (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime)) elapsedSteps
          (CompactComplexScheduledPCDecode.savedPC call)
          ((Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
            ((CompactComplexSourceReadyStoppedLeaf.ready
              (SharedPlacementAlphabet.setTape completedBank
                (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack) olderWord olderHead)).append
              (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).append
            (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime)) := by
  dsimp only
  let entryBank := childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack
  let childStage := child phaseCoordinate entryPath.visit activeFits pair call.slot
  let childDependency := CompactRecursiveDependencyBudget.Path.child entryPath call
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have entered := CompactComplexSourceReadySiblingChildInvariant.scheduled_child_entered
    phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack
    pcHeaderDistinct pcLiveDistinct metadataFits growthReserve eventBound eventEquation
  have reachedAssociation : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin (call::calls)
      ((CompactComplexSourceReadyStoppedLeaf.ready entryBank).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)) := by
    simpa only [CompactComplexSourceReadyScalarWorkspace.ready,CompactComplexSourceReadyWorkspace.ready_leaf]
      using entered.saved_calls
  have sourceRoleFits : childStage.source.val≤arity := Nat.le_of_lt childStage.source.isLt
  have targetRoleFits : childStage.target.val≤arity := Nat.le_of_lt childStage.target.isLt
  have childRightFits : childStage.right≤shape.active := Nat.sub_le _ _
  obtain ⟨olderWord,olderHead,restoredAssociation,elapsedSteps,timeBound,execution⟩ :=
    CompactComplexAlignedStoppedChildRun.stopped_child_return_width basisProgram headerStack pcStack liveStack call
      shape (parentRows/roles) polynomialExponent metadataPrecision phaseCoordinate childDependency
      childStage.right childStage.source.val childStage.target.val parentLive entryBank
      (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
      (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime) origin calls reachedAssociation
      (selectedArray parentReached call) guardPositive axesPositive childRowsPositive metadataFits entered.width baselineLive
      entered.headers entered.source entered.live entered.target_blank entered.exponent.2 entered.exponent.1
      CompactComplexDenominatorCapacity.scalarRows 0 unitPayload childRightFits sourceRoleFits targetRoleFits
      (by omega) (by omega) denominatorRoom entered.upper_ledger activeFits entered.stop_ready entered.dimension childStopped
  rw [returned_oriented] at execution
  exact ⟨olderWord,olderHead,restoredAssociation,elapsedSteps,timeBound,execution⟩

end Parent
end
end IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedChildRun
