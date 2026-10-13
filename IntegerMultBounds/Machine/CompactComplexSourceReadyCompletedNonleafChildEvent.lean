module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildReturn
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedNonleafReturnStep
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEventSemantics

/-! One completed-child certificate supplies both physical execution and
exact original child-instruction semantics of a nonstopped parent event.
The actual forward-entry prefix and the certificate's child path are joined
with parent restoration on the same bank and table. This is the compositional
induction step; existence of certificates at every depth remains separate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildEvent
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
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyCompletedNonleafChild (CompletedChild resultArray returnedBank)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Event
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive
    parentLevels parentFrames parentReturned eventIndex parentLive eventBudget pathBudget : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (parentPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    parentLevels parentFrames parentReturned)
  (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  {pcStack headerStack liveStack : Fin stackCount} {origin : ℤ} {savedCalls : List ComplexRecursiveCallSchema.Call}

local notation "ParentState" => State (stage:=parent phaseCoordinate parentPath.visit activeFits pair) (rowCount:=parentRows)
  (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
  (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
  (baselineLive:=baselineLive) (dependencyLevels:=parentLevels) (frameVolume:=parentFrames)
  (entryReturned:=parentReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
  (origin:=origin) (savedCalls:=savedCalls)

/-- The certificate is the only recursive execution input: its actual tensor
and returned bank determine the same paid parent successor and exact values. -/
theorem step
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (call : ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (childNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false)
    (before : ParentState eventIndex parentLive)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<parentRows/roles)
    (parentSlots : (parent phaseCoordinate parentPath.visit activeFits pair).slots=25^3)
    (forwardReached : Reached (parent phaseCoordinate parentPath.visit activeFits pair) parentRows polynomialExponent
      metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive parentLevels parentFrames
      (returnedCursor parentReturned eventIndex (arity^(childExponent+1)))
      (CompactComplexActualScalarOrdinal.scalarGroups (schedule.take eventIndex)).length parentLive pcStack origin savedCalls
      (canonical (replacementCaller before.reached (CompactComplexRolePhaseSite.role call.site)
        (basisArray (parent phaseCoordinate parentPath.visit activeFits pair) (parentRows/roles) polynomialExponent metadataPrecision
          guardPositive guardFitsChunk childRowsPositive parentSlots (CompactComplexRolePhaseSite.pc call.site) false
          (before.reached.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site))))) before.reached.aux))
    (forwardData : forwardReached.data=replacementData before.reached (CompactComplexRolePhaseSite.role call.site)
      (basisArray (parent phaseCoordinate parentPath.visit activeFits pair) (parentRows/roles) polynomialExponent metadataPrecision
        guardPositive guardFitsChunk childRowsPositive parentSlots (CompactComplexRolePhaseSite.pc call.site) false
        (before.reached.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)))))
    (forwardTarget : forwardReached.targetValue=before.reached.targetValue)
    (childSlots : (CompactComplexChildHeadersData.child phaseCoordinate parentPath.visit activeFits pair call.slot).slots=arity)
    (childRowsDivisible : roles∣parentRows/roles)
    (certificate : CompletedChild (headerStack:=headerStack) (liveStack:=liveStack) phaseCoordinate parentPath activeFits pair forwardReached call basisProgram
      childSlots childRowsDivisible eventBudget pathBudget)
    (entryElapsed entryBudget : ℕ) (entryTimeBound : entryElapsed≤entryBudget)
    (entryExecution : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (CompactComplexScheduledPCLayout.eventPC ⟨eventIndex,eventBound⟩) (physicalBank before) entryElapsed
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
      (CompactComplexAlignedBoundaryPaths.alignedBank
        ((CompactComplexSourceReadyWorkspace.ready
          (CompactComplexSourceReadySiblingChildInvariant.childPublic phaseCoordinate parentPath activeFits pair
            forwardReached call headerStack liveStack)).append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))))
    (snapshot : Snapshot stackCount) (beforeSettled : Settled snapshot before.reached.storage before.reached.aux)
    (snapshotHeaderStack : snapshot.headerStack=headerStack) (snapshotLiveStack : snapshot.liveStack=liveStack)
    (snapshotPcStack : snapshot.pcStack=pcStack)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (rowsPositive : 0<parentRows) (rolesDivideRows : roles∣parentRows)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) (activePositive : 0<shape.active) (unitPayload : shape.payload=1)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesFit : 0+2*arity^(childExponent+1)≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedTargetLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      before.reached.targetValue ledgerLeft ledgerExponent)
    (parentPacked : ∀ operation : BinaryRowProgram.Op (Fin (parent phaseCoordinate parentPath.visit activeFits pair).slots),
      1<(parent phaseCoordinate parentPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
          (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit) :
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate parentPath.visit activeFits pair)
      (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput polynomialExponent
      (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots (CompactComplexRolePhaseSite.pc call.site) true
        (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent) (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ after : ParentState (eventIndex+1)
      (childTarget (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) parentLive (childExponent+1)),
      after.reached.targetValue=before.reached.targetValue ∧ Settled snapshot after.reached.storage after.reached.aux ∧
      ∃ elapsedSteps≤entryBudget+(pathBudget+(CompactComplexSourceReadyChildReturnPath.timeConstant roles*
        CompactNativeRoleTransferBudget.volume parentRows shape polynomialExponent metadataPrecision+1+
        CompactComplexActualCallRoleAlignment.cost roles (parent phaseCoordinate parentPath.visit activeFits pair)
          parentRows polynomialExponent metadataPrecision passTime+1)),
        Step basisProgram headerStack liveStack before after elapsedSteps ∧
        ∀ (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
          stored phaseCoordinate parentPath.visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            (childTarget (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) parentLive (childExponent+1))
            after.reached.data row polynomialIndex globalAnchor=
          FramedFactorExecution.run [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
            (stored phaseCoordinate parentPath.visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
              parentLive before.reached.data row polynomialIndex globalAnchor) := by
  dsimp only
  have forwardFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields forwardReached _ before.reached.aux rfl
  have forwardStorage : forwardReached.storage=before.reached.storage := by
    simpa only [replacementCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using forwardFields.1
  have forwardSettled : Settled snapshot forwardReached.storage forwardReached.aux := by
    rw [forwardStorage,forwardFields.2]
    exact beforeSettled
  have retainedLedger := CompactComplexSourceReadySiblingChildProgress.retainedTargetLedger savedTargetLedger forwardTarget
  have returnOutcome := CompactComplexSourceReadyCompletedNonleafChildReturn.runs
    phaseCoordinate parentPath activeFits pair forwardReached call basisProgram childSlots childRowsDivisible certificate
    snapshot forwardSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack eventBound eventEquation
    headerLiveDistinct pcHeaderDistinct pcLiveDistinct packingLimit basisConstant basisRuns rowsPositive childRowsPositive
    rolesDivideRows guardPositive guardFitsChunk axesPositive chunkPositive activePositive unitPayload precisionReserve
    baselineFits growthReserve denominatorRoom axesFit chunkRoom ledgerLive ledgerLeft ledgerExponent retainedLedger parentSlots parentPacked
  have eventOutcome := CompactComplexSourceReadyNonleafReturnFrame.append_outcome
    phaseCoordinate parentPath activeFits pair forwardReached call headerStack liveStack certificate.resultArray
    certificate.returnedBank certificate.finalBoundary.state.reached.scalar packingLimit basisProgram basisConstant
    guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked _ _ _ _ entryElapsed entryBudget _
    entryTimeBound entryExecution returnOutcome
  obtain ⟨controlBank,queueBank,scalarHeaders,tailBank,storageBank,auxiliaryBank,returnedReached,returnedData,
      finalReached,finalData,targetPreserved,finalSettled,elapsedSteps,timeBound,physical⟩ :=
    CompactComplexSourceReadyNonleafReturnFrame.extract_final_settled
      phaseCoordinate parentPath activeFits pair forwardReached call headerStack liveStack
      certificate.resultArray _ certificate.finalBoundary.state.reached.scalar certificate.older certificate.top
      certificate.olderAssociated snapshot forwardSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
      headerLiveDistinct pcHeaderDistinct pcLiveDistinct packingLimit basisProgram basisConstant guardPositive guardFitsChunk
      childRowsPositive parentSlots parentPacked _ _ _ eventOutcome
  have selectedIndex : CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)=
      CompactComplexScalarIntegerRows.wireIndex call.role := by
    rw [←CompactComplexSourceReadyChildEventSemantics.selected_role_index call,Equiv.symm_apply_apply]
  have selectedForwardData : forwardReached.data=replacementData before.reached (CompactComplexRolePhaseSite.role call.site)
      (CompactComplexSourceReadyNonleafChildTensor.selectedForward phaseCoordinate parentPath.visit activeFits pair
        (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive call before.reached.data) := by
    simpa only [CompactComplexSourceReadyNonleafChildTensor.selectedForward,selectedIndex,
      CompactComplexChildHeadersData.parent] using forwardData
  have childTensor := CompactComplexSourceReadyNonleafChildReturnGrid.child_tensor_of_forward before.reached
    phaseCoordinate parentPath.visit activeFits pair guardPositive guardFitsChunk childRowsPositive call
    forwardReached selectedForwardData certificate.resultArray certificate.actualChildTensor
  have childFitsNode : arity^(childExponent+1)≤arity^(childExponent+2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have exactValues := CompactComplexSourceReadySiblingChildEventSemantics.reached_child_semantics before.reached
    phaseCoordinate parentPath.visit activeFits pair rfl rfl call guardPositive guardFitsChunk childRowsPositive parentSlots
    parentPath childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom certificate.resultArray
    controlBank queueBank scalarHeaders tailBank storageBank auxiliaryBank childTensor
    forwardReached forwardData returnedReached returnedData finalReached finalData
  obtain ⟨after,_sameBank,sameData,targetRetained,settled,actualStep⟩ :=
    CompactComplexSourceReadyReachedNonleafEventSuccessor.successor
      phaseCoordinate parentPath activeFits pair basisProgram headerStack liveStack call eventBound eventEquation
      childNonstopped before _ finalReached snapshot (targetPreserved.trans forwardTarget) finalSettled elapsedSteps physical
  refine ⟨after,targetRetained,settled,elapsedSteps,timeBound,actualStep,?_⟩
  intro row polynomialIndex globalAnchor
  have nonstoppedTarget : childTarget (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1))
      parentLive (childExponent+1)=parentLive+2*arity^(childExponent+1) := by
    rw [childNonstopped]
    rfl
  rw [sameData,nonstoppedTarget]
  exact exactValues row polynomialIndex globalAnchor

end Event
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildEvent
