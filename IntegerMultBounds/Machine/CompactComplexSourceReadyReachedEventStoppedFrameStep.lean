module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedEventPath
public import IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal
public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnedDormantFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedChildSemantics

/-! Actual stopped-child successors retain the incoming target certificate
and settled ancestor frames on the same physical endpoint. Every return witness
is produced by the stopped run; no outcome or storage equality is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedFrameStep
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller returnedData)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule Event childTarget)
open CompactComplexSourceReadyReachedEventTrace (State Step physicalBank)
open CompactComplexAlignedStoppedReturnPath (ReturnOutcome prefixCost returnCost stoppedResult stoppedBank)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls schedule CompactComplexRolePhaseSite.roleCount

section Transport
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume returnedBefore returnedAfter prefixBefore prefixAfter liveBefore liveAfter : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {bank : Tapes (nodeTapes stackCount roles) 2}

/-- Equality transport changes only the numerical indices of a reached
witness, retaining its literal physical bank and every data component. -/
private def reindex_reached
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedAfter prefixAfter liveAfter pcStack origin savedCalls bank := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  exact reached

private theorem reindex_reached_data
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    (reindex_reached reached returnedEqual prefixEqual liveEqual).data=reached.data := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  rfl

private theorem reindex_reached_fields
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (returnedEqual : returnedBefore=returnedAfter) (prefixEqual : prefixBefore=prefixAfter) (liveEqual : liveBefore=liveAfter) :
    (reindex_reached reached returnedEqual prefixEqual liveEqual).targetValue=reached.targetValue ∧
    (reindex_reached reached returnedEqual prefixEqual liveEqual).storage=reached.storage ∧
    (reindex_reached reached returnedEqual prefixEqual liveEqual).aux=reached.aux := by
  cases returnedEqual
  cases prefixEqual
  cases liveEqual
  exact ⟨rfl,rfl,rfl⟩

/-- The retained target is certified by the actual physical target port;
all other fields, the data and the underlying bank remain literal. -/
private def retarget_reached
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank)
    (retainedTarget : ℕ)
    (targetPort : reached.storage.head (⟨8,by omega⟩ : Fin (10+stackCount))=1 ∧
      reached.storage.tape (⟨8,by omega⟩ : Fin (10+stackCount))=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits retainedTarget))
    (targetGrowth : retainedTarget≤liveBefore+2*arity^nodeExponent) :
    Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedBefore prefixBefore liveBefore pcStack origin savedCalls bank :=
  { reached with targetValue := retainedTarget, target := targetPort, target_growth := targetGrowth }

end Transport

section Parent
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {leftBoundary childExponent rowCount logColumns precision basePrecision growthConstant baseline levels frames
    entryReturned eventIndex scalarPrefix parentLive : ℕ}
  (rowCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+2) levels frames entryReturned)
  (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair) rowCount logColumns precision
    (childExponent+2) basePrecision growthConstant 0 baseline levels frames
    (CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
    scalarPrefix parentLive pcStack stackOrigin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- Extract the actual final canonical bank while result and stopped-return
banks are abstract. No physical endpoint equality is an input. -/
private theorem extract_final_settled
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (childBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (olderWord : ℤ → Fin 6) (olderHead : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead)
    (snapshot : Snapshot stackCount) (parentSettled : Settled snapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : snapshot.headerStack=headerStack)
    (snapshotLiveStack : snapshot.liveStack=liveStack) (snapshotPcStack : snapshot.pcStack=pcStack)
    (headerLiveDistinct : headerStack≠liveStack) (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (parentSlots : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (parentPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2))
    (initialBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (timeBudget : ℕ)
    (outcome : ReturnOutcome rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
      childResult (CompactComplexAlignedPoppedReturnReadiness.popped childBank pcStack olderWord olderHead) packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive
      parentSlots parentPacked startPC initialBank timeBudget) :
    ∃ (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
      (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (aux : Tapes 2 2),
      ∃ returnedReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls
        (canonical (returnedCaller parentReached (CompactComplexRolePhaseSite.role call.site)
          (arity^(childExponent+1)) childResult control queue scalar tail storage) aux),
      returnedReached.data=returnedData parentReached (CompactComplexRolePhaseSite.role call.site)
        (arity^(childExponent+1)) childResult ∧
      let inverseArray := basisArray (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        (rowCount/roles) logColumns precision guardPositive guardFitsChunk childRowsPositive parentSlots
        (CompactComplexRolePhaseSite.pc call.site) true
        (returnedReached.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)))
      ∃ finalReached : Reached (parent rowCoordinate entryPath.visit activeFitsAxes pair)
        rowCount logColumns precision (childExponent+2) basePrecision growthConstant 0 baseline levels frames
        (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
        (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls
        (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
          returnedReached.aux),
      finalReached.data=replacementData returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray ∧
      finalReached.targetValue=parentReached.targetValue ∧
      Settled snapshot finalReached.storage finalReached.aux ∧
      ∃ elapsedSteps≤timeBudget,
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack startPC initialBank elapsedSteps
          (CompactComplexScheduledPCLayout.callNextPC call)
          (CleanSubbank.bank (Alphabet.mapTapes encoding
            (ready (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
              returnedReached.aux)))) := by
  unfold ReturnOutcome at outcome
  dsimp only at outcome
  obtain ⟨returnedReached,returnedData,finalReached,finalData,inverseBound,elapsedSteps,timeBound,physical⟩ := outcome
  have framePreserved := CompactComplexAlignedReturnedDormantFrames.captured_final_settled parentReached
    (CompactComplexRolePhaseSite.role call.site) childBank olderWord olderHead olderAssociated
    headerStack liveStack snapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
    headerLiveDistinct pcHeaderDistinct pcLiveDistinct (arity^(childExponent+1)) (arity^(childExponent+1))
    rowCoordinate entryPath.visit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult)) childResult
    _ _ parentReached.scalar _ returnedReached _ finalReached
  let restoredStorage := CompactComplexAlignedReturnedDormantFrames.capturedStorage parentReached
    (CompactComplexRolePhaseSite.role call.site) childBank olderWord olderHead headerStack liveStack
    (arity^(childExponent+1)) rowCoordinate entryPath.visit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult))
  have returnedFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields
    returnedReached _ parentReached.aux rfl
  have returnedStorage : returnedReached.storage=restoredStorage := by
    simpa only [restoredStorage,CompactComplexAlignedReturnedDormantFrames.capturedStorage,
      CompactComplexSourceReadyReachedReturnInvariant.returnedCaller,
      CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using returnedFields.1
  have finalFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields
    finalReached _ returnedReached.aux rfl
  have finalStorage : finalReached.storage=returnedReached.storage := by
    simpa only [CompactComplexSourceReadyReachedBasisInvariant.replacementCaller,
      CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using finalFields.1
  have targetPorts : restoredStorage.head ⟨8,by omega⟩=1 ∧
      restoredStorage.tape ⟨8,by omega⟩=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits parentReached.targetValue) := by
    unfold restoredStorage CompactComplexAlignedReturnedDormantFrames.capturedStorage
    constructor
    · exact (CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports _ _ _ _ _).2.2.1
    · exact (CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports _ _ _ _ _).2.2.2.1.trans
        (BinaryDescriptorStackRoundtrip.descriptor_encoded _)
  let retainedReached := { finalReached with
    targetValue := parentReached.targetValue
    target := by rw [finalStorage,returnedStorage]; exact targetPorts
    target_growth := parentReached.target_growth.trans
      (Nat.add_le_add_right (Nat.le_add_right parentLive (arity^(childExponent+1)))
        (2*arity^(childExponent+2))) }
  exact ⟨_,_,_,_,_,_,returnedReached,returnedData,retainedReached,finalData,rfl,
    framePreserved.2,elapsedSteps,timeBound,physical⟩

end Parent

attribute [local irreducible] ReturnOutcome stoppedBank CompactComplexAlignedPoppedReturnReadiness.popped

section Event
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex : ℕ}
  {rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive sourceLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- All literal programs, basis passes and table edges of one stopped event
are paid. Its next State is constructed from the actual returned witness. -/
theorem stopped_child_frame_step_values
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (before : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) eventIndex sourceLive)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (snapshot : Snapshot stackCount) (beforeSettled : Settled snapshot before.reached.storage before.reached.aux)
    (snapshotHeaderStack : snapshot.headerStack=headerStack)
    (snapshotLiveStack : snapshot.liveStack=liveStack) (snapshotPcStack : snapshot.pcStack=pcStack)
    (activePositive : 0<shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
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
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      before.reached.targetValue ledgerLeft ledgerExponent) :
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) polynomialExponent
      metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
      basisInput polynomialExponent (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
        basisPC false (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent)
          (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ after : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)),
      after.reached.targetValue=before.reached.targetValue ∧
      Settled snapshot after.reached.storage after.reached.aux ∧
      ∃ elapsedSteps≤(CompactComplexActualCallRoleAlignment.cost roles stage rowCount polynomialExponent metadataPrecision passTime+
        1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) rowCount polynomialExponent metadataPrecision+1)+
        (prefixCost (rowCount/roles) shape polynomialExponent metadataPrecision childExponent+
          returnCost phaseCoordinate entryPath.visit activeFits pair call packingLimit guardPositive guardFitsChunk
            childRowsPositive parentSlots parentPacked),
        Step basisProgram headerStack liveStack before after elapsedSteps ∧
        ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
            (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1))
              sourceLive (childExponent+1)) after.reached.data row polynomialIndex globalAnchor=
          Networks.FramedFactorExecution.run
            [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
            (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
              sourceLive before.reached.data row polynomialIndex globalAnchor) := by
  dsimp only
  have parentTailsClean : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,before.reached.storage.head storagePort≤cell →
      before.reached.storage.tape storagePort cell=blank := by
    intro storagePort protectedPort cell cellBound
    have snapshotProtected : CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
        snapshot.headerStack snapshot.liveStack snapshot.pcStack storagePort := by
      rw [snapshotHeaderStack,snapshotLiveStack,snapshotPcStack]
      exact protectedPort
    apply beforeSettled.storage_clean storagePort snapshotProtected cell
    rw [←beforeSettled.storage_heads storagePort snapshotProtected]
    exact cellBound
  obtain ⟨forwardReached,forwardData,targetRetained,forwardBasisBound,olderWord,olderHead,olderAssociated,outcome⟩ :=
    CompactComplexAlignedSiblingStoppedEventPath.runs phaseCoordinate entryPath activeFits pair headerStack pcStack liveStack
      origin savedCalls before.bank ⟨eventIndex,eventBound⟩ before.reached call packingLimit basisProgram basisConstant basisRuns
      (by simpa only [List.get_eq_getElem] using eventEquation) pcHeaderDistinct pcLiveDistinct headerLiveDistinct
      parentTailsClean activePositive childStopped axesFit chunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive
      rolesDivideRows unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom
      axesPositive chunkPositive ledgerLive ledgerLeft ledgerExponent savedLedger
  have forwardFields := CompactComplexSourceReadySettledEventInvariant.canonical_fields
    forwardReached _ before.reached.aux rfl
  have forwardStorage : forwardReached.storage=before.reached.storage := by
    simpa only [CompactComplexSourceReadyReachedBasisInvariant.replacementCaller,
      CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] using forwardFields.1
  have forwardSettled : Settled snapshot forwardReached.storage forwardReached.aux := by
    rw [forwardStorage,forwardFields.2]
    exact beforeSettled
  obtain ⟨control,queue,scalar,tail,storage,aux,returnedReached,returnedDataEquation,
      finalReached,finalDataEquation,targetPreserved,finalSettled,elapsedSteps,timeBound,physical⟩ :=
    extract_final_settled (rowCoordinate:=phaseCoordinate) (entryPath:=entryPath) (activeFitsAxes:=activeFits) (pair:=pair)
      (parentReached:=forwardReached) (call:=call) (headerStack:=headerStack) (liveStack:=liveStack)
      (stoppedResult phaseCoordinate entryPath.visit activeFits pair forwardReached call)
      (stoppedBank phaseCoordinate entryPath.visit activeFits pair forwardReached call headerStack liveStack)
      olderWord olderHead olderAssociated snapshot forwardSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
      headerLiveDistinct pcHeaderDistinct pcLiveDistinct packingLimit basisProgram basisConstant guardPositive guardFitsChunk childRowsPositive parentSlots parentPacked _ _ _ outcome
  have exactValues := CompactComplexSourceReadySiblingStoppedChildSemantics.reached_event_semantics
    phaseCoordinate entryPath activeFits pair before.reached call guardPositive guardFitsChunk childRowsPositive parentSlots
    activePositive precisionReserve (by simpa only [Nat.zero_add] using axesFit) growthReserve chunkRoom
    control queue scalar tail storage aux forwardReached forwardData returnedReached returnedDataEquation
    finalReached finalDataEquation
  let inverseArray := basisArray (parent phaseCoordinate entryPath.visit activeFits pair) (rowCount/roles)
    polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive parentSlots
    (CompactComplexRolePhaseSite.pc call.site) true
    (returnedReached.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)))
  let finalBank := canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) inverseArray)
    returnedReached.aux
  have returnedSuccessor := CompactComplexSourceReadySiblingChildProgress.returned_cursor_successor
    entryReturned eventIndex (arity^(childExponent+1)) call eventBound eventEquation
  have scalarPreserved := CompactComplexActualScalarOrdinal.child_count_successor schedule eventIndex eventBound call eventEquation
  have stoppedTarget : childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1))
      sourceLive (childExponent+1)=sourceLive+arity^(childExponent+1) := by
    rw [childStopped]
    rfl
  let after : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)) := {
    inRange := by omega
    bank := finalBank
    reached := reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm stoppedTarget.symm }
  have fieldsPreserved := reindex_reached_fields finalReached returnedSuccessor.symm scalarPreserved.symm stoppedTarget.symm
  refine ⟨after,fieldsPreserved.1.trans (targetPreserved.trans targetRetained),?_,elapsedSteps,timeBound,?_,?_⟩
  · change Settled snapshot (reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm stoppedTarget.symm).storage
      (reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm stoppedTarget.symm).aux
    rw [fieldsPreserved.2.1,fieldsPreserved.2.2]
    exact finalSettled
  ·
    apply Step.child call eventBound eventEquation before after elapsedSteps
    rw [CompactComplexSourceReadyReachedEventTrace.cursorPC_event eventIndex eventBound,
      CompactComplexSourceReadyReachedEventTrace.cursorPC_next (⟨eventIndex,eventBound⟩ : Fin schedule.length)]
    rw [CompactComplexScheduledPCLayout.actual_return_successor call (⟨eventIndex,eventBound⟩ : Fin schedule.length)
      (by simpa only [List.get_eq_getElem] using eventEquation)] at physical
    exact physical
  · intro row polynomialIndex globalAnchor
    change stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1))
      (reindex_reached finalReached returnedSuccessor.symm scalarPreserved.symm stoppedTarget.symm).data
      row polynomialIndex globalAnchor=_
    rw [reindex_reached_data,stoppedTarget]
    exact exactValues row polynomialIndex globalAnchor


/-- Compatibility projection of the joint stopped-frame/value construction. -/
theorem stopped_child_frame_step
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventBound : eventIndex<schedule.length) (eventEquation : schedule[eventIndex]=Event.child call)
    (before : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) eventIndex sourceLive)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (snapshot : Snapshot stackCount) (beforeSettled : Settled snapshot before.reached.storage before.reached.aux)
    (snapshotHeaderStack : snapshot.headerStack=headerStack)
    (snapshotLiveStack : snapshot.liveStack=liveStack) (snapshotPcStack : snapshot.pcStack=pcStack)
    (activePositive : 0<shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
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
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      before.reached.targetValue ledgerLeft ledgerExponent) :
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    let basisPC := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) polynomialExponent
      metadataPrecision guardPositive guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles)
      basisInput polynomialExponent (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput parentSlots
        basisPC false (ActivePrefixStageNativePolynomial.symbols (2^polynomialExponent)
          (NativePolynomialStageShape.width shape metadataPrecision)) parentPacked)
    ∃ after : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=metadataPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (eventIndex+1)
      (childTarget (Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) sourceLive (childExponent+1)),
      after.reached.targetValue=before.reached.targetValue ∧
      Settled snapshot after.reached.storage after.reached.aux ∧
      ∃ elapsedSteps≤(CompactComplexActualCallRoleAlignment.cost roles stage rowCount polynomialExponent metadataPrecision passTime+
        1+CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) rowCount polynomialExponent metadataPrecision+1)+
        (prefixCost (rowCount/roles) shape polynomialExponent metadataPrecision childExponent+
          returnCost phaseCoordinate entryPath.visit activeFits pair call packingLimit guardPositive guardFitsChunk
            childRowsPositive parentSlots parentPacked),
        Step basisProgram headerStack liveStack before after elapsedSteps := by
  obtain ⟨after,targetRetained,settled,elapsedSteps,timeBound,physical,exactValues⟩ :=
    stopped_child_frame_step_values phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack call eventBound eventEquation before
      pcHeaderDistinct pcLiveDistinct headerLiveDistinct snapshot beforeSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
      activePositive childStopped axesFit chunkRoom guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows
      unitPayload parentSlots parentPacked precisionReserve baselineFits growthReserve denominatorRoom axesPositive chunkPositive
      ledgerLive ledgerLeft ledgerExponent savedLedger
  exact ⟨after,targetRetained,settled,elapsedSteps,timeBound,physical⟩

end Event
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventStoppedFrameStep
