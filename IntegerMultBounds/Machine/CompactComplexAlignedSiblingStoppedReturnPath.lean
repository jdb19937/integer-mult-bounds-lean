module

public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnPath
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedChildRun
public import IntegerMultBounds.Machine.CompactComplexAlignedSiblingJoinedPhysicalReturn
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildProgress
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedGrid

/-! Complete stopped-child return after actual counted siblings. Classifier,
leaf, saved-PC pop, parent restoration and inverse basis use the original entry
Path and one unchanged aligned table; the current cursor is counted once. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedReturnPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyReachedReturnInvariant (roleData)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyCapturedChildFrames (childOutput)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexNonleafRoleChildBank (storage)
open CompactComplexAlignedStoppedReturnPath
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

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

private theorem ready_frame (publicBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2) :
    ((Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
      ((CompactComplexSourceReadyStoppedLeaf.ready publicBank).append
        (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))).append
      (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime))=
      CompactComplexAlignedChildReturnPath.liftedBank (CompactComplexSourceReadyWorkspace.bank publicBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)) := rfl


open CompactComplexSourceReadyReachedEventInvariant (canonical)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller returnedData)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexAlignedReachedChildReturnPath (mid)
open CompactComplexAlignedChildReturnPath (liftedBank)
open CompactComplexSourceReadyChildReturnPath (storagePart controlPart queuePart tailPart scalarPart)
open CompactComplexSourceReadyChildReturnPath (timeConstant)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyScalarWorkspace (ready)

private theorem prepend_return
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (basisWidth : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardSufficient : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (slotsCorrect : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth)
    (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+CompactComplexCompletedLiveLower.schedule.length)+2))
    (initialBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (prefixSteps prefixBudget : ℕ) (prefixBound : prefixSteps≤prefixBudget)
    (prefixPath : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      startPC initialBank prefixSteps (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2))))
    (joined : ReturnOutcome rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack childResult returnedBank
      basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked
      (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
      (returnCost rowCoordinate entryPath.visit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked)) :
    ReturnOutcome rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack childResult returnedBank
      basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked startPC initialBank (prefixBudget+(returnCost rowCoordinate entryPath.visit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked)) := by
  unfold ReturnOutcome at joined ⊢
  dsimp only [returnCost] at joined ⊢
  obtain ⟨returnedReached,returnedDataEquality,finalReached,finalDataEquality,inverseCostBound,returnSteps,returnBound,returnPath⟩ := joined
  refine ⟨returnedReached,returnedDataEquality,finalReached,finalDataEquality,inverseCostBound,
    prefixSteps+returnSteps,Nat.add_le_add prefixBound returnBound,?_⟩
  exact FiniteFlowPath.append prefixPath returnPath

/-- Package the physical return while its result and public bank are abstract.
The concrete stopped-child specialization therefore has a nominal result type. -/
private theorem physical_outcome
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (headerDistinctLive : headerStack≠liveStack)
    (exponentPositive : 0<(childExponent+2))
    (childRowsPositive : 0<rowCount/roles)
    (rowsGrouped : roles ∣ rowCount)
    (exponentEquality : (childExponent+2)=childExponent+2)
    (guardSufficient : 1≤shape.guard)
    (rawReady : Placement.active CompactComplexNonleafRoleParentContinuation.placement returnedBank=
      CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rowCoordinate entryPath.visit activeFitsAxes pair call.slot) (rowCount/roles) logColumns precision) (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles))
    (headerWord : returnedBank.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames (parentReached.storage.tape (Fin.natAdd 10 headerStack)) (parentReached.storage.head (Fin.natAdd 10 headerStack))
      (CompactComplexControllerChildPrefix.data (parent rowCoordinate entryPath.visit activeFitsAxes pair)))
    (headerHead : returnedBank.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top (parentReached.storage.head (Fin.natAdd 10 headerStack))
      (CompactComplexControllerChildPrefix.data (parent rowCoordinate entryPath.visit activeFitsAxes pair)))
    (headerTailClean : ∀ z,(parentReached.storage.head (Fin.natAdd 10 headerStack))≤z → (parentReached.storage.tape (Fin.natAdd 10 headerStack)) z=blank)
    (exponentWord : returnedBank.tape (CompactComplexNonleafRoleChildBank.control 1)=BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits ((childExponent+2)-1)))
    (exponentHead : returnedBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (progress : CompactComplexChildAlignmentBudget.Progress shape precision parentLive (parentLive+arity^(childExponent+1)) (parentLive+(arity^(childExponent+1))))
    (liveWord : returnedBank.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame (parentReached.storage.tape (Fin.natAdd 10 liveStack)) (parentReached.storage.head (Fin.natAdd 10 liveStack)) (RecursiveChildQuotientsConstant.bits parentLive))
    (liveHeadReady : returnedBank.head (storage (Fin.natAdd 10 liveStack))=(parentReached.storage.head (Fin.natAdd 10 liveStack))+1+(RecursiveChildQuotientsConstant.bits parentLive).length)
    (currentWord : returnedBank.tape CompactComplexNonleafRoleChildBank.current=BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (parentLive+(arity^(childExponent+1)))))
    (currentHead : returnedBank.head CompactComplexNonleafRoleChildBank.current=1)
    (targetBlankWord : returnedBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (targetBlankHead : returnedBank.head CompactComplexNonleafRoleChildBank.target=0)
    (liveFrameFree : ∀ z,(parentReached.storage.head (Fin.natAdd 10 liveStack))≤z → z<(parentReached.storage.head (Fin.natAdd 10 liveStack))+1+(RecursiveChildQuotientsConstant.bits parentLive).length → (parentReached.storage.tape (Fin.natAdd 10 liveStack)) z=blank)
    (childWidth : ∀ j,(childResult j).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      (childResult j).2.length=CompactNativeRoleHeaders.recordWidth shape precision)
    (rolesPositive : 0<roles)
    (axesPositive : 0<shape.axes)
    (chunkPositive : 0<shape.chunk)
    (payloadActual : returnedBank.head (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape rowCount logColumns precision
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).rho (parent rowCoordinate entryPath.visit activeFitsAxes pair).left
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).f (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).right (parent rowCoordinate entryPath.visit activeFitsAxes pair).source.val
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).target.val (caller parentReached)).head CompactComplexNonleafRoleEntry.stack ∧
      returnedBank.tape (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape rowCount logColumns precision
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).rho (parent rowCoordinate entryPath.visit activeFitsAxes pair).left
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).f (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).right (parent rowCoordinate entryPath.visit activeFitsAxes pair).source.val
          (parent rowCoordinate entryPath.visit activeFitsAxes pair).target.val (caller parentReached)).tape CompactComplexNonleafRoleEntry.stack)
    (clockBlank : returnedBank.head (CompactComplexNonleafRoleParentPayloadContinuation.extra 1)=0 ∧ returnedBank.tape (CompactComplexNonleafRoleParentPayloadContinuation.extra 1)=fun _ => blank)
    (scalarBank : scalarPart returnedBank=ActiveRepairRankHeadersCommands.bank parentReached.scalar)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (parentLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape precision ledgerLive parentReached.targetValue ledgerLeft ledgerExponent)
    (targetWord : (storagePart returnedBank).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) (parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount))) (RecursiveChildQuotientsConstant.bits parentReached.targetValue))
    (targetHeadReady : (storagePart returnedBank).head ⟨9,by omega⟩=(parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount)))+1+(RecursiveChildQuotientsConstant.bits parentReached.targetValue).length)
    (targetFrameFree : ∀ z,(parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount)))≤z → z<(parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount)))+1+(RecursiveChildQuotientsConstant.bits parentReached.targetValue).length → (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) z=blank)
    (basisWidth : ℕ)
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns basisWidth basisStateCount basisProgram basisConstant)
    (activePositive : 0<shape.active)
    (metadataFits : basePrecision+2*shape.bits≤precision)
    (axesFit : 0+(arity^(childExponent+1))≤shape.bits)
    (growthSufficient : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (advanceBound : (arity^(childExponent+1))≤2*(arity^(childExponent+1)))
    (childGrid : CompactSpectatorInheritedGrid.Grid shape (rowCount/roles) logColumns (precision-2*shape.bits) (parentLive+(arity^(childExponent+1)))
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound basePrecision growthConstant levels (frames+2*((CompactComplexSourceReadySiblingGuards.returnedCursor entryReturned eventIndex (arity^(childExponent+1)))+(arity^(childExponent+1)))+0))) childResult)
    (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<rowCount)
    (unitPayload : shape.payload=1)
    (slotsCorrect : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ op,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) op) basisWidth)
    (pcDistinctHeader : pcStack≠headerStack)
    (pcDistinctLive : pcStack≠liveStack)
    (countBlank : (storagePart returnedBank).head 0=0 ∧ (storagePart returnedBank).tape 0=(fun _ => blank))
    (control28Blank : (controlPart returnedBank).head 28=0 ∧ (controlPart returnedBank).tape 28=(fun _ => blank))
    (control29Blank : (controlPart returnedBank).head 29=0 ∧ (controlPart returnedBank).tape 29=(fun _ => blank))
    (savedAssociation : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls
      ((storagePart returnedBank).tape (Fin.natAdd 10 pcStack)) ((storagePart returnedBank).head (Fin.natAdd 10 pcStack))) :
    ReturnOutcome rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack childResult returnedBank
      basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked
      (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
      (returnCost rowCoordinate entryPath.visit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked) := by
  have joined := CompactComplexAlignedSiblingJoinedPhysicalReturn.runs
    rowCoordinate entryPath.visit activeFitsAxes pair call
    rowCount logColumns precision childResult returnedBank
    headerStack pcStack liveStack headerDistinctLive (parentReached.storage.tape (Fin.natAdd 10 headerStack))
    (parentReached.storage.head (Fin.natAdd 10 headerStack)) (childExponent+2) exponentPositive childRowsPositive rowsGrouped
    exponentEquality guardSufficient rawReady headerWord headerHead
    headerTailClean exponentWord exponentHead (parentReached.storage.tape (Fin.natAdd 10 liveStack)) (parentReached.storage.head (Fin.natAdd 10 liveStack))
    parentLive (parentLive+arity^(childExponent+1)) (arity^(childExponent+1)) (arity^(childExponent+1)) progress
    liveWord liveHeadReady currentWord currentHead targetBlankWord
    targetBlankHead liveFrameFree basePrecision growthConstant 0
    baseline levels frames entryReturned eventIndex scalarPrefix
    stackOrigin savedCalls parentBank parentReached childWidth
    rolesPositive axesPositive chunkPositive payloadActual clockBlank
    parentReached.scalar scalarBank (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) (parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount))) ledgerLive
    ledgerLeft ledgerExponent parentLedger targetWord targetHeadReady
    targetFrameFree basisWidth basisProgram basisConstant basisRuns
    entryPath (Nat.pow_le_pow_right (by decide) (by omega)) activePositive metadataFits axesFit growthSufficient
    dependencyRoom advanceBound childGrid guardFitsChunk rowsPositive
    unitPayload slotsCorrect basisPacked pcDistinctHeader pcDistinctLive
    countBlank control28Blank control29Blank savedAssociation
  unfold ReturnOutcome
  dsimp only [returnCost] at joined ⊢
  exact joined

attribute [local irreducible] stoppedResult stoppedBank CompactComplexAlignedPoppedReturnReadiness.popped ReturnOutcome

/-- The stopped child returns its real installed result, restores its actual
parent frames, and executes the original inverse basis word on the same table.
No returned-bank readiness or local execution hypothesis is supplied. -/
theorem runs (basisWidth : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (basisConstant : ℝ) (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns basisWidth basisStateCount basisProgram basisConstant)
    (eventBound : eventIndex<CompactComplexCompletedLiveLower.schedule.length)
    (eventEquation : CompactComplexCompletedLiveLower.schedule[eventIndex]=CompactComplexCompletedLiveLower.Event.child call)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    (parentTailsClean : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,parentReached.storage.head storagePort≤cell →
      parentReached.storage.tape storagePort cell=blank)
    (metadataFits : basePrecision+2*shape.bits≤precision) (baselineFits : baseline≤basePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (activePositive : 0<shape.active) (axesPositive : 0<shape.axes)
    (guardSufficient : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (childRowsPositive : 0<rowCount/roles) (rowsGrouped : roles∣rowCount) (unitPayload : shape.payload=1)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1)≤shape.bits)
    (growthSufficient : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (parentLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape precision ledgerLive parentReached.targetValue ledgerLeft ledgerExponent)
    (slotsCorrect : (parent rowCoordinate entryPath.visit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate entryPath.visit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate entryPath.visit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth) :
    ∃ olderWord olderHead,
      CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead ∧
      ReturnOutcome rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
        (stoppedResult rowCoordinate entryPath.visit activeFitsAxes pair parentReached call)
        (CompactComplexAlignedPoppedReturnReadiness.popped
          (stoppedBank rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack)
          pcStack olderWord olderHead)
        basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length 0)
        (liftedBank (CompactComplexSourceReadyWorkspace.bank
          (childOutput rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack)
          (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
        (prefixCost (rowCount/roles) shape logColumns precision childExponent+
          returnCost rowCoordinate entryPath.visit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked) := by
  let entryBank := childOutput rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  let childResult := stoppedResult rowCoordinate entryPath.visit activeFitsAxes pair parentReached call
  let completedBank := stoppedBank rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have resultDefinition : childResult=CompactComplexCorrectedStoppedChildGridSemantics.installed call (rowCount/roles) logColumns
      (precision-2*shape.bits) rowCoordinate (Visit.child entryPath.visit call.slot)
      (oriented call (selectedArray parentReached call)) := by
    unfold childResult stoppedResult
    rfl
  have bankDefinition : completedBank=CompactComplexSourceReadyStoppedLeafCount.returned entryBank
      (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1)) := by
    unfold completedBank stoppedBank
    rfl
  obtain ⟨olderWord,olderHead,restoredAssociation,prefixSteps,prefixBound,prefixPath⟩ :=
    CompactComplexAlignedSiblingStoppedChildRun.stopped_prefix rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack basisProgram
      eventBound eventEquation pcDistinctHeader pcDistinctLive metadataFits growthSufficient baselineFits denominatorRoom childRowsPositive
      (by omega) axesPositive unitPayload childStopped
  have entryBankEquality : CompactComplexSourceReadySiblingChildInvariant.childPublic
      rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack=entryBank := rfl
  rw [entryBankEquality,ready_frame,ready_frame,←resultDefinition,←bankDefinition] at prefixPath
  let publicPopped := CompactComplexAlignedPoppedReturnReadiness.popped completedBank pcStack olderWord olderHead
  have poppedDefinition : publicPopped=SharedPlacementAlphabet.setTape completedBank
      (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack) olderWord olderHead := by
    unfold publicPopped CompactComplexAlignedPoppedReturnReadiness.popped
    rfl
  rw [←poppedDefinition] at prefixPath
  let snapshot := CompactComplexSourceReadyCapturedChildFrames.snapshot rowCoordinate entryPath.visit activeFitsAxes pair
    parentReached call headerStack liveStack
  have capturedSettled := CompactComplexSourceReadyCapturedSettledFrames.snapshot_settled
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
    headerDistinctLive pcDistinctHeader pcDistinctLive parentTailsClean
  have beforepopSettled := CompactComplexSourceReadyStoppedSettledFrames.beforepop_settled snapshot call entryBank
    (selectedArray parentReached call) (CompactSpectatorLeafAxis.word childResult)
    (parentLive+arity^(childExponent+1)) capturedSettled
  rw [returned_oriented,←bankDefinition] at beforepopSettled
  have capturedHeaders := CompactComplexSourceReadyCapturedChildFrames.snapshot_headers
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack pcDistinctHeader.symm headerDistinctLive
  have capturedLive := CompactComplexSourceReadyCapturedChildFrames.snapshot_live
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack headerDistinctLive.symm pcDistinctLive.symm
  have capturedTarget := CompactComplexSourceReadyCapturedChildFrames.snapshot_target
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have capturedPayload := CompactComplexSourceReadyCapturedChildFrames.snapshot_payload
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have poppedHeaders := popped_snapshot_storage snapshot completedBank beforepopSettled pcStack olderWord olderHead
    (Fin.natAdd 10 headerStack) (Or.inl rfl) (fun equality => pcDistinctHeader (Fin.natAdd_injective _ _ equality).symm)
  have poppedLive := popped_snapshot_storage snapshot completedBank beforepopSettled pcStack olderWord olderHead
    (Fin.natAdd 10 liveStack) (Or.inr (Or.inl rfl)) (fun equality => pcDistinctLive (Fin.natAdd_injective _ _ equality).symm)
  have poppedTarget := popped_snapshot_storage snapshot completedBank beforepopSettled pcStack olderWord olderHead
    (⟨9,by omega⟩ : Fin (10+stackCount)) (Or.inr (Or.inr (Or.inr rfl)))
    (by intro equality;have indexEquality := congrArg Fin.val equality;simp only [Fin.val_natAdd] at indexEquality;omega)
  have headerWord := poppedHeaders.2.trans capturedHeaders.2
  have headerHead := poppedHeaders.1.trans capturedHeaders.1
  have liveWord := poppedLive.2.trans capturedLive.2
  have liveHead := poppedLive.1.trans capturedLive.1
  have targetRead := CompactComplexAlignedReachedChildReturnPath.storage_read publicPopped (⟨9,by omega⟩ : Fin (10+stackCount))
  have targetWord := targetRead.2.trans (poppedTarget.2.trans capturedTarget.2)
  have targetHead := targetRead.1.trans (poppedTarget.1.trans capturedTarget.1)
  have settledPayload := CompactComplexSourceReadyReachedDormantFrameInvariant.settled_aux beforepopSettled
  have poppedPayload := popped_extra completedBank pcStack olderWord olderHead 0
  have payloadActual := And.intro (poppedPayload.1.trans (settledPayload.1.trans capturedPayload.1))
    (poppedPayload.2.trans (settledPayload.2.trans capturedPayload.2))
  have initialRaw := CompactComplexSourceReadyChildEntryPath.public_output_active call rowCoordinate entryPath.visit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have completedRaw := returned_raw_source entryBank
    (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rowCoordinate entryPath.visit activeFitsAxes pair call.slot)
      (rowCount/roles) logColumns precision) (rowCount/roles) logColumns
    (selectedArray parentReached call) childResult (parentLive+arity^(childExponent+1)) initialRaw
  rw [←bankDefinition] at completedRaw
  have poppedRaw := (CompactComplexAlignedPoppedReturnPorts.popped_raw_active completedBank pcStack olderWord olderHead).trans completedRaw
  have metadataWidthFits : 2*shape.bits≤precision := by omega
  have selectedSourceEquality : selectedArray parentReached call=
      roleData parentReached (CompactComplexRolePhaseSite.role call.site) := rfl
  have widthResultDefinition := resultDefinition
  rw [selectedSourceEquality] at widthResultDefinition
  have childWidth := installed_width parentReached call rowCoordinate (Visit.child entryPath.visit call.slot) metadataWidthFits
  dsimp only at childWidth
  rw [←widthResultDefinition] at childWidth
  have childGrid := CompactComplexSourceReadySiblingStoppedGrid.installed_grid parentReached entryPath call rowCoordinate (Visit.child entryPath.visit call.slot)
    (Nat.pow_le_pow_right (by decide) (by omega)) activePositive metadataFits axesFit growthSufficient dependencyRoom
  rw [←widthResultDefinition] at childGrid
  have headerTailClean := parentTailsClean (Fin.natAdd 10 headerStack) (Or.inl rfl)
  have liveTailClean := parentTailsClean (Fin.natAdd 10 liveStack) (Or.inr (Or.inl rfl))
  have targetTailClean := parentTailsClean (⟨9,by omega⟩ : Fin (10+stackCount)) (Or.inr (Or.inr (Or.inr rfl)))

  have enteredExponent := CompactComplexChildInputReadiness.entered_exponent call rowCoordinate entryPath.visit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have retainedExponent := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_control entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1)) 1
  rw [←bankDefinition] at retainedExponent
  have poppedExponent := CompactComplexAlignedPoppedReturnPorts.popped_control_read completedBank pcStack olderWord olderHead 1
  have exponentRead := CompactComplexAlignedReachedChildReturnPath.control_read publicPopped 1
  have exponentHead := exponentRead.1.symm.trans (poppedExponent.1.trans (retainedExponent.1.trans enteredExponent.1))
  have exponentWord : publicPopped.tape (CompactComplexNonleafRoleChildBank.control 1)=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (childExponent+2-1)) := by
    have encodedWord := exponentRead.2.symm.trans (poppedExponent.2.trans (retainedExponent.2.trans enteredExponent.2))
    have exponentIdentity : childExponent+2-1=childExponent+1 := by omega
    rw [exponentIdentity,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact encodedWord
  have returnedPorts := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_ports entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedPorts
  have poppedCurrent := CompactComplexAlignedPoppedReturnPorts.popped_small_storage_read completedBank pcStack olderWord olderHead
    (⟨7,by omega⟩ : Fin (10+stackCount)) (by change (7:ℕ)<10;omega)
  have currentRead := CompactComplexAlignedReachedChildReturnPath.storage_read publicPopped (⟨7,by omega⟩ : Fin (10+stackCount))
  have currentHead := currentRead.1.symm.trans (poppedCurrent.1.trans returnedPorts.2.2.1)
  have currentWord : publicPopped.tape CompactComplexNonleafRoleChildBank.current=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (parentLive+arity^(childExponent+1))) := by
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact currentRead.2.symm.trans (poppedCurrent.2.trans returnedPorts.2.2.2.1)
  have poppedTargetBlank := CompactComplexAlignedPoppedReturnPorts.popped_small_storage_read completedBank pcStack olderWord olderHead
    (⟨8,by omega⟩ : Fin (10+stackCount)) (by change (8:ℕ)<10;omega)
  have targetBlankRead := CompactComplexAlignedReachedChildReturnPath.storage_read publicPopped (⟨8,by omega⟩ : Fin (10+stackCount))
  have targetBlankHead := targetBlankRead.1.symm.trans (poppedTargetBlank.1.trans returnedPorts.2.2.2.2.1)
  have targetBlankWord := targetBlankRead.2.symm.trans (poppedTargetBlank.2.trans returnedPorts.2.2.2.2.2)
  have entryScalar := CompactComplexSourceReadyStoppedChildEntryPorts.child_scalarPart
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedScalar := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_scalarPart entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedScalar
  have scalarBank := (CompactComplexAlignedPoppedReturnPorts.popped_scalarPart completedBank pcStack olderWord olderHead).trans
    (returnedScalar.trans entryScalar)
  have entryClock := CompactComplexSourceReadyStoppedChildEntryPorts.child_clock_blank
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedClock := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_clock entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedClock
  have poppedClock := popped_extra completedBank pcStack olderWord olderHead 1
  have clockBlank := And.intro (poppedClock.1.trans (returnedClock.1.trans entryClock.1))
    (poppedClock.2.trans (returnedClock.2.trans entryClock.2))
  have entryCount := CompactComplexSourceReadyStoppedChildEntryPorts.child_count_blank
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedCount := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_count entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedCount
  have poppedCount := CompactComplexAlignedPoppedReturnPorts.popped_small_storage_read completedBank pcStack olderWord olderHead
    (⟨0,by omega⟩ : Fin (10+stackCount)) (by change (0:ℕ)<10;omega)
  have countBlank := And.intro (poppedCount.1.trans (returnedCount.1.trans entryCount.1))
    (poppedCount.2.trans (returnedCount.2.trans entryCount.2))
  have entryControl28 := CompactComplexSourceReadyStoppedChildEntryPorts.child_control28
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedControl28 := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_control entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1)) 28
  rw [←bankDefinition] at returnedControl28
  have poppedControl28 := CompactComplexAlignedPoppedReturnPorts.popped_control_read completedBank pcStack olderWord olderHead 28
  have control28Blank := And.intro (poppedControl28.1.trans (returnedControl28.1.trans entryControl28.1))
    (poppedControl28.2.trans (returnedControl28.2.trans entryControl28.2))
  have entryControl29 := CompactComplexSourceReadyStoppedChildEntryPorts.child_control29
    rowCoordinate entryPath.visit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedControl29 := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_control entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1)) 29
  rw [←bankDefinition] at returnedControl29
  have poppedControl29 := CompactComplexAlignedPoppedReturnPorts.popped_control_read completedBank pcStack olderWord olderHead 29
  have control29Blank := And.intro (poppedControl29.1.trans (returnedControl29.1.trans entryControl29.1))
    (poppedControl29.2.trans (returnedControl29.2.trans entryControl29.2))
  have savedAssociation := CompactComplexAlignedPoppedReturnPorts.popped_saved_associated completedBank pcStack
    olderWord olderHead stackOrigin savedCalls restoredAssociation
  have savedRead := CompactComplexAlignedReachedChildReturnPath.storage_read publicPopped (Fin.natAdd 10 pcStack)
  have projectedAssociation : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls
      ((storagePart publicPopped).tape (Fin.natAdd 10 pcStack)) ((storagePart publicPopped).head (Fin.natAdd 10 pcStack)) := by
    rw [savedRead.1,savedRead.2]
    exact savedAssociation
  have rolesPositive : 0<roles := by norm_num [roles,CompactComplexRolePhaseSite.roleCount]
  have rowsPositive : 0<rowCount := lt_of_lt_of_le childRowsPositive (Nat.div_le_self rowCount roles)
  have chunkPositive : 0<shape.chunk := Nat.zero_lt_of_lt rowCoordinate.isLt
  have stoppedProgress := CompactComplexSourceReadySiblingChildProgress.stopped entryPath call eventIndex precision
    CompactComplexDenominatorCapacity.scalarRows baseline (CompactFramedScalarGrid.rows scalarPrefix).length parentLive
    eventBound eventEquation (by omega) (by omega) denominatorRoom
    (CompactComplexDenominatorCapacity.actual_prefix scalarPrefix) parentReached.upper_ledger
  have joinedOutcome := physical_outcome rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack
    childResult publicPopped headerDistinctLive (by omega) childRowsPositive
    rowsGrouped rfl guardSufficient poppedRaw headerWord
    headerHead headerTailClean exponentWord exponentHead stoppedProgress
    liveWord liveHead currentWord currentHead targetBlankWord
    targetBlankHead (fun cell beyondHead _ => liveTailClean cell beyondHead) childWidth rolesPositive
    axesPositive chunkPositive payloadActual clockBlank scalarBank
    ledgerLive ledgerLeft ledgerExponent parentLedger targetWord
    targetHead (fun cell beyondHead _ => targetTailClean cell beyondHead) basisWidth basisProgram basisConstant
    basisRuns activePositive metadataFits axesFit
    growthSufficient dependencyRoom (by omega) childGrid guardFitsChunk
    rowsPositive unitPayload slotsCorrect basisPacked pcDistinctHeader
    pcDistinctLive countBlank control28Blank control29Blank projectedAssociation
  refine ⟨olderWord,olderHead,restoredAssociation,?_⟩
  exact prepend_return rowCoordinate entryPath activeFitsAxes pair parentReached call headerStack liveStack
    childResult publicPopped basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive
    slotsCorrect basisPacked
    (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length 0)
    (liftedBank (CompactComplexSourceReadyWorkspace.bank entryBank
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
    prefixSteps (prefixCost (rowCount/roles) shape logColumns precision childExponent)
    prefixBound prefixPath joinedOutcome


end Parent
end
end IntegerMultBounds.Machine.CompactComplexAlignedSiblingStoppedReturnPath
