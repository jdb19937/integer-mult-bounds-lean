module

public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedChildRun
public import IntegerMultBounds.Machine.CompactComplexAlignedJoinedPhysicalReturn
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedSettledFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedReturnGrid
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildEntryPorts

/-! The stopped child uses the actual pre-oriented leaf result and one-volume
live advance. Numerical result widths and grids derive from the reached parent;
its literal saved-frame references come from the physical child entry. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedReturnInvariant (roleData)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexChildHeadersData (parent)
variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

section Numerical
variable {parentStage : ActivePrefixStageParameters.Stage shape}
  {rowCount logColumns precision parentExponent basePrecision growthConstant axesUsed baseline levels frames returnedVolume scalarPrefix parentLive : ℕ}
  {pcStack : Fin stackCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached parentStage rowCount logColumns precision parentExponent basePrecision growthConstant axesUsed
    baseline levels frames returnedVolume scalarPrefix parentLive pcStack stackOrigin savedCalls parentBank)

/-- The literal corrected stopped leaf inherits the actual role record width,
including both saved-call conjugations. -/
theorem installed_width {childLeft childExponent : ℕ}
    (call : Networks.ComplexRecursiveCallSchema.Call) (rowCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active childLeft (childExponent+1))
    (metadataFits : 2*shape.bits≤precision) :
    let installed := CompactComplexCorrectedStoppedChildGridSemantics.installed call (rowCount/roles) logColumns
      (precision-2*shape.bits) rowCoordinate childVisit
      (oriented call (roleData parentReached (CompactComplexRolePhaseSite.role call.site)))
    ∀ coefficient, (installed coefficient).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      (installed coefficient).2.length=CompactNativeRoleHeaders.recordWidth shape precision := by
  dsimp only
  let source := roleData parentReached (CompactComplexRolePhaseSite.role call.site)
  have sourceWidth := CompactComplexSourceReadyReachedReturnInvariant.role_width parentReached metadataFits
    (CompactComplexRolePhaseSite.role call.site)
  have orientedWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call shape (rowCount/roles)
    logColumns (precision-2*shape.bits) source sourceWidth
  have leafWidth := CompactSpectatorLeafLoop.width_run shape (rowCount/roles) logColumns
    (ButterflyIndependentGuardHeaders.reservation shape.bits (precision-2*shape.bits))
    rowCoordinate childVisit (arity^(childExponent+1)) (oriented call source) orientedWidth
  have installedWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call shape (rowCount/roles)
    logColumns (precision-2*shape.bits)
    (CompactSpectatorLeafGuardOriginal.result .forward shape (rowCount/roles) logColumns
      (precision-2*shape.bits) rowCoordinate childVisit (oriented call source)) leafWidth
  intro coefficient
  have recordWidth : CompactNativeRoleHeaders.recordWidth shape precision=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation shape.bits (precision-2*shape.bits)) shape.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  rw [recordWidth]
  exact installedWidth coefficient

/-- The parent prefix supplies the grid for the exact installed stopped result,
with its genuine one-child-volume denominator advance. -/
theorem installed_grid {parentLeft childLeft childExponent : ℕ}
    (parentPath : CompactRecursiveDependencyBudget.Path shape.active parentLeft parentExponent levels frames returnedVolume)
    (call : Networks.ComplexRecursiveCallSchema.Call) (rowCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active childLeft (childExponent+1))
    (activePositive : 0<shape.active) (metadataFits : basePrecision+2*shape.bits≤precision)
    (axesFit : axesUsed+arity^(childExponent+1)≤shape.bits)
    (growthSufficient : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    CompactSpectatorInheritedGrid.Grid shape (rowCount/roles) logColumns (precision-2*shape.bits)
      (parentLive+arity^(childExponent+1))
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound basePrecision growthConstant levels
          (frames+2*(returnedVolume+arity^(childExponent+1))+axesUsed)))
      (CompactComplexCorrectedStoppedChildGridSemantics.installed call (rowCount/roles) logColumns
        (precision-2*shape.bits) rowCoordinate childVisit
        (oriented call (roleData parentReached (CompactComplexRolePhaseSite.role call.site)))) :=
  CompactComplexSourceReadyCompletedReturnGrid.stopped_grid parentReached parentPath call rowCoordinate childVisit
    _ rfl activePositive metadataFits axesFit growthSufficient dependencyRoom

end Numerical

section Literal
open SharedPlacementAlphabet (setTape)
open CompactComplexNonleafRoleChildBank (tapes storage current target)
open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexSourceReadyOrientedControlsFrame (output)

/-- The final leaf source write absorbs the earlier source-only conjugation;
all dormant input ports remain the actual entry ports. -/
theorem returned_oriented {coefficientCount : ℕ} (call : Networks.ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (tapes stackCount roles) 2)
    (sourceArray : Fin coefficientCount → ButterflyStreamData.Coefficient)
    (resultWord : ℤ → Fin 6) (resultLive : ℕ) :
    returned (output call inputBank sourceArray) resultWord resultLive=returned inputBank resultWord resultLive := by
  unfold output returned
  split_ifs
  · simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
      CompactComplexSourceReadyLeafPhase.source,SharedPlacementAlphabet.setTape_setTape]
  · rfl

private theorem active_update_outside {activeCount extraCount tapeCount : ℕ}
    (tapePlacement : Fin (activeCount+extraCount) ≃ Fin tapeCount)
    (inputBank : Tapes tapeCount 2) (updatedPort : Fin tapeCount)
    (portOutside : ∀ activePort,updatedPort≠tapePlacement (Fin.castAdd extraCount activePort))
    (resultWord : ℤ → Fin 6) (resultHead : ℤ) :
    Placement.active tapePlacement (setTape inputBank updatedPort resultWord resultHead)=
      Placement.active tapePlacement inputBank := by
  apply congrArg₂ Tapes.mk <;> funext activePort
  all_goals simp only [setTape,Function.update_of_ne (portOutside activePort).symm]

private theorem active_update_inside {activeCount extraCount tapeCount : ℕ}
    (tapePlacement : Fin (activeCount+extraCount) ≃ Fin tapeCount)
    (inputBank : Tapes tapeCount 2) (updatedPort : Fin activeCount)
    (resultWord : ℤ → Fin 6) (resultHead : ℤ) :
    Placement.active tapePlacement
      (setTape inputBank (tapePlacement (Fin.castAdd extraCount updatedPort)) resultWord resultHead)=
      setTape (Placement.active tapePlacement inputBank) updatedPort resultWord resultHead := by
  apply congrArg₂ Tapes.mk <;> funext activePort
  all_goals
    by_cases portsEqual : activePort=updatedPort
    · subst activePort
      simp only [Placement.active,setTape,Function.update_self]
    · have indicesDistinct : tapePlacement (Fin.castAdd extraCount activePort)≠
          tapePlacement (Fin.castAdd extraCount updatedPort) := by
        intro indicesEqual
        exact portsEqual (Fin.castAdd_injective _ _ (tapePlacement.injective indicesEqual))
      simp only [Placement.active,setTape,Function.update_of_ne indicesDistinct,Function.update_of_ne portsEqual]

private def nativeSourceIndex {roleCount : ℕ} : Fin (43+CompactNativeRoleInstall.rawCount roleCount) :=
  Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+roleCount)))

private theorem native_source_slot {roleCount : ℕ} :
    CompactComplexNonleafRoleSplit.slot (s:=10+stackCount) (c:=roleCount) nativeSourceIndex=
      CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount) (c:=roleCount) := by
  apply Fin.ext
  simp [nativeSourceIndex,CompactComplexNonleafRoleSplit.slot,CompactComplexSourceReadyLeafPhase.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot]

private theorem storage_outside_raw {roleCount : ℕ} (storagePort : Fin (10+stackCount))
    (rawPort : Fin (43+CompactNativeRoleInstall.rawCount roleCount)) :
    storage (s:=stackCount) (c:=roleCount) storagePort≠
      CompactComplexNonleafRoleSplit.slot (s:=10+stackCount) (c:=roleCount) rawPort := by
  intro portsEqual
  have portValues := congrArg Fin.val portsEqual
  dsimp only [CompactComplexNonleafRoleSplit.slot] at portValues
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at portValues
  have rawPortBound := rawPort.isLt
  have storagePortBound := storagePort.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at portValues
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at rawPortBound
  split_ifs at portValues <;> omega

private theorem source_payload_update {roleCount : ℕ} (oldWord resultWord : ℤ → Fin 6) :
    setTape (CyclicRowCopy.payload oldWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0))
      (Fin.castAdd roleCount (0 : Fin 1)) resultWord 0=
      CyclicRowCopy.payload resultWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0) := by
  unfold CyclicRowCopy.payload
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun sourceBank : Tapes 1 2 => sourceBank.append
    (⟨fun _ => 0,fun _ : Fin roleCount => fun _ => blank⟩ : Tapes roleCount 2))
  apply congrArg₂ Tapes.mk <;> funext singlePort
  all_goals
    have indexEqual : singlePort=(0 : Fin 1) := Subsingleton.elim _ _
    rw [indexEqual]
    simp only [Function.update_self]

private theorem native_source_update {roleCount : ℕ} (rawState : ActiveRepairRankHeadersCommands.State)
    (oldWord resultWord : ℤ → Fin 6) :
    setTape (CompactNativeRoleOriginal.bank rawState
      (CyclicRowCopy.payload oldWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0)))
      nativeSourceIndex resultWord 0=
      CompactNativeRoleOriginal.bank rawState
        (CyclicRowCopy.payload resultWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0)) := by
  have sourceIndexExpanded : nativeSourceIndex (roleCount:=roleCount)=
      Fin.natAdd 43 (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2
        (Fin.castAdd roleCount (0 : Fin 1)))))) := Fin.ext rfl
  rw [sourceIndexExpanded]
  unfold CompactNativeRoleOriginal.bank CompactNativeRoleInstall.blankRaw
  rw [SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    source_payload_update]

/-- Stopped execution retains the child raw headers and vacant roles, while
its literal leaf result replaces the selected source. -/
theorem returned_raw_source (inputBank : Tapes (tapes stackCount roles) 2)
    (rawState : ActiveRepairRankHeadersCommands.State) (rowCount logColumns : ℕ)
    (sourceArray resultArray : CompactSpectatorVisitGeometry.Array shape rowCount logColumns)
    (resultLive : ℕ)
    (initialRawSource : Placement.active placement inputBank=
      CompactNativeRoleOriginal.bank rawState
        (CompactNativeRoleReservedBridge.sourcePayload shape rowCount logColumns sourceArray roles)) :
    Placement.active placement (returned inputBank (CompactSpectatorLeafAxis.word resultArray) resultLive)=
      CompactNativeRoleOriginal.bank rawState
        (CompactNativeRoleReservedBridge.sourcePayload shape rowCount logColumns resultArray roles) := by
  unfold returned
  rw [active_update_outside placement _ target (fun port => by
      simpa only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.current,
        CompactComplexNonleafRoleParentContinuation.placement,CompactComplexNonleafRoleSplit.placement,
        InjectivePlacement.active_slot] using
        storage_outside_raw (stackCount:=stackCount) (roleCount:=roles) (⟨8,by omega⟩ : Fin (10+stackCount)) port)]
  rw [active_update_outside placement _ current (fun port => by
      simpa only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.current,
        CompactComplexNonleafRoleParentContinuation.placement,CompactComplexNonleafRoleSplit.placement,
        InjectivePlacement.active_slot] using
        storage_outside_raw (stackCount:=stackCount) (roleCount:=roles) (⟨7,by omega⟩ : Fin (10+stackCount)) port)]
  have sourcePlacement : placement (s:=stackCount) (c:=roles)
      (Fin.castAdd _ (nativeSourceIndex (roleCount:=roles)))=
      CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount) (c:=roles) := by
    simpa only [CompactComplexNonleafRoleParentContinuation.placement,
      CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot] using
      native_source_slot (stackCount:=stackCount) (roleCount:=roles)
  rw [←sourcePlacement,active_update_inside,initialRawSource]
  exact native_source_update rawState _ _

private theorem storage_injective : Function.Injective (storage (s:=stackCount) (c:=roles)) := by
  intro firstPort secondPort portsEqual
  apply Fin.ext
  have portValues := congrArg Fin.val portsEqual
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at portValues
  omega

private theorem extra_ne_saved (auxPort : Fin 2) (pcStack : Fin stackCount) :
    CompactComplexNonleafRoleParentPayloadContinuation.extra (s:=stackCount) (c:=roles) auxPort≠
      CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack := by
  intro portsEqual
  have portValues := congrArg Fin.val portsEqual
  have pcStackBound := pcStack.isLt
  simp only [CompactComplexNonleafRoleParentPayloadContinuation.extra,
    CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portValues
  unfold CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at portValues
  omega

/-- A physical saved-PC pop retains each distinct captured stack port exactly. -/
theorem popped_snapshot_storage
    (snapshot : CompactComplexSourceReadyReachedDormantFrameInvariant.Snapshot stackCount)
    (inputBank : Tapes (tapes stackCount roles) 2)
    (framesSettled : CompactComplexSourceReadyReachedDormantFrameInvariant.Settled snapshot
      (SharedBank.payload inputBank storage)
      (SharedBank.payload inputBank CompactComplexNonleafRoleParentPayloadContinuation.extra))
    (pcStack : Fin stackCount) (olderWord : ℤ → Fin 6) (olderHead : ℤ)
    (storagePort : Fin (10+stackCount))
    (portProtected : CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      snapshot.headerStack snapshot.liveStack snapshot.pcStack storagePort)
    (portNotPopped : storagePort≠Fin.natAdd 10 pcStack) :
    (CompactComplexAlignedPoppedReturnReadiness.popped inputBank pcStack olderWord olderHead).head (storage storagePort)=
      snapshot.storage.head storagePort ∧
    (CompactComplexAlignedPoppedReturnReadiness.popped inputBank pcStack olderWord olderHead).tape (storage storagePort)=
      snapshot.storage.tape storagePort := by
  have portDistinct : storage (s:=stackCount) (c:=roles) storagePort≠
      CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack := by
    intro portsEqual
    exact portNotPopped (storage_injective portsEqual)
  have capturedPort := CompactComplexSourceReadyReachedDormantFrameInvariant.settled_storage framesSettled storagePort portProtected
  simpa only [CompactComplexAlignedPoppedReturnReadiness.popped,setTape,
    Function.update_of_ne portDistinct,SharedBank.payload] using capturedPort

/-- Both auxiliary physical ports survive the actual saved-PC pop. -/
theorem popped_extra (inputBank : Tapes (tapes stackCount roles) 2)
    (pcStack : Fin stackCount) (olderWord : ℤ → Fin 6) (olderHead : ℤ) (auxPort : Fin 2) :
    (CompactComplexAlignedPoppedReturnReadiness.popped inputBank pcStack olderWord olderHead).head
      (CompactComplexNonleafRoleParentPayloadContinuation.extra auxPort)=
        inputBank.head (CompactComplexNonleafRoleParentPayloadContinuation.extra auxPort) ∧
    (CompactComplexAlignedPoppedReturnReadiness.popped inputBank pcStack olderWord olderHead).tape
      (CompactComplexNonleafRoleParentPayloadContinuation.extra auxPort)=
        inputBank.tape (CompactComplexNonleafRoleParentPayloadContinuation.extra auxPort) := by
  simp only [CompactComplexAlignedPoppedReturnReadiness.popped,setTape,
    Function.update_of_ne (extra_ne_saved auxPort pcStack),and_self]

end Literal

section Entered
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyReachedEventInvariant (caller)
open CompactComplexSourceReadyCapturedChildFrames (childOutput)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexSourceReadyChildEntryPath (selected)
open CompactComplexNonleafRoleChildBank (storage)
variable {basisStateCount leftBoundary childExponent rowCount logColumns precision basePrecision growthConstant axesUsed baseline levels frames returnedVolume scalarPrefix parentLive : ℕ}
  (rowCoordinate : Fin shape.chunk) (parentVisit : Visit shape.active leftBoundary (childExponent+2))
  (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  {pcStack : Fin stackCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackCount roles) 2}
  (parentReached : Reached (parent rowCoordinate parentVisit activeFitsAxes pair) rowCount logColumns precision
    (childExponent+2) basePrecision growthConstant axesUsed baseline levels frames returnedVolume scalarPrefix parentLive
    pcStack stackOrigin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

private theorem caller_storage (storagePort : Fin (10+stackCount)) :
    (caller parentReached).head (CompactComplexNonleafRoleReturnFrame.oldSlot storagePort)=parentReached.storage.head storagePort ∧
    (caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot storagePort)=parentReached.storage.tape storagePort := by
  have callerPrefix := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent rowCoordinate parentVisit activeFitsAxes pair) rowCount logColumns precision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux (CompactComplexSpectatorTargetBank.oldSlot storagePort)
  have storageBankPort := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent rowCoordinate parentVisit activeFitsAxes pair) rowCount logColumns precision)
    parentReached.tail parentReached.storage parentReached.payload storagePort
  exact ⟨callerPrefix.1.trans storageBankPort.1,callerPrefix.2.trans storageBankPort.2⟩

/-- The literal actual entry has the pushed original call association, including
its genuine old stack word and fixed stack origin. -/
theorem entered_associated (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    let entryBank := childOutput rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
    CompactComplexSourceReadySavedCallHistory.Associated stackOrigin (call::savedCalls)
      (entryBank.tape (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack))
      (entryBank.head (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)) := by
  have parentAssociation := CompactComplexAlignedReturnedDormantFrames.parent_saved_associated parentReached
  have callerPort := caller_storage rowCoordinate parentVisit activeFitsAxes pair parentReached (Fin.natAdd 10 pcStack)
  rw [←callerPort.1,←callerPort.2] at parentAssociation
  exact CompactComplexSourceReadySavedCallHistory.child_entry_push call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached)
    parentReached.targetValue parentLive headerStack pcStack liveStack pcDistinctHeader pcDistinctLive
    stackOrigin savedCalls parentAssociation

/-- A genuinely stopped actual child entry executes the classifier, pre/post
orientations, leaf body and saved-PC pop on the fixed aligned table. -/
theorem stopped_prefix (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (parentPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+2) levels frames returnedVolume)
    (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    (metadataFits : basePrecision+2*shape.bits≤precision) (baselineFits : baseline≤basePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childRowsPositive : 0<rowCount/roles) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (unitPayload : shape.payload=1)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true) :
    let entryBank := childOutput rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
    let childResult := CompactComplexCorrectedStoppedChildGridSemantics.installed call (rowCount/roles) logColumns
      (precision-2*shape.bits) rowCoordinate (Visit.child parentVisit call.slot)
      (oriented call (selectedArray parentReached call))
    let completedBank := CompactComplexSourceReadyStoppedLeafCount.returned entryBank
      (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
    ∃ olderWord olderHead,
      CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead ∧
      ∃ elapsedSteps≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume (rowCount/roles) shape logColumns precision+1+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
          CompactComplexSourceReadyOrientationInvariants.constant+1)*
          CompactNativeRoleTransferBudget.volume (rowCount/roles) shape logColumns precision*(arity^(childExponent+1)))+1+
          (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)),
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length 0)
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
  let entryBank := childOutput rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  let childStage := CompactComplexChildHeadersData.child rowCoordinate parentVisit activeFitsAxes pair call.slot
  let childDependency := CompactRecursiveDependencyBudget.Path.child parentPath call
  have association := entered_associated rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
    pcDistinctHeader pcDistinctLive
  have reachedAssociation := CompactComplexSourceReadySavedCallHistory.ready_associated pcStack stackOrigin (call::savedCalls)
    entryBank (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2) association
  have entryHeaders := CompactComplexChildInputReadiness.entered_headers call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have entrySource := CompactComplexChildInputReadiness.entered_source call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have entryCurrent := CompactComplexChildInputReadiness.entered_current call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have callerLive := caller_storage rowCoordinate parentVisit activeFitsAxes pair parentReached (⟨7,by omega⟩ : Fin (10+stackCount))
  have childLive : entryBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      entryBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits parentLive) :=
    ⟨entryCurrent.1.trans (callerLive.1.trans parentReached.live.1),
      entryCurrent.2.trans (callerLive.2.trans parentReached.live.2)⟩
  have entryTarget := CompactComplexChildInputReadiness.entered_target call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have entryExponent := CompactComplexChildInputReadiness.entered_exponent call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have entryReady := CompactComplexChildInputReadiness.entered_stop_ready call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have entryDimension := CompactComplexChildInputReadiness.entered_dimension call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have metadataWidthFits : 2*shape.bits≤precision := by omega
  have sourceWidth := CompactComplexSourceReadyReachedChildInvariant.selected_width parentReached call metadataWidthFits
  have childLiveBound : parentLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows baseline
      (levels+1) (frames+arity^(childExponent+2))
      (returnedVolume+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1)) 0 := by
    apply CompactComplexDenominatorCapacity.child_entry CompactComplexDenominatorCapacity.scalarRows baseline levels frames returnedVolume
      (CompactFramedScalarGrid.rows scalarPrefix).length parentLive (childExponent+1) call
      (CompactComplexDenominatorCapacity.actual_prefix scalarPrefix)
    exact parentReached.upper_ledger.trans (by unfold CompactComplexDenominatorCapacity.ledger; omega)
  have sourceRoleFits : childStage.source.val≤arity := Nat.le_of_lt childStage.source.isLt
  have targetRoleFits : childStage.target.val≤arity := Nat.le_of_lt childStage.target.isLt
  have childRightFits : childStage.right≤shape.active := Nat.sub_le _ _
  obtain ⟨olderWord,olderHead,restoredAssociation,elapsedSteps,timeBound,execution⟩ :=
    CompactComplexAlignedStoppedChildRun.stopped_child_return_width basisProgram headerStack pcStack liveStack call
      shape (rowCount/roles) logColumns precision rowCoordinate childDependency childStage.right childStage.source.val childStage.target.val
      parentLive entryBank (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
      (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime) stackOrigin savedCalls reachedAssociation
      (selectedArray parentReached call) guardPositive axesPositive childRowsPositive metadataWidthFits sourceWidth baseline entryHeaders
      entrySource childLive entryTarget entryExponent.2 entryExponent.1 CompactComplexDenominatorCapacity.scalarRows 0
      unitPayload childRightFits sourceRoleFits targetRoleFits (by omega) (by omega) denominatorRoom childLiveBound
      activeFitsAxes entryReady entryDimension childStopped
  rw [returned_oriented] at execution
  exact ⟨olderWord,olderHead,restoredAssociation,elapsedSteps,timeBound,execution⟩

/-- Actual normalized child array installed by the stopped route. -/
def stoppedResult := CompactComplexCorrectedStoppedChildGridSemantics.installed call (rowCount/roles) logColumns
  (precision-2*shape.bits) rowCoordinate (Visit.child parentVisit call.slot)
  (oriented call (selectedArray parentReached call))

/-- Literal public bank before the real decoded saved-PC pop. -/
def stoppedBank := CompactComplexSourceReadyStoppedLeafCount.returned
  (childOutput rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack)
  (CompactSpectatorLeafAxis.word (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call))
  (parentLive+arity^(childExponent+1))

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

/-- All classifier, stopped-body and saved-PC joins paid before restoration. -/
def prefixCost (childRowCount : ℕ) (runtimeShape : Shape) (runtimeLogColumns runtimePrecision runtimeExponent : ℕ) :=
  (CompactComplexSourceReadyOrientationInvariants.constant+4*CompactComplexSourceReadyGuard.guardConstant+1)*
    CompactNativeRoleTransferBudget.volume childRowCount runtimeShape runtimeLogColumns runtimePrecision+1+
    (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+CompactComplexSourceReadyOrientationInvariants.constant+1)*
      CompactNativeRoleTransferBudget.volume childRowCount runtimeShape runtimeLogColumns runtimePrecision*(arity^(runtimeExponent+1)))+1+
      (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5))


/- Compose across abstract arrays and public banks before specializing to the
   actual stopped child. This keeps dependent endpoint conversion shallow. -/
/-- Physical restoration and original inverse-basis pass, including both table joins. -/
def returnCost (basisWidth : ℕ)
    (guardSufficient : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (slotsCorrect : (parent rowCoordinate parentVisit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate parentVisit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate parentVisit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth) :=
    let stage := parent rowCoordinate parentVisit activeFitsAxes pair
    let basisOccurrence := CompactComplexRolePhaseSite.pc call.site
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) logColumns precision
      guardSufficient guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput logColumns
      (CompactComplexActualCallAlignment.nativeCost basisWidth basisInput slotsCorrect basisOccurrence true
        (ActivePrefixStageNativePolynomial.symbols (2^logColumns) (NativePolynomialStageShape.width shape precision)) basisPacked)
    timeConstant roles*CompactNativeRoleTransferBudget.volume rowCount shape logColumns precision+1+
      CompactComplexActualCallRoleAlignment.cost roles stage rowCount logColumns precision passTime+1

/-- Exact restored-parent and inverse-basis witnesses, their unchanged-table
execution, original next-call PC, literal output bank and charged total runtime.
The named predicate keeps specialization nominal without weakening endpoints. -/
def ReturnOutcome
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (basisWidth : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardSufficient : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (slotsCorrect : (parent rowCoordinate parentVisit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate parentVisit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate parentVisit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth)
    (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+CompactComplexCompletedLiveLower.schedule.length)+2))
    (initialBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (totalBudget : ℕ) : Prop :=
    let stage := parent rowCoordinate parentVisit activeFitsAxes pair
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let basisOccurrence := CompactComplexRolePhaseSite.pc call.site
    let restoredMidpoint := mid selectedRole (caller parentReached) returnedBank headerStack liveStack (parentReached.storage.tape (Fin.natAdd 10 headerStack)) (parentReached.storage.head (Fin.natAdd 10 headerStack)) (parentReached.storage.tape (Fin.natAdd 10 liveStack)) (parentReached.storage.head (Fin.natAdd 10 liveStack)) (childExponent+2) parentLive (parentLive+(arity^(childExponent+1)))
      rowCoordinate parentVisit activeFitsAxes pair rowCount logColumns precision (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles)
      (NativeZeroPadding.word (NativeZeroPaddingArray.word childResult))
    let restoredStorage := CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart restoredMidpoint)
      (parentLive+(arity^(childExponent+1))) (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) (parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount))) parentReached.targetValue
    let restoredParentBank := canonical (returnedCaller parentReached selectedRole (arity^(childExponent+1)) childResult (controlPart restoredMidpoint) (queuePart restoredMidpoint)
      parentReached.scalar (tailPart restoredMidpoint) restoredStorage) parentReached.aux
    let basisInput := CompactComplexSourceReadyReachedBasisInvariant.input stage (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive
    let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) basisInput logColumns
      (CompactComplexActualCallAlignment.nativeCost basisWidth basisInput slotsCorrect basisOccurrence true
        (ActivePrefixStageNativePolynomial.symbols (2^logColumns) (NativePolynomialStageShape.width shape precision)) basisPacked)
    ∃ returnedReached : Reached stage rowCount logColumns precision (childExponent+2) basePrecision growthConstant axesUsed baseline levels frames (returnedVolume+(arity^(childExponent+1))) scalarPrefix
      (parentLive+(arity^(childExponent+1))) pcStack stackOrigin savedCalls restoredParentBank,
      returnedReached.data=returnedData parentReached selectedRole (arity^(childExponent+1)) childResult ∧
      let afterBasisArray := basisArray stage (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisOccurrence true
        (returnedReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
      ∃ finalReached : Reached stage rowCount logColumns precision (childExponent+2) basePrecision growthConstant axesUsed baseline levels frames (returnedVolume+(arity^(childExponent+1))) scalarPrefix
        (parentLive+(arity^(childExponent+1))) pcStack stackOrigin savedCalls (canonical (replacementCaller returnedReached selectedRole afterBasisArray) returnedReached.aux),
        finalReached.data=replacementData returnedReached selectedRole afterBasisArray ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage rowCount logColumns precision passTime : ℝ)≤
          basisConstant*ActivePrefixStageInverseBudget.scale basisInput ∧
        ∃ elapsedSteps≤totalBudget,
          CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
            startPC initialBank elapsedSteps
            (CompactComplexScheduledPCLayout.callNextPC call)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready
              (canonical (replacementCaller returnedReached selectedRole afterBasisArray) returnedReached.aux))))

private theorem prepend_return
    (childResult : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (returnedBank : Tapes (CompactComplexNonleafRoleChildBank.tapes stackCount roles) 2)
    (basisWidth : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (guardSufficient : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (childRowsPositive : 0<rowCount/roles)
    (slotsCorrect : (parent rowCoordinate parentVisit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate parentVisit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate parentVisit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth)
    (startPC : Fin (CompactComplexScheduledPCLayout.originalCount+(4+CompactComplexCompletedLiveLower.schedule.length)+2))
    (initialBank : Tapes (CompactComplexActualCallFullAlignment.tapes stackCount roles) prime)
    (prefixSteps prefixBudget : ℕ) (prefixBound : prefixSteps≤prefixBudget)
    (prefixPath : CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      startPC initialBank prefixSteps (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2))))
    (joined : ReturnOutcome rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack childResult returnedBank
      basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked
      (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
      (returnCost rowCoordinate parentVisit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked)) :
    ReturnOutcome rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack childResult returnedBank
      basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked startPC initialBank (prefixBudget+(returnCost rowCoordinate parentVisit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked)) := by
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
      CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rowCoordinate parentVisit activeFitsAxes pair call.slot) (rowCount/roles) logColumns precision) (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns childResult roles))
    (headerWord : returnedBank.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames (parentReached.storage.tape (Fin.natAdd 10 headerStack)) (parentReached.storage.head (Fin.natAdd 10 headerStack))
      (CompactComplexControllerChildPrefix.data (parent rowCoordinate parentVisit activeFitsAxes pair)))
    (headerHead : returnedBank.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top (parentReached.storage.head (Fin.natAdd 10 headerStack))
      (CompactComplexControllerChildPrefix.data (parent rowCoordinate parentVisit activeFitsAxes pair)))
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
          (parent rowCoordinate parentVisit activeFitsAxes pair).rho (parent rowCoordinate parentVisit activeFitsAxes pair).left
          (parent rowCoordinate parentVisit activeFitsAxes pair).f (parent rowCoordinate parentVisit activeFitsAxes pair).slots
          (parent rowCoordinate parentVisit activeFitsAxes pair).right (parent rowCoordinate parentVisit activeFitsAxes pair).source.val
          (parent rowCoordinate parentVisit activeFitsAxes pair).target.val (caller parentReached)).head CompactComplexNonleafRoleEntry.stack ∧
      returnedBank.tape (CompactComplexNonleafRoleParentPayloadContinuation.extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) shape rowCount logColumns precision
          (parent rowCoordinate parentVisit activeFitsAxes pair).rho (parent rowCoordinate parentVisit activeFitsAxes pair).left
          (parent rowCoordinate parentVisit activeFitsAxes pair).f (parent rowCoordinate parentVisit activeFitsAxes pair).slots
          (parent rowCoordinate parentVisit activeFitsAxes pair).right (parent rowCoordinate parentVisit activeFitsAxes pair).source.val
          (parent rowCoordinate parentVisit activeFitsAxes pair).target.val (caller parentReached)).tape CompactComplexNonleafRoleEntry.stack)
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
    (parentPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+2) levels frames returnedVolume)
    (activePositive : 0<shape.active)
    (metadataFits : basePrecision+2*shape.bits≤precision)
    (axesFit : axesUsed+(arity^(childExponent+1))≤shape.bits)
    (growthSufficient : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (advanceBound : (arity^(childExponent+1))≤2*(arity^(childExponent+1)))
    (childGrid : CompactSpectatorInheritedGrid.Grid shape (rowCount/roles) logColumns (precision-2*shape.bits) (parentLive+(arity^(childExponent+1)))
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound basePrecision growthConstant levels (frames+2*(returnedVolume+(arity^(childExponent+1)))+axesUsed))) childResult)
    (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<rowCount)
    (unitPayload : shape.payload=1)
    (slotsCorrect : (parent rowCoordinate parentVisit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ op,1<(parent rowCoordinate parentVisit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate parentVisit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) op) basisWidth)
    (pcDistinctHeader : pcStack≠headerStack)
    (pcDistinctLive : pcStack≠liveStack)
    (countBlank : (storagePart returnedBank).head 0=0 ∧ (storagePart returnedBank).tape 0=(fun _ => blank))
    (control28Blank : (controlPart returnedBank).head 28=0 ∧ (controlPart returnedBank).tape 28=(fun _ => blank))
    (control29Blank : (controlPart returnedBank).head 29=0 ∧ (controlPart returnedBank).tape 29=(fun _ => blank))
    (savedAssociation : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls
      ((storagePart returnedBank).tape (Fin.natAdd 10 pcStack)) ((storagePart returnedBank).head (Fin.natAdd 10 pcStack))) :
    ReturnOutcome rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack childResult returnedBank
      basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked
      (CompactComplexScheduledPCDecode.savedPC call)
      (liftedBank (CompactComplexSourceReadyWorkspace.bank returnedBank
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
      (returnCost rowCoordinate parentVisit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked) := by
  have joined := CompactComplexAlignedJoinedPhysicalReturn.runs
    rowCoordinate parentVisit activeFitsAxes pair call
    rowCount logColumns precision childResult returnedBank
    headerStack pcStack liveStack headerDistinctLive (parentReached.storage.tape (Fin.natAdd 10 headerStack))
    (parentReached.storage.head (Fin.natAdd 10 headerStack)) (childExponent+2) exponentPositive childRowsPositive rowsGrouped
    exponentEquality guardSufficient rawReady headerWord headerHead
    headerTailClean exponentWord exponentHead (parentReached.storage.tape (Fin.natAdd 10 liveStack)) (parentReached.storage.head (Fin.natAdd 10 liveStack))
    parentLive (parentLive+arity^(childExponent+1)) (arity^(childExponent+1)) (arity^(childExponent+1)) progress
    liveWord liveHeadReady currentWord currentHead targetBlankWord
    targetBlankHead liveFrameFree basePrecision growthConstant axesUsed
    baseline levels frames returnedVolume scalarPrefix
    stackOrigin savedCalls parentBank parentReached childWidth
    rolesPositive axesPositive chunkPositive payloadActual clockBlank
    parentReached.scalar scalarBank (parentReached.storage.tape (⟨9,by omega⟩ : Fin (10+stackCount))) (parentReached.storage.head (⟨9,by omega⟩ : Fin (10+stackCount))) ledgerLive
    ledgerLeft ledgerExponent parentLedger targetWord targetHeadReady
    targetFrameFree basisWidth basisProgram basisConstant basisRuns
    parentPath activePositive metadataFits axesFit growthSufficient
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
    (parentPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+2) levels frames returnedVolume)
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
    (axesFit : axesUsed+arity^(childExponent+1)≤shape.bits)
    (growthSufficient : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (progress : CompactComplexChildAlignmentBudget.Progress shape precision parentLive
      (parentLive+arity^(childExponent+1)) (parentLive+arity^(childExponent+1)))
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (parentLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape precision ledgerLive parentReached.targetValue ledgerLeft ledgerExponent)
    (slotsCorrect : (parent rowCoordinate parentVisit activeFitsAxes pair).slots=25^3)
    (basisPacked : ∀ operation,1<(parent rowCoordinate parentVisit activeFitsAxes pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent rowCoordinate parentVisit activeFitsAxes pair)
          (rowCount/roles) logColumns precision guardSufficient guardFitsChunk childRowsPositive) operation) basisWidth) :
    ∃ olderWord olderHead,
      CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead ∧
      ReturnOutcome rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
        (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call)
        (CompactComplexAlignedPoppedReturnReadiness.popped
          (stoppedBank rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack)
          pcStack olderWord olderHead)
        basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length 0)
        (liftedBank (CompactComplexSourceReadyWorkspace.bank
          (childOutput rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack)
          (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
        (prefixCost (rowCount/roles) shape logColumns precision childExponent+
          returnCost rowCoordinate parentVisit activeFitsAxes pair call basisWidth guardSufficient guardFitsChunk childRowsPositive slotsCorrect basisPacked) := by
  let entryBank := childOutput rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  let childResult := stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call
  let completedBank := stoppedBank rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  have resultDefinition : childResult=CompactComplexCorrectedStoppedChildGridSemantics.installed call (rowCount/roles) logColumns
      (precision-2*shape.bits) rowCoordinate (Visit.child parentVisit call.slot)
      (oriented call (selectedArray parentReached call)) := by
    unfold childResult stoppedResult
    rfl
  have bankDefinition : completedBank=CompactComplexSourceReadyStoppedLeafCount.returned entryBank
      (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1)) := by
    unfold completedBank stoppedBank
    rfl
  obtain ⟨olderWord,olderHead,restoredAssociation,prefixSteps,prefixBound,prefixPath⟩ :=
    stopped_prefix rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack basisProgram
      parentPath pcDistinctHeader pcDistinctLive metadataFits baselineFits denominatorRoom childRowsPositive
      (by omega) axesPositive unitPayload childStopped
  rw [ready_frame,ready_frame,←resultDefinition,←bankDefinition] at prefixPath
  let publicPopped := CompactComplexAlignedPoppedReturnReadiness.popped completedBank pcStack olderWord olderHead
  have poppedDefinition : publicPopped=SharedPlacementAlphabet.setTape completedBank
      (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack) olderWord olderHead := by
    unfold publicPopped CompactComplexAlignedPoppedReturnReadiness.popped
    rfl
  rw [←poppedDefinition] at prefixPath
  let snapshot := CompactComplexSourceReadyCapturedChildFrames.snapshot rowCoordinate parentVisit activeFitsAxes pair
    parentReached call headerStack liveStack
  have capturedSettled := CompactComplexSourceReadyCapturedSettledFrames.snapshot_settled
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
    headerDistinctLive pcDistinctHeader pcDistinctLive parentTailsClean
  have beforepopSettled := CompactComplexSourceReadyStoppedSettledFrames.beforepop_settled snapshot call entryBank
    (selectedArray parentReached call) (CompactSpectatorLeafAxis.word childResult)
    (parentLive+arity^(childExponent+1)) capturedSettled
  rw [returned_oriented,←bankDefinition] at beforepopSettled
  have capturedHeaders := CompactComplexSourceReadyCapturedChildFrames.snapshot_headers
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack pcDistinctHeader.symm headerDistinctLive
  have capturedLive := CompactComplexSourceReadyCapturedChildFrames.snapshot_live
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack headerDistinctLive.symm pcDistinctLive.symm
  have capturedTarget := CompactComplexSourceReadyCapturedChildFrames.snapshot_target
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  have capturedPayload := CompactComplexSourceReadyCapturedChildFrames.snapshot_payload
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
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
  have initialRaw := CompactComplexSourceReadyChildEntryPath.public_output_active call rowCoordinate parentVisit activeFitsAxes pair
    rowCount logColumns precision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive
    headerStack pcStack liveStack
  have completedRaw := returned_raw_source entryBank
    (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rowCoordinate parentVisit activeFitsAxes pair call.slot)
      (rowCount/roles) logColumns precision) (rowCount/roles) logColumns
    (selectedArray parentReached call) childResult (parentLive+arity^(childExponent+1)) initialRaw
  rw [←bankDefinition] at completedRaw
  have poppedRaw := (CompactComplexAlignedPoppedReturnPorts.popped_raw_active completedBank pcStack olderWord olderHead).trans completedRaw
  have metadataWidthFits : 2*shape.bits≤precision := by omega
  have selectedSourceEquality : selectedArray parentReached call=
      roleData parentReached (CompactComplexRolePhaseSite.role call.site) := rfl
  have widthResultDefinition := resultDefinition
  rw [selectedSourceEquality] at widthResultDefinition
  have childWidth := installed_width parentReached call rowCoordinate (Visit.child parentVisit call.slot) metadataWidthFits
  dsimp only at childWidth
  rw [←widthResultDefinition] at childWidth
  have childGrid := installed_grid parentReached parentPath call rowCoordinate (Visit.child parentVisit call.slot)
    activePositive metadataFits axesFit growthSufficient dependencyRoom
  rw [←widthResultDefinition] at childGrid
  have headerTailClean := parentTailsClean (Fin.natAdd 10 headerStack) (Or.inl rfl)
  have liveTailClean := parentTailsClean (Fin.natAdd 10 liveStack) (Or.inr (Or.inl rfl))
  have targetTailClean := parentTailsClean (⟨9,by omega⟩ : Fin (10+stackCount)) (Or.inr (Or.inr (Or.inr rfl)))

  have enteredExponent := CompactComplexChildInputReadiness.entered_exponent call rowCoordinate parentVisit activeFitsAxes pair
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
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedScalar := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_scalarPart entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedScalar
  have scalarBank := (CompactComplexAlignedPoppedReturnPorts.popped_scalarPart completedBank pcStack olderWord olderHead).trans
    (returnedScalar.trans entryScalar)
  have entryClock := CompactComplexSourceReadyStoppedChildEntryPorts.child_clock_blank
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedClock := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_clock entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedClock
  have poppedClock := popped_extra completedBank pcStack olderWord olderHead 1
  have clockBlank := And.intro (poppedClock.1.trans (returnedClock.1.trans entryClock.1))
    (poppedClock.2.trans (returnedClock.2.trans entryClock.2))
  have entryCount := CompactComplexSourceReadyStoppedChildEntryPorts.child_count_blank
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedCount := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_count entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1))
  rw [←bankDefinition] at returnedCount
  have poppedCount := CompactComplexAlignedPoppedReturnPorts.popped_small_storage_read completedBank pcStack olderWord olderHead
    (⟨0,by omega⟩ : Fin (10+stackCount)) (by change (0:ℕ)<10;omega)
  have countBlank := And.intro (poppedCount.1.trans (returnedCount.1.trans entryCount.1))
    (poppedCount.2.trans (returnedCount.2.trans entryCount.2))
  have entryControl28 := CompactComplexSourceReadyStoppedChildEntryPorts.child_control28
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
  have returnedControl28 := CompactComplexSourceReadyStoppedChildEntryPorts.stopped_returned_control entryBank
    (CompactSpectatorLeafAxis.word childResult) (parentLive+arity^(childExponent+1)) 28
  rw [←bankDefinition] at returnedControl28
  have poppedControl28 := CompactComplexAlignedPoppedReturnPorts.popped_control_read completedBank pcStack olderWord olderHead 28
  have control28Blank := And.intro (poppedControl28.1.trans (returnedControl28.1.trans entryControl28.1))
    (poppedControl28.2.trans (returnedControl28.2.trans entryControl28.2))
  have entryControl29 := CompactComplexSourceReadyStoppedChildEntryPorts.child_control29
    rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
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
  have joinedOutcome := physical_outcome rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
    childResult publicPopped headerDistinctLive (by omega) childRowsPositive
    rowsGrouped rfl guardSufficient poppedRaw headerWord
    headerHead headerTailClean exponentWord exponentHead progress
    liveWord liveHead currentWord currentHead targetBlankWord
    targetBlankHead (fun cell beyondHead _ => liveTailClean cell beyondHead) childWidth rolesPositive
    axesPositive chunkPositive payloadActual clockBlank scalarBank
    ledgerLive ledgerLeft ledgerExponent parentLedger targetWord
    targetHead (fun cell beyondHead _ => targetTailClean cell beyondHead) basisWidth basisProgram basisConstant
    basisRuns parentPath activePositive metadataFits axesFit
    growthSufficient dependencyRoom (by omega) childGrid guardFitsChunk
    rowsPositive unitPayload slotsCorrect basisPacked pcDistinctHeader
    pcDistinctLive countBlank control28Blank control29Blank projectedAssociation
  refine ⟨olderWord,olderHead,restoredAssociation,?_⟩
  exact prepend_return rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack
    childResult publicPopped basisWidth basisProgram basisConstant guardSufficient guardFitsChunk childRowsPositive
    slotsCorrect basisPacked
    (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount CompactComplexCompletedLiveLower.schedule.length 0)
    (liftedBank (CompactComplexSourceReadyWorkspace.bank entryBank
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)))
    prefixSteps (prefixCost (rowCount/roles) shape logColumns precision childExponent)
    prefixBound prefixPath joinedOutcome

end Entered

end
end IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnPath
