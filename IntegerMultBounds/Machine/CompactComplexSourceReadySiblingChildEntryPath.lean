module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildInvariant
public import IntegerMultBounds.Machine.CompactComplexNonleafRolePreparationBudget

/-! Paid literal child entry after actual counted siblings uses a genuine
immutable node-entry saved-target ledger and the genuine current child-entry
live ledger. Header costs derive separately from these real certificates;
no fictitious advanced parent Path or execution callback is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEntryPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent)
open CompactNativeRoleTransferBudget (volume)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexNonleafRoleChildBank (cost coreCost)
open CompactComplexNonleafRoleChildBankBudget (coreConstant core_bound constant)
open CompactComplexNonleafRolePreparation (entryCost quotientCost)
open CompactComplexNonleafRolePreparationBudget (quotient_cost_linear childEntryCost)
variable {shape : Shape} {nodeLeft childExponent stackCount roleCount siteCount : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexFramedExecution.rows CompactComplexRolePhaseSite.roleCount
  CompactComplexCompletedLiveLower.schedule CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

private theorem bank_cost_linear (siteCount savedTarget parentLive : ℕ) (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active nodeLeft (childExponent+2)) (activeFits : shape.active≤shape.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rowCount polynomialExponent metadataPrecision : ℕ)
    (liveLength : (bits parentLive).length≤volume rowCount shape polynomialExponent metadataPrecision+1)
    (targetLength : (bits savedTarget).length≤volume rowCount shape polynomialExponent metadataPrecision+1)
    (rowsPositive : 0<rowCount) (guardPositive : 0<shape.guard) :
    cost siteCount savedTarget parentLive (childExponent+2) phaseCoordinate visit activeFits pair coordinate rowCount polynomialExponent metadataPrecision≤
      constant siteCount*volume rowCount shape polynomialExponent metadataPrecision := by
  have liveBitsBound := liveLength
  have targetBitsBound := targetLength
  have coreBound := core_bound siteCount phaseCoordinate visit activeFits pair coordinate rowCount polynomialExponent metadataPrecision
  have dimensionVolume := CompactComplexControllerChildBudget.dimension_square_le_volume (s:=shape) rowCount polynomialExponent metadataPrecision rowsPositive (by omega)
  have chargedDimension := Nat.mul_le_mul_left (coreConstant siteCount) dimensionVolume
  have nativeVolumePositive : 0<volume rowCount shape polynomialExponent metadataPrecision := Nat.mul_pos rowsPositive
    (CompactNativeRoleTransferBudget.symbols_pos shape polynomialExponent metadataPrecision)
  unfold cost constant
  nlinarith


private theorem child_entry_cost_linear (selected : Fin roleCount) (savedTarget parentLive : ℕ) (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active nodeLeft (childExponent+2)) (activeFits : shape.active≤shape.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rowCount polynomialExponent metadataPrecision : ℕ)
    (liveLength : (bits parentLive).length≤volume (rowCount/roleCount) shape polynomialExponent metadataPrecision+1)
    (targetLength : (bits savedTarget).length≤volume (rowCount/roleCount) shape polynomialExponent metadataPrecision+1)
    (rowsPositive : 0<rowCount) (childRowsPositive : 0<rowCount/roleCount) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) :
    childEntryCost (s:=stackCount) (siteCount:=siteCount) selected savedTarget parentLive phaseCoordinate visit activeFits pair coordinate rowCount polynomialExponent metadataPrecision≤
      CompactComplexNonleafRolePreparationBudget.constant roleCount siteCount*volume rowCount shape polynomialExponent metadataPrecision := by
  have entryCostBound := CompactComplexNonleafRoleEntryBudget.cost_linear (s:=10+stackCount) selected shape rowCount polynomialExponent metadataPrecision
    (parent phaseCoordinate visit activeFits pair).rho (parent phaseCoordinate visit activeFits pair).left
    (parent phaseCoordinate visit activeFits pair).f (parent phaseCoordinate visit activeFits pair).slots
    (parent phaseCoordinate visit activeFits pair).right (parent phaseCoordinate visit activeFits pair).source.val
    (parent phaseCoordinate visit activeFits pair).target.val rowsPositive axesPositive guardPositive chunkPositive
  have quotientCostBound := quotient_cost_linear roleCount shape rowCount polynomialExponent metadataPrecision
    (parent phaseCoordinate visit activeFits pair).rho (parent phaseCoordinate visit activeFits pair).left
    (parent phaseCoordinate visit activeFits pair).f (parent phaseCoordinate visit activeFits pair).slots
    (parent phaseCoordinate visit activeFits pair).right (parent phaseCoordinate visit activeFits pair).source.val
    (parent phaseCoordinate visit activeFits pair).target.val rowsPositive
  have childCost := bank_cost_linear siteCount savedTarget parentLive phaseCoordinate visit activeFits pair coordinate
    (rowCount/roleCount) polynomialExponent metadataPrecision liveLength targetLength childRowsPositive guardPositive
  have childVolume := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols shape polynomialExponent metadataPrecision) (Nat.div_le_self rowCount roleCount)
  have childCostBound := childCost.trans (Nat.mul_le_mul_left (CompactComplexNonleafRoleChildBankBudget.constant siteCount) childVolume)
  change CompactComplexNonleafRoleChildBank.cost siteCount savedTarget parentLive (childExponent+2)
    phaseCoordinate visit activeFits pair coordinate (rowCount/roleCount) polynomialExponent metadataPrecision≤
    CompactComplexNonleafRoleChildBankBudget.constant siteCount*volume rowCount shape polynomialExponent metadataPrecision
    at childCostBound
  have nativeVolumePositive : 0<volume rowCount shape polynomialExponent metadataPrecision := Nat.mul_pos rowsPositive
    (CompactNativeRoleTransferBudget.symbols_pos shape polynomialExponent metadataPrecision)
  change entryCost (10+stackCount) selected shape rowCount polynomialExponent metadataPrecision _ _ _ _ _ _ _≤_ at entryCostBound
  unfold childEntryCost CompactComplexNonleafRolePreparationBudget.constant
  nlinarith only [entryCostBound,quotientCostBound,childCostBound,nativeVolumePositive]


section Parent
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadyChildEntryPath (selected)
open CompactComplexSourceReadySiblingChildInvariant (childPublic)
variable {basisStateCount dependencyLevels frameVolume entryReturned eventIndex parentRows polynomialExponent metadataPrecision
    baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
    (phaseCoordinate : Fin shape.chunk)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
      dependencyLevels frameVolume entryReturned)
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackCount} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackCount roles) 2}
    (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent
      metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) scalarPrefix parentLive pcStack origin calls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call)

private theorem caller_storage (storagePort : Fin (10+stackCount)) :
    (caller parentReached).head (CompactComplexNonleafRoleReturnFrame.oldSlot storagePort)=parentReached.storage.head storagePort ∧
    (caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot storagePort)=parentReached.storage.tape storagePort := by
  have callerPrefix := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux (CompactComplexSpectatorTargetBank.oldSlot storagePort)
  have hb := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload storagePort
  exact ⟨callerPrefix.1.trans hb.1,callerPrefix.2.trans hb.2⟩


/-- Actual source-ready child entry executes with its original paid bound.
The pending target is certified by an immutable genuine node-entry ledger;
current live capacity comes independently from the scheduled child's Path. -/
theorem child_entry_runs (headerStack liveStack : Fin stackCount)
    (ledgerLive ledgerLeft ledgerExponent : ℕ)
    (savedLedger : CompactComplexNonleafRoleChildBankBudget.Ledger shape metadataPrecision ledgerLive
      parentReached.targetValue ledgerLeft ledgerExponent)
    (eventBound : eventIndex<CompactComplexCompletedLiveLower.schedule.length)
    (eventEquation : CompactComplexCompletedLiveLower.schedule[eventIndex]=CompactComplexCompletedLiveLower.Event.child call)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childRowsPositive : 0<parentRows/roles) (guardPositive : 0<shape.guard)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) :
    HoareTime (CompactComplexSourceReadyChildEntryPath.program headerStack pcStack liveStack call)
      (fun result => result=parentBank)
      (fun result => result=CompactComplexSourceReadyWorkspace.ready
        (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack))
      (CompactComplexSourceReadyChildEntryPath.bound (sh:=shape) parentRows polynomialExponent metadataPrecision) := by
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have entered := CompactComplexSourceReadySiblingChildInvariant.scheduled_child_entered phaseCoordinate
    entryPath activeFits pair parentReached call headerStack liveStack pcHeaderDistinct pcLiveDistinct
    metadataFits growthReserve eventBound eventEquation
  have currentHeaderVolume := CompactComplexDenominatorCapacity.target_volume entered.path
    CompactComplexDenominatorCapacity.scalarRows baselineLive (metadataPrecision-2*shape.bits) 0
    parentLive parentLive (parentRows/roles) polynomialExponent (by omega) (by omega) denominatorRoom
    entered.upper_ledger (Nat.le_add_right _ _) childRowsPositive
  have streamVolumeEquation := CompactComplexSpectatorVolumeHeaders.volume_semantic shape 1
    (parentRows/roles) polynomialExponent metadataPrecision false metadataFits
  change CompactComplexSpectatorVolumeHeaders.streamVolume shape 1 (parentRows/roles) polynomialExponent metadataPrecision false=
    ButterflySpectatorGeometry.Size (parentRows/roles) shape.bits (2^polynomialExponent)*
      (2*(CompactSpectatorInheritedGrid.half shape (metadataPrecision-2*shape.bits)+2)) at streamVolumeEquation
  rw [←streamVolumeEquation] at currentHeaderVolume
  have liveVolume : parentLive≤volume (parentRows/roles) shape polynomialExponent metadataPrecision := by
    simpa only [CompactComplexSpectatorVolumeHeaders.streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,
      Bool.false_eq_true,ite_false,volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
      CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using currentHeaderVolume
  have liveLength : (bits parentLive).length≤volume (parentRows/roles) shape polynomialExponent metadataPrecision+1 :=
    (ActiveRepairRankHeadersCommands.bits_length parentLive).trans (Nat.add_le_add_right liveVolume 1)
  have targetLength := (CompactComplexNonleafRoleChildBankBudget.header_lengths metadataPrecision ledgerLive
    parentReached.targetValue ledgerLeft ledgerExponent (parentRows/roles) polynomialExponent savedLedger childRowsPositive).2
  have exponentReady := CompactComplexSourceReadyReachedEventInvariant.child_exponent parentReached
  rw [parentReached.exponentValue_eq] at exponentReady
  have callerTarget := caller_storage phaseCoordinate entryPath activeFits pair parentReached ⟨8,by omega⟩
  have callerLive := caller_storage phaseCoordinate entryPath activeFits pair parentReached ⟨7,by omega⟩
  have parentRowsPositive : 0<parentRows := by
    have hmul : 0<parentRows/roles*roles := Nat.mul_pos childRowsPositive (by norm_num [roles,CompactComplexRolePhaseSite.roleCount])
    exact lt_of_lt_of_le hmul (Nat.div_mul_le_self parentRows roles)
  have sourceBlank := CompactComplexSourceReadyReachedEventInvariant.child_source parentReached
  have targetDescriptor : (caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits parentReached.targetValue) := by
    exact (callerTarget.2.trans parentReached.target.2).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have liveDescriptor : (caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits parentLive) := by
    exact (callerLive.2.trans parentReached.live.2).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have roleSources : ∀ role,(caller parentReached).head (CompactComplexNonleafRoleEntry.roleTape role)=0 ∧
      RoleArrayStack.Supported ((caller parentReached).tape (CompactComplexNonleafRoleEntry.roleTape role))
        (CompactComplexSpectatorVolumeHeaders.streamVolume shape roles parentRows polynomialExponent metadataPrecision true) := by
    intro role
    have callerPrefix := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
      (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
        (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
        parentReached.tail parentReached.storage parentReached.payload) parentReached.aux (CompactComplexNativeRoleBridge.roleSlot role)
    have roleWord := parentReached.role_words (CompactComplexScalarRolePorts.roleIndex.symm role)
    simp only [Equiv.apply_symm_apply] at roleWord
    refine ⟨callerPrefix.1.trans roleWord.1,?_⟩
    simpa only [Equiv.apply_symm_apply] using
      CompactComplexSourceReadyReachedEventInvariant.child_role_supported parentReached (CompactComplexScalarRolePorts.roleIndex.symm role)
  have selectedSource : (caller parentReached).tape (CompactComplexNonleafRoleEntry.roleTape (selected call))=
      NativeZeroPadding.word (NativeZeroPaddingArray.word (selectedArray parentReached call)) := by
    have callerPrefix := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
      (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
        (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
        parentReached.tail parentReached.storage parentReached.payload) parentReached.aux (CompactComplexNativeRoleBridge.roleSlot (selected call))
    have roleWord := parentReached.role_words (CompactComplexScalarRolePorts.roleIndex.symm (selected call))
    simp only [Equiv.apply_symm_apply] at roleWord
    exact callerPrefix.2.trans roleWord.2
  have rawRuns := CompactComplexNonleafRolePreparation.child_entry_from_caller_runs
    (selected call) phaseCoordinate entryPath.visit activeFits pair call.slot parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached)
    parentReached.targetValue parentLive headerStack pcStack liveStack call.site exponentReady
    targetDescriptor (callerTarget.1.trans parentReached.target.1) liveDescriptor (callerLive.1.trans parentReached.live.1)
    (by norm_num [roles,CompactComplexRolePhaseSite.roleCount]) parentRowsPositive childRowsPositive guardPositive axesPositive chunkPositive
    (CompactComplexSourceReadyReachedEventInvariant.child_headers parentReached)
    (CompactComplexSourceReadyReachedEventInvariant.child_clock parentReached)
    ⟨sourceBlank.1,by rw [sourceBlank.2]; intro z hz; rfl⟩ roleSources selectedSource
  have costBound := child_entry_cost_linear (stackCount:=stackCount)
    (siteCount:=Networks.ComplexRecursiveCallSchema.sites.length) (selected call) parentReached.targetValue parentLive
    phaseCoordinate entryPath.visit activeFits pair call.slot parentRows polynomialExponent metadataPrecision liveLength targetLength parentRowsPositive childRowsPositive guardPositive axesPositive chunkPositive
  have paidRuns := rawRuns.consequence (fun _ equality => equality) (fun _ equality => equality) costBound
  have fullRuns := CompactComplexSourceReadyWorkspace.public_runs paidRuns
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)
  have parentBankEquation : parentBank=CompactComplexSourceReadyWorkspace.ready ((caller parentReached).append (SharedBank.empty 7 2)) :=
    parentReached.canonical_bank
  exact fullRuns.consequence (fun _ hz => hz.trans parentBankEquation) (fun _ hz => hz) le_rfl

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEntryPath
