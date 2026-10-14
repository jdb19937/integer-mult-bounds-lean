module

public import IntegerMultBounds.Machine.CompactComplexActualInverseBasisPullback
public import IntegerMultBounds.Machine.CompactComplexActualEventNetwork
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant

/-! One computed forward basis, recursive child tensor, spectator promotion
and inverse basis has the literal original child-instruction action on stored
decoded slices. Recursive correctness is an equality of decoded child arrays;
there is no machine execution callback or assumed full-network equality. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid half)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray)
open CompactComplexActualBasisSlice (native_slots)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (insert address)
open CompactComplexScalarIntegerRows (wireIndex)
open CompactComplexScalarRowBlock (wireCount)
open Networks
attribute [local irreducible] ComplexRecursiveCallSchema.sites ComplexRank25.program
  CompactComplexRolePhaseSite.roleCount
  CompactComplexScalarIntegerRows.wireIndex CompactComplexScalarRolePorts.roleIndex
  Networks.ComplexFramedExecution.rows CompactFramedScalarGrid.rows
  basisArray CompactComplexSourceReadyReachedBasisInvariant.replacementCaller
  CompactComplexSourceReadyReachedReturnInvariant.returnedCaller
  CompactComplexSourceReadyReachedEventInvariant.canonical

section Node
variable {shape : Shape} {nodeLeft childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rowCount polynomialExponent metadataPrecision : ℕ) (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (rowsPositive : 0<rowCount)

def stored (storagePrecision parentLive : ℕ) (data : Fin wireCount → Array shape rowCount polynomialExponent)
    (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    CompactComplexActualEventNetwork.Stored (arity^(childExponent+1)) :=
  fun wire => slice phaseCoordinate visit anchor (nativeField storagePrecision parentLive (data (wireIndex wire)) row polynomialIndex)

def computedData (call : ComplexRecursiveCallSchema.Call) (denominatorAdvance : ℕ)
    (data : Fin wireCount → Array shape rowCount polynomialExponent) (result : Array shape rowCount polynomialExponent) :=
  fun arrayIndex => if arrayIndex=wireIndex call.role then
    basisArray (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
      (native_slots phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
      (CompactComplexRolePhaseSite.pc call.site) true result
    else CompactComplexChildGridPromoted.promote shape rowCount polynomialExponent denominatorAdvance (data arrayIndex)

/-- The recursive result assertion at the literal selected forward basis
array, retaining outer parentRows, polynomial indices and global spectator bits. -/
def ChildTensor (call : ComplexRecursiveCallSchema.Call) (storagePrecision parentLive denominatorAdvance : ℕ)
    (data : Fin wireCount → Array shape rowCount polynomialExponent) (result : Array shape rowCount polynomialExponent) : Prop :=
  ∀ (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAddress : BinaryWalsh.Address shape.bits),
    let native := nativeField storagePrecision parentLive
      (basisArray (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
        (native_slots phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
        (CompactComplexRolePhaseSite.pc call.site) false (data (wireIndex call.role))) row polynomialIndex
    nativeField storagePrecision (parentLive+denominatorAdvance) result row polynomialIndex globalAddress=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^childExponent)).symm
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress native)
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress)
      else ComplexEndpoints.fullFrame (arity^childExponent)
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress native)
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress)

theorem selected_role_index (call : ComplexRecursiveCallSchema.Call) :
    CompactComplexScalarRolePorts.roleIndex (wireIndex call.role)=
      CompactComplexRolePhaseSite.role call.site := by
  simp only [CompactComplexScalarRolePorts.roleIndex,Equiv.trans_apply,
    Equiv.symm_apply_apply,CompactComplexRolePhaseSite.role,ComplexRecursiveCallSchema.Call.role]

/-- The actual forward replacement, literal normalized return data, and
inverse replacement give precisely computedData. These are individual array
equations emitted by the three readiness witnesses, not arrayIndex whole-bank premise. -/
theorem transition_data (call : ComplexRecursiveCallSchema.Call) (denominatorAdvance : ℕ)
    (data forward returned final : Fin wireCount → Array shape rowCount polynomialExponent) (result : Array shape rowCount polynomialExponent)
    (forwardDataEquation : forward=Function.update data (wireIndex call.role)
      (basisArray (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
        (native_slots phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
        (CompactComplexRolePhaseSite.pc call.site) false (data (wireIndex call.role))))
    (returnedDataEquation : returned=fun arrayIndex => CompactComplexNormalizedSpectatorHandoff.aligned shape rowCount polynomialExponent denominatorAdvance
      (CompactComplexRolePhaseSite.role call.site)
      (fun selectedRole => forward (CompactComplexScalarRolePorts.roleIndex.symm selectedRole)) result
      (CompactComplexScalarRolePorts.roleIndex arrayIndex))
    (finalDataEquation : final=Function.update returned (wireIndex call.role)
      (basisArray (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
        (native_slots phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
        (CompactComplexRolePhaseSite.pc call.site) true (returned (wireIndex call.role)))) :
    final=computedData phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call denominatorAdvance data result := by
  have selectedRoleIndex := selected_role_index call
  have selectedReturnData : returned (wireIndex call.role)=result := by
    rw [returnedDataEquation]
    simp only [CompactComplexNormalizedSpectatorHandoff.aligned,selectedRoleIndex,ite_true]
  rw [finalDataEquation,selectedReturnData]
  funext arrayIndex
  by_cases wireSelected : arrayIndex=wireIndex call.role
  · subst arrayIndex
    simp only [Function.update_self,computedData,ite_true]
  · have roleUnselected : CompactComplexScalarRolePorts.roleIndex arrayIndex≠CompactComplexRolePhaseSite.role call.site := by
      rw [←selectedRoleIndex]
      exact fun indexEquality => wireSelected (CompactComplexScalarRolePorts.roleIndex.injective indexEquality)
    rw [Function.update_of_ne wireSelected,returnedDataEquation,forwardDataEquation]
    simp only [computedData,ite_eq_right wireSelected,CompactComplexNormalizedSpectatorHandoff.aligned,
      ite_eq_right roleUnselected,Equiv.symm_apply_apply,Function.update_of_ne wireSelected]

/-- Spectator promotion preserves arrayIndex decoded original global-address field. -/
theorem promoted_nativeField (storagePrecision parentLive numeratorBound denominatorAdvance : ℕ) (sourceArray : Array shape rowCount polynomialExponent)
    (dataWidth : Width shape rowCount polynomialExponent storagePrecision sourceArray) (dataGrid : Grid shape rowCount polynomialExponent storagePrecision parentLive numeratorBound sourceArray)
    (promotionCapacity : denominatorAdvance≤half shape storagePrecision+1) (promotionGuard : numeratorBound*2^denominatorAdvance<2^(half shape storagePrecision))
    (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAddress : BinaryWalsh.Address shape.bits) :
    nativeField storagePrecision (parentLive+denominatorAdvance) (CompactComplexChildGridPromoted.promote shape rowCount polynomialExponent denominatorAdvance sourceArray) row polynomialIndex globalAddress=
      nativeField storagePrecision parentLive sourceArray row polynomialIndex globalAddress :=
  CompactComplexChildGridAlignment.decode_promotes (half shape storagePrecision) parentLive denominatorAdvance _ _
    (CompactComplexChildGridPromoted.promotes shape rowCount polynomialExponent storagePrecision parentLive numeratorBound denominatorAdvance sourceArray dataWidth dataGrid promotionCapacity promotionGuard _)

/-- Exact computed data performs one actual child instruction. Width, grid,
and promotion guards are the local numerical readiness obligations; tensor
correctness is the recursive decoded-result induction hypothesis. -/
theorem computed_semantics (call : ComplexRecursiveCallSchema.Call) (storagePrecision parentLive numeratorBound denominatorAdvance : ℕ)
    (data : Fin wireCount → Array shape rowCount polynomialExponent) (result : Array shape rowCount polynomialExponent)
    (dataWidth : ∀ arrayIndex,Width shape rowCount polynomialExponent storagePrecision (data arrayIndex)) (dataGrid : ∀ arrayIndex,Grid shape rowCount polynomialExponent storagePrecision parentLive numeratorBound (data arrayIndex))
    (promotionCapacity : denominatorAdvance≤half shape storagePrecision+1) (promotionGuard : numeratorBound*2^denominatorAdvance<2^(half shape storagePrecision))
    (childTensorSemantics : ∀ (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAddress : BinaryWalsh.Address shape.bits),
      let native := nativeField storagePrecision parentLive
        (basisArray (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
          (native_slots phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
          (CompactComplexRolePhaseSite.pc call.site) false (data (wireIndex call.role))) row polynomialIndex
      nativeField storagePrecision (parentLive+denominatorAdvance) result row polynomialIndex globalAddress=
        if call.inverse then (ComplexEndpoints.fullFrame (arity^childExponent)).symm
          (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress native)
          (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress)
        else ComplexEndpoints.fullFrame (arity^childExponent)
          (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress native)
          (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit visit call) globalAddress))
    (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    stored phaseCoordinate visit rowCount polynomialExponent storagePrecision (parentLive+denominatorAdvance)
      (computedData phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call denominatorAdvance data result) row polynomialIndex anchor=
    FramedFactorExecution.run [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
      (stored phaseCoordinate visit rowCount polynomialExponent storagePrecision parentLive data row polynomialIndex anchor) := by
  funext wire arrayIndex
  by_cases wireSelected : wire=call.role
  · subst wire
    simp only [stored,computedData,ite_true,FramedFactorExecution.run,
      CompactComplexActualEventNetwork.childInstruction,FramedFactorExecution.execute,Function.update_self]
    change nativeField storagePrecision (parentLive+denominatorAdvance)
      (basisArray (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
        (native_slots phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
        (CompactComplexRolePhaseSite.pc call.site) true result) row polynomialIndex (insert phaseCoordinate visit anchor arrayIndex)=_
    have factorSemantics := CompactComplexActualInverseBasisPullback.returned_factor_at phaseCoordinate visit activeFits pair
      rowCount polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call storagePrecision parentLive (parentLive+denominatorAdvance) (data (wireIndex call.role)) result
      row polynomialIndex (insert phaseCoordinate visit anchor arrayIndex) (childTensorSemantics row polynomialIndex)
    have sliceEquality : slice phaseCoordinate visit (insert phaseCoordinate visit anchor arrayIndex)
        (nativeField storagePrecision parentLive (data (wireIndex call.role)) row polynomialIndex)=
        slice phaseCoordinate visit anchor (nativeField storagePrecision parentLive (data (wireIndex call.role)) row polynomialIndex) := by
      funext sliceAddress
      unfold slice
      erw [CompactComplexActualBasisPullback.insert_insert]
    rw [sliceEquality] at factorSemantics
    erw [CompactComplexNonleafChildAddress.address_insert] at factorSemantics
    exact factorSemantics
  · have selectedIndex : wireIndex wire≠wireIndex call.role := fun indexEquality => wireSelected (wireIndex.injective indexEquality)
    simp only [stored,computedData,ite_eq_right selectedIndex,FramedFactorExecution.run,
      CompactComplexActualEventNetwork.childInstruction,FramedFactorExecution.execute,
      Function.update_of_ne wireSelected]
    exact promoted_nativeField rowCount polynomialExponent storagePrecision parentLive numeratorBound denominatorAdvance (data (wireIndex wire))
      (dataWidth _) (dataGrid _) promotionCapacity promotionGuard row polynomialIndex (insert phaseCoordinate visit anchor arrayIndex)

end Node

section Reached
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix parentLive pcStack origin calls v)

/-- Genuine Reached and dependency geometry discharge every numerical premise
of computed_semantics for the actual stored parent data. -/
theorem numerical_inputs {dependencyLeft denominatorAdvance : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes+denominatorAdvance≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    (∀ arrayIndex,Width shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentReached.data arrayIndex)) ∧
    (∀ arrayIndex,Grid shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume+completedAxes))) (parentReached.data arrayIndex)) ∧
    denominatorAdvance≤half shape (metadataPrecision-2*shape.bits)+1 ∧
    CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume+completedAxes))*2^denominatorAdvance<
      2^(half shape (metadataPrecision-2*shape.bits)) := by
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  refine ⟨?_,?_,CompactComplexSourceReadyReachedReturnInvariant.promotion_guard
    path denominatorAdvance activePositive precisionReserve axesFit growthReserve chunkRoom⟩
  · intro arrayIndex
    have dataWidth := CompactComplexSourceReadyReachedReturnInvariant.role_width parentReached metadataFits
      (CompactComplexScalarRolePorts.roleIndex arrayIndex)
    simpa only [CompactComplexSourceReadyReachedReturnInvariant.roleData,Equiv.symm_apply_apply] using dataWidth
  · intro arrayIndex
    have dataGrid := CompactComplexSourceReadyReachedReturnInvariant.role_grid parentReached metadataFits
      (CompactComplexScalarRolePorts.roleIndex arrayIndex)
    simpa only [CompactComplexSourceReadyReachedReturnInvariant.roleData,Equiv.symm_apply_apply] using dataGrid

end Reached

section ActualReached
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedBasisInvariant (replacementCaller replacementData)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller returnedData)
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix parentLive pcStack origin calls v)

/-- The three actual readiness witnesses on their exact canonical banks
realize the original instruction. Their individual data equations are the
outputs of basis_reached, returned_reached and inverse basis_reached. Every
numerical premise is derived from the original parent; only actual recursive
tensor correctness remains semantic input. -/
theorem reached_child_semantics {dependencyLeft childExponent denominatorAdvance childVolume : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active dependencyLeft (childExponent+2))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (parentStage : stage=CompactComplexChildHeadersData.parent phaseCoordinate visit activeFits pair)
    (_nodeExponentEquation : nodeExponent=childExponent+2) (call : ComplexRecursiveCallSchema.Call)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (rowsPositive : 0<parentRows/roles)
    (stageSlots : stage.slots=25^3)
    (path : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes+denominatorAdvance≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (result : Array shape (parentRows/roles) polynomialExponent)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+extraTapes) 2) (aux : Tapes 2 2)
    (childTensorSemantics : ChildTensor phaseCoordinate visit activeFits pair (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call
      (metadataPrecision-2*shape.bits) parentLive denominatorAdvance parentReached.data result) :
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let forwardArray := basisArray stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive stageSlots
      (CompactComplexRolePhaseSite.pc call.site) false
      (parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    ∀ forward : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix parentLive pcStack origin calls
      (canonical (replacementCaller parentReached selectedRole forwardArray) parentReached.aux),
      forward.data=replacementData parentReached selectedRole forwardArray →
    ∀ restored : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume (returnedVolume+childVolume) scalarPrefix
      (parentLive+denominatorAdvance) pcStack origin calls
      (canonical (returnedCaller forward selectedRole denominatorAdvance result control queue scalar tail storage) aux),
      restored.data=returnedData forward selectedRole denominatorAdvance result →
    let inverseArray := basisArray stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive stageSlots
      (CompactComplexRolePhaseSite.pc call.site) true
      (restored.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    ∀ final : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume (returnedVolume+childVolume) scalarPrefix
      (parentLive+denominatorAdvance) pcStack origin calls
      (canonical (replacementCaller restored selectedRole inverseArray) restored.aux),
      final.data=replacementData restored selectedRole inverseArray →
    ∀ (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits),
      stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentLive+denominatorAdvance) final.data row polynomialIndex anchor=
      FramedFactorExecution.run [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
        (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive parentReached.data row polynomialIndex anchor) := by
  dsimp only
  intro forward forwardDataEquation restored restoredDataEquation final finalDataEquation row polynomialIndex anchor
  have selectedIndex : CompactComplexScalarRolePorts.roleIndex.symm
      (CompactComplexRolePhaseSite.role call.site)=wireIndex call.role := by
    rw [←selected_role_index call,Equiv.symm_apply_apply]
  have forwardEquation := forwardDataEquation
  have returnedEquation := restoredDataEquation
  have inverseEquation := finalDataEquation
  simp only [replacementData,selectedIndex] at forwardEquation inverseEquation
  subst stage
  have dataEquation := transition_data phaseCoordinate visit activeFits pair (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
    call denominatorAdvance parentReached.data forward.data restored.data final.data result forwardEquation returnedEquation inverseEquation
  obtain ⟨dataWidth,dataGrid,promotionCapacity,promotionGuard⟩ := numerical_inputs parentReached path activePositive precisionReserve axesFit growthReserve chunkRoom
  rw [dataEquation]
  exact computed_semantics phaseCoordinate visit activeFits pair (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call
    (metadataPrecision-2*shape.bits) parentLive
    (CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume+completedAxes))) denominatorAdvance
    parentReached.data result dataWidth dataGrid promotionCapacity promotionGuard childTensorSemantics row polynomialIndex anchor

end ActualReached
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics
