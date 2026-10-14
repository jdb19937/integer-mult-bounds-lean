module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingReturnInvariant

/-! Actual child-event semantics after counted siblings. The forward, returned
and inverse Reached witnesses realize the original instruction using guards
from the node-entry Path and current cursor. Recursive tensor correctness is
still an induction obligation; no advanced dependency Path is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEventSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid half)
open CompactComplexSourceReadyChildEventSemantics
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open Networks
open CompactComplexSourceReadyReachedBasisInvariant (basisArray)
open CompactComplexScalarIntegerRows (wireIndex)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

section Reached
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume entryReturned eventIndex siblingVolume scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex siblingVolume) scalarPrefix parentLive pcStack origin calls v)

/-- Genuine Reached and dependency geometry discharge every numerical premise
of computed_semantics for the actual stored parent data. -/
theorem numerical_inputs {dependencyLeft denominatorAdvance : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (childFitsNode : siblingVolume ≤ arity ^ nodeExponent)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes+denominatorAdvance≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    (∀ arrayIndex,Width shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentReached.data arrayIndex)) ∧
    (∀ arrayIndex,Grid shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*(returnedCursor entryReturned eventIndex siblingVolume)+completedAxes))) (parentReached.data arrayIndex)) ∧
    denominatorAdvance≤half shape (metadataPrecision-2*shape.bits)+1 ∧
    CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*(returnedCursor entryReturned eventIndex siblingVolume)+completedAxes))*2^denominatorAdvance<
      2^(half shape (metadataPrecision-2*shape.bits)) := by
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  refine ⟨?_,?_,CompactComplexSourceReadySiblingReturnInvariant.promotion_guard
    entryPath eventIndex siblingVolume scalarPrefix baselinePrecision growthConstant completedAxes denominatorAdvance metadataPrecision childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom⟩
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
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume entryReturned eventIndex siblingVolume scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex siblingVolume) scalarPrefix parentLive pcStack origin calls v)

/-- The three actual readiness witnesses on their exact canonical banks
realize the original instruction. Their individual data equations are the
outputs of basis_reached, returned_reached and inverse basis_reached. Every
numerical premise is derived from the original entry Path and actual parent cursor; only actual recursive
tensor correctness remains semantic input. -/
theorem reached_child_semantics {dependencyLeft childExponent denominatorAdvance childVolume : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active dependencyLeft (childExponent+2))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (parentStage : stage=CompactComplexChildHeadersData.parent phaseCoordinate visit activeFits pair)
    (_nodeExponentEquation : nodeExponent=childExponent+2) (call : ComplexRecursiveCallSchema.Call)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk) (rowsPositive : 0<parentRows/roles)
    (stageSlots : stage.slots=25^3)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume entryReturned)
    (childFitsNode : siblingVolume ≤ arity ^ nodeExponent)
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
    ∀ forward : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex siblingVolume) scalarPrefix parentLive pcStack origin calls
      (canonical (replacementCaller parentReached selectedRole forwardArray) parentReached.aux),
      forward.data=replacementData parentReached selectedRole forwardArray →
    ∀ restored : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume ((returnedCursor entryReturned eventIndex siblingVolume)+childVolume) scalarPrefix
      (parentLive+denominatorAdvance) pcStack origin calls
      (canonical (returnedCaller forward selectedRole denominatorAdvance result control queue scalar tail storage) aux),
      restored.data=returnedData forward selectedRole denominatorAdvance result →
    let inverseArray := basisArray stage (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive stageSlots
      (CompactComplexRolePhaseSite.pc call.site) true
      (restored.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    ∀ final : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume ((returnedCursor entryReturned eventIndex siblingVolume)+childVolume) scalarPrefix
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
  obtain ⟨dataWidth,dataGrid,promotionCapacity,promotionGuard⟩ := numerical_inputs parentReached entryPath childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom
  rw [dataEquation]
  exact computed_semantics phaseCoordinate visit activeFits pair (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call
    (metadataPrecision-2*shape.bits) parentLive
    (CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*(returnedCursor entryReturned eventIndex siblingVolume)+completedAxes))) denominatorAdvance
    parentReached.data result dataWidth dataGrid promotionCapacity promotionGuard childTensorSemantics row polynomialIndex anchor

end ActualReached

end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEventSemantics
