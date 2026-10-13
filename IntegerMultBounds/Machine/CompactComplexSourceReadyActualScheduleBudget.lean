module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedRecursiveSchedule
public import IntegerMultBounds.Machine.CompactComplexScheduleRuntimeBudget

/-! Exact runtime decomposition of the actual mixed schedule. The local
term contains both original basis passes, physical entry/restoration, all
joins and the complete stopped body. Only nonstopped child execution is
left in the recursive sum, once per original call occurrence. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyActualScheduleBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexScalarIntegerRows (GroupIndex)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.sites ComplexRecursiveCallSchema.calls schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexCallReturn.addressCount
  CompactComplexCallReturn.addressWidth

private theorem map_sum_add {α : Type*} (entries : List α) (leftCost rightCost : α → ℕ) :
    (entries.map (fun entry => leftCost entry+rightCost entry)).sum=
      (entries.map leftCost).sum+(entries.map rightCost).sum := by
  induction entries with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
    simp only [List.map_cons,List.sum_cons,inductionHypothesis]
    omega

private theorem map_zero_sum {α : Type*} (entries : List α) :
    (entries.map (fun _ => (0 : ℕ))).sum=0 := by
  induction entries with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
    simp only [List.map_cons,List.sum_cons,inductionHypothesis,Nat.zero_add]

/-- The complete actual stopped prefix, including classifier, orientations,
leaf execution, saved-PC pop and joins, has this fixed per-volume charge. -/
def stoppedPrefixCoefficient (exponent : ℕ) :=
  CompactComplexSourceReadyOrientationInvariants.constant+4*CompactComplexSourceReadyGuard.guardConstant+1+
  (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
    CompactComplexSourceReadyOrientationInvariants.constant+1)*arity^(exponent+1)+
  CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+7

theorem stopped_prefix_linear (shape : Shape) (rows ell precision exponent : ℕ) (rowsPositive : 0<rows) :
    CompactComplexAlignedStoppedReturnPath.prefixCost rows shape ell precision exponent≤
      stoppedPrefixCoefficient exponent*volume rows shape ell precision := by
  have volumePositive := Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape ell precision)
  change 0<volume rows shape ell precision at volumePositive
  have joinBound := Nat.le_mul_of_pos_right
    (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+7) volumePositive
  unfold CompactComplexAlignedStoppedReturnPath.prefixCost stoppedPrefixCoefficient
  nlinarith only [joinBound]

/-- Actual quotient-row serialization gives the precise child volume; the
same symbol width is retained rather than replaced by a recursive estimate. -/
theorem child_volume_eq (shape : Shape) (rows ell precision : ℕ) (rolesDivideRows : roles∣rows) :
    volume (rows/roles) shape ell precision=volume rows shape ell precision/roles := by
  have rolesPositive : 0<roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
  have rowsEqual := Nat.div_mul_cancel rolesDivideRows
  unfold volume
  conv_rhs => rw [←rowsEqual]
  rw [Nat.mul_assoc,Nat.mul_comm roles,←Nat.mul_assoc,Nat.mul_div_cancel _ rolesPositive]

/-- Scalar setup, arithmetic, live increments and cleanup already use the
actual record measure, so the original fixed coefficient pays their sum. -/
theorem scalar_sum_linear (shape : Shape) (rows ell precision : ℕ) (rowsPositive : 0<rows) :
    (∑ group : GroupIndex,CompactComplexSourceReadyReachedRecursiveSchedule.scalarBudget
      (shape:=shape) (rowCount:=rows) (polynomialExponent:=ell) (metadataPrecision:=precision) group)≤
    (CompactComplexScheduleRuntimeBudget.scalarCoefficient+CompactComplexScheduleRuntimeBudget.groupCount)*
      volume rows shape ell precision := by
  have scalarEquality (group : GroupIndex) :
      CompactComplexSourceReadyReachedRecursiveSchedule.scalarBudget
        (shape:=shape) (rowCount:=rows) (polynomialExponent:=ell) (metadataPrecision:=precision) group=
      CompactComplexScheduleRuntimeBudget.scalarAllowance shape rows ell precision group := by
    unfold CompactComplexSourceReadyReachedRecursiveSchedule.scalarBudget
      CompactComplexScheduleRuntimeBudget.scalarAllowance CompactNativeRoleHeaders.recordWidth ButterflyGuard.width
    rfl
  simp only [scalarEquality]
  exact CompactComplexScheduleRuntimeBudget.scalar_sum shape rows ell precision rowsPositive

section Node
variable {shape : Shape} {nodeLeft childExponent levels frames returned rows ell precision : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : Path shape.active nodeLeft (childExponent+2) levels frames returned)
  (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  (packingLimit : ℕ) (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
  (childRowsPositive : 0<rows/roles)
  (stageSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
  (stagePacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f →
    ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)

/-- Concrete physical local work for one occurrence; the stopped body is
included only when the original runtime classifier selects that branch. -/
def localChildBudget (call : ComplexRecursiveCallSchema.Call) :=
  CompactComplexSourceReadyRecursiveChildProvider.forwardBudget phaseCoordinate entryPath activeFits pair
    packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked call+
  CompactComplexSourceReadyRecursiveChildProvider.returnBudget phaseCoordinate entryPath activeFits pair
    packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked call+
  if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then
    CompactComplexAlignedStoppedReturnPath.prefixCost (rows/roles) shape ell precision childExponent
  else 0

/-- Every scalar group and every literal call occurrence contributes its
own already specified physical local budget. No total-time premise occurs. -/
def localBudget :=
  (∑ group : GroupIndex,CompactComplexSourceReadyReachedRecursiveSchedule.scalarBudget
    (shape:=shape) (rowCount:=rows) (polynomialExponent:=ell) (metadataPrecision:=precision) group)+
  (ComplexRecursiveCallSchema.calls.map
    (localChildBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
      childRowsPositive stageSlots stagePacked)).sum

theorem event_eq (childPathBudget : ComplexRecursiveCallSchema.Call → ℕ) (event : Event) :
    CompactComplexSourceReadyReachedRecursiveSchedule.eventBudget phaseCoordinate entryPath activeFits pair
      packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked event=
    CompactComplexScheduleRuntimeBudget.weight
      (CompactComplexSourceReadyReachedRecursiveSchedule.scalarBudget
        (shape:=shape) (rowCount:=rows) (polynomialExponent:=ell) (metadataPrecision:=precision))
      (fun call => localChildBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
        childRowsPositive stageSlots stagePacked call+
        if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else childPathBudget call) event := by
  cases event with
  | scalar group => rfl
  | child call =>
    unfold CompactComplexSourceReadyReachedRecursiveSchedule.eventBudget
      CompactComplexScheduleRuntimeBudget.weight localChildBudget
    split_ifs with childrenStopped
    · dsimp only [CompactComplexSourceReadyReachedRecursiveSchedule.stoppedBudget,
        CompactComplexAlignedStoppedReturnPath.returnCost,
        CompactComplexSourceReadyRecursiveChildProvider.forwardBudget,
        CompactComplexSourceReadyRecursiveChildProvider.returnBudget,
        CompactComplexSourceReadyRecursiveChildProvider.basisCost]
      omega
    · unfold CompactComplexSourceReadyRecursiveChildProvider.eventBudget
      dsimp only
      omega

/-- Exact actual schedule cost: local physical work plus the sum of
nonstopped child paths, with repeated call labels charged separately. -/
theorem total_eq (childPathBudget : ComplexRecursiveCallSchema.Call → ℕ) :
    CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
      packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked=
    localBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
      childRowsPositive stageSlots stagePacked+
    if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
      (ComplexRecursiveCallSchema.calls.map childPathBudget).sum := by
  unfold CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget
  have budgetEquality := funext (event_eq phaseCoordinate entryPath activeFits pair packingLimit
    guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked childPathBudget)
  rw [budgetEquality]
  rw [CompactComplexScheduleRuntimeBudget.schedule_sum,map_sum_add]
  unfold localBudget
  split_ifs with childrenStopped
  · rw [map_zero_sum]
    omega
  · exact (Nat.add_assoc _ _ _).symm

/-- The actual child certificates fit the original RuntimeSum recurrence
when their individually certified path budgets fit its child term. Local
physical work stays exact rather than being replaced by an assumed sum. -/
theorem total_le_recursive_sum (childPathBudget : ComplexRecursiveCallSchema.Call → ℕ)
    (leaf : ℕ) (localCost : ℕ → ℕ) (depth : ℕ)
    (childBounds : ∀ call ∈ ComplexRecursiveCallSchema.calls,
      childPathBudget call≤CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows shape ell precision/CompactComplexRecursiveRuntimeSum.roles)) :
    CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
      packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked≤
    localBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
      childRowsPositive stageSlots stagePacked+
      ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows shape ell precision/CompactComplexRecursiveRuntimeSum.roles) := by
  rw [total_eq]
  split_ifs with childrenStopped
  · omega
  · exact Nat.add_le_add_left
      (CompactComplexRecursiveRuntimeSum.child_sum_le childPathBudget leaf localCost depth
        (volume rows shape ell precision) childBounds) _

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyActualScheduleBudget
