module

public import IntegerMultBounds.Machine.CompactComplexActualBasisCostBudget
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren
public import IntegerMultBounds.Machine.CompactComplexCorrectedNonleafBoundaryBudget

/-! The actual polynomial basis scale has the original per-depth width
power. Complete nonleaf child boundary costs match the corrected checked
boundary expression, leaving the actual event budget as its only addend. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexRecursiveStageScaleBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.sites CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- Codec expansion costs exactly three native volumes. The polynomial
shape retains the original guard and stage width, so its certified scale
is bounded by the original native volume and width power. -/
theorem stage_scale_le {shape : Shape} (stage : Stage shape) (rows ell precision : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (childRowsPositive : 0<rows/roles) :
    ActivePrefixStageInverseBudget.scale
      (NativePolynomialStageShape.inputs stage (rows/roles) ell precision
        guardPositive guardFitsChunk childRowsPositive)≤
    3*(volume rows shape ell precision : ℝ)*(shape.guard : ℝ)^Parameters.tau*(stage.f : ℝ)^Parameters.tau := by
  have tauNonnegative := Shared50RecursiveBudgetBound.exponent_range.1.le
  have guardStrict : 0<shape.guard := by omega
  have factorBound : max 1 ((stage.f-1)*shape.guard)≤stage.f*shape.guard :=
    max_le (Nat.mul_pos stage.positiveWidth guardStrict)
      (Nat.mul_le_mul_right shape.guard (Nat.sub_le stage.f 1))
  have factorPowerBound := Real.rpow_le_rpow
    (Nat.cast_nonneg (max 1 ((stage.f-1)*shape.guard)) : (0 : ℝ)≤max 1 ((stage.f-1)*shape.guard))
    (Nat.cast_le (α:=ℝ).mpr factorBound) tauNonnegative
  have childVolumeBound : volume (rows/roles) shape ell precision≤volume rows shape ell precision :=
    Nat.mul_le_mul_right _ (Nat.div_le_self rows roles)
  have scaleEquation : ActivePrefixStageInverseBudget.scale
      (NativePolynomialStageShape.inputs stage (rows/roles) ell precision
        guardPositive guardFitsChunk childRowsPositive)=
      (3*volume (rows/roles) shape ell precision : ℕ)*
        ((max 1 ((stage.f-1)*shape.guard) : ℕ) : ℝ)^Parameters.tau := by
    unfold ActivePrefixStageInverseBudget.scale
    change ((rows/roles)*(NativePolynomialStageShape.shape shape ell precision).recordWidth : ℕ)*
      ((max 1 ((stage.f-1)*shape.guard) : ℕ) : ℝ)^Parameters.tau=_
    rw [NativePolynomialStageHeaderBudget.expanded_volume]
  rw [scaleEquation]
  calc
    (3*volume (rows/roles) shape ell precision : ℕ)*
        ((max 1 ((stage.f-1)*shape.guard) : ℕ) : ℝ)^Parameters.tau≤
      (3*volume rows shape ell precision : ℕ)*((stage.f*shape.guard : ℕ) : ℝ)^Parameters.tau := by
        exact mul_le_mul (Nat.cast_le.mpr (Nat.mul_le_mul_left 3 childVolumeBound)) factorPowerBound
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    _=3*(volume rows shape ell precision : ℝ)*(shape.guard : ℝ)^Parameters.tau*(stage.f : ℝ)^Parameters.tau := by
      rw [Nat.cast_mul,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring

/-- The budget used by actual completed-child certificates is exactly the
checked corrected nonleaf boundary cost plus its genuine event budget. -/
theorem child_path_budget_eq (shape : Shape) (rows ell precision eventBudget : ℕ) :
    CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget shape rows ell precision eventBudget=
    CompactComplexCorrectedNonleafBoundaryBudget.childCost shape rows ell precision+eventBudget := by
  unfold CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget
    CompactComplexCorrectedNonleafBoundaryBudget.childCost CompactComplexCorrectedNonleafBoundaryBudget.childExpression
    CompactComplexAlignedReachedNodeEntryPath.entryCost CompactComplexAlignedReachedFinalReturn.finalCost
  ring

/-- Every original classifier, orientation, entry, finalization and saved-PC
pop is paid with the fixed corrected boundary coefficient, independently
of the actual schedule chosen by the recursive provider. -/
theorem child_path_budget_le (shape : Shape) (rows ell precision eventBudget : ℕ) (rowsPositive : 0<rows) :
    CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget shape rows ell precision eventBudget≤
    CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient*volume rows shape ell precision+eventBudget := by
  rw [child_path_budget_eq]
  exact Nat.add_le_add_right (CompactComplexCorrectedNonleafBoundaryBudget.child_linear rows ell precision rowsPositive) _

/-- One fixed machine coefficient pays complete actual local work at the
original recursion depth. The only width power is the manuscript tau power;
stopped leaf work remains explicitly confined to the real stopped branch. -/
theorem exists_local_depth_bound (packingLimit : ℕ) :
    ∃ basisConstant : ℝ,0<basisConstant ∧
    ∀ {shape : Shape} {nodeLeft childExponent levels frames returned rows ell precision : ℕ}
      (phaseCoordinate : Fin shape.chunk)
      (entryPath : Path shape.active nodeLeft (childExponent+2) levels frames returned)
      (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
      (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
      (_rowsPositive : 0<rows) (childRowsPositive : 0<rows/roles) (_rolesDivideRows : roles∣rows)
      (_unitPayload : shape.payload=1)
      (stageSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
      (stagePacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f →
        ActivePrefixStageRuntimeData.Packed
          (ActivePrefixStagePairData.changePair
            (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
              (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit),
      (CompactComplexSourceReadyActualScheduleBudget.localBudget phaseCoordinate entryPath activeFits pair
        packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked : ℝ)≤
      (((CompactComplexScheduleRuntimeBudget.scalarCoefficient+CompactComplexScheduleRuntimeBudget.groupCount+
          ComplexRank25.rankSum*CompactComplexSourceReadyActualScheduleBudget.childLocalCoefficient shape childExponent : ℕ) : ℝ)+
        6*(ComplexRank25.rankSum : ℝ)*basisConstant*(shape.guard : ℝ)^Parameters.tau*
          ((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau)*
        (volume rows shape ell precision : ℝ) := by
  obtain ⟨basisConstant,constantPositive,localBound⟩ := CompactComplexActualBasisCostBudget.exists_local_budget_bound packingLimit
  refine ⟨basisConstant,constantPositive,?_⟩
  intro shape nodeLeft childExponent levels frames returned rows ell precision phaseCoordinate entryPath activeFits pair
    guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload stageSlots stagePacked
  have paid := localBound phaseCoordinate entryPath activeFits pair guardPositive guardFitsChunk rowsPositive childRowsPositive
    rolesDivideRows unitPayload stageSlots stagePacked
  have scaleBound := stage_scale_le (parent phaseCoordinate entryPath.visit activeFits pair) rows ell precision
    guardPositive guardFitsChunk childRowsPositive
  have stageWidth : (parent phaseCoordinate entryPath.visit activeFits pair).f=arity^(childExponent+1) := rfl
  rw [stageWidth] at scaleBound
  have basisFactorNonnegative : 0≤(ComplexRank25.rankSum : ℝ)*(2*basisConstant) := by positivity
  have enlarged := mul_le_mul_of_nonneg_left scaleBound basisFactorNonnegative
  exact paid.trans (by nlinarith only [enlarged])

end
end IntegerMultBounds.Machine.CompactComplexRecursiveStageScaleBudget
