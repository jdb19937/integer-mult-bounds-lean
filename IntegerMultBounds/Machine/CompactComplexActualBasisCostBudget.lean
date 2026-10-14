module

public import IntegerMultBounds.Machine.CompactComplexActualCallRoleAlignment
public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildProvider
public import IntegerMultBounds.Machine.CompactComplexSourceReadyActualScheduleBudget

/-! Uniform cost bounds on the exact basis allowances used by the actual
recursive schedule. These bounds are extracted from the checked physical
machine theorem using one literal fixed-width input, since its cost does
not depend on the coefficient values or caller tapes. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualBasisCostBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactRecursiveDependencyBudget (Path)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount

/-- The literal selected-role allowance, including header setup/restoration
and the codec lifecycle, is independent of the data stored in its records. -/
def roleCost {shape : Shape} (packingLimit roleCount : ℕ) (stage : Stage shape) (rows ell precision : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (childRowsPositive : 0<rows/roleCount) (stageSlots : stage.slots=25^3)
    (stagePacked : ∀ operation,1<stage.f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (NativePolynomialStageShape.inputs stage (rows/roleCount) ell precision
          guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (basisPC : Fin CompactAllAxisPhaseDispatch.count) (reverse : Bool) :=
  let basisInput := NativePolynomialStageShape.inputs stage (rows/roleCount) ell precision
    guardPositive guardFitsChunk childRowsPositive
  let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roleCount)
    basisInput ell (CompactComplexActualCallAlignment.nativeCost packingLimit basisInput stageSlots basisPC reverse
      (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width shape precision)) stagePacked)
  CompactComplexActualCallRoleAlignment.cost roleCount stage rows ell precision passTime

/-- One fixed coefficient bounds the actual cost of both basis directions
for every genuine stage and literal record width. No runtime-bound premise
or supplied coefficient array is needed. -/
theorem exists_role_cost_bound (packingLimit roleCount : ℕ) (rolesPositive : 0<roleCount) :
    ∃ basisConstant : ℝ,0<basisConstant ∧
    ∀ (shape : Shape) (stage : Stage shape) (rows ell precision : ℕ)
      (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
      (_rowsPositive : 0<rows) (childRowsPositive : 0<rows/roleCount) (_rolesDivideRows : roleCount∣rows)
      (_unitPayload : shape.payload=1) (stageSlots : stage.slots=25^3)
      (stagePacked : ∀ operation,1<stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (NativePolynomialStageShape.inputs stage (rows/roleCount) ell precision
            guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
      (basisPC : Fin CompactAllAxisPhaseDispatch.count) (reverse : Bool),
      (roleCost packingLimit roleCount stage rows ell precision guardPositive guardFitsChunk childRowsPositive
        stageSlots stagePacked basisPC reverse : ℝ)≤
      basisConstant*ActivePrefixStageInverseBudget.scale
        (NativePolynomialStageShape.inputs stage (rows/roleCount) ell precision
          guardPositive guardFitsChunk childRowsPositive) := by
  obtain ⟨stateCount,basisProgram,basisConstant,constantPositive,physicalRuns⟩ :=
    CompactComplexActualCallRoleAlignment.exists_program packingLimit roleCount rolesPositive
  refine ⟨basisConstant,constantPositive,?_⟩
  intro shape stage rows ell precision guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows
    unitPayload stageSlots stagePacked basisPC reverse
  let basisInput := NativePolynomialStageShape.inputs stage (rows/roleCount) ell precision
    guardPositive guardFitsChunk childRowsPositive
  let recordWidth := NativePolynomialStageShape.width shape precision
  let coefficients : Fin (ActivePrefixStageTripleWords.count basisInput) → Fin (2^ell) → Coefficient :=
    fun _ _ => (List.replicate recordWidth 0,List.replicate recordWidth 0)
  have coefficientWidths : ∀ row polynomial,
      (coefficients row polynomial).1.length=recordWidth ∧
      (coefficients row polynomial).2.length=recordWidth := by
    intro row polynomial
    simp [coefficients]
  let selectedRole : Fin roleCount := ⟨0,rolesPositive⟩
  let sourceSlot : Fin (1+roleCount) := ⟨1,by omega⟩
  let sourceWord := SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
    (ActivePrefixStageNativePolynomial.rows basisInput coefficients coefficientWidths)))
  let payload := SharedPlacementAlphabet.setTape (SharedBank.empty (1+roleCount) 2) sourceSlot sourceWord 0
  have sourceTape : payload.tape ⟨selectedRole.val+1,by omega⟩=sourceWord := by
    change (SharedPlacementAlphabet.setTape (SharedBank.empty (1+roleCount) 2) sourceSlot sourceWord 0).tape sourceSlot=sourceWord
    simp only [SharedPlacementAlphabet.setTape,Function.update_self]
  have sourceHead : payload.head ⟨selectedRole.val+1,by omega⟩=0 := by
    change (SharedPlacementAlphabet.setTape (SharedBank.empty (1+roleCount) 2) sourceSlot sourceWord 0).head sourceSlot=0
    simp only [SharedPlacementAlphabet.setTape,Function.update_self]
  have paid := physicalRuns 44 (SharedBank.empty 44 2) (by omega) payload selectedRole
    shape stage rows ell precision guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload
    stageSlots basisPC reverse stagePacked coefficients coefficientWidths sourceTape sourceHead
  exact paid.2

/-- Specialization to the exact forward/reverse budgets in genuine recursive
events. The coefficient is chosen before the Path, stage or call occurrence. -/
theorem exists_basis_cost_bound (packingLimit : ℕ) :
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
              (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
      (call : ComplexRecursiveCallSchema.Call) (reverse : Bool),
      (CompactComplexSourceReadyRecursiveChildProvider.basisCost phaseCoordinate entryPath activeFits pair
        packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked call reverse : ℝ)≤
      basisConstant*ActivePrefixStageInverseBudget.scale
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive) := by
  have rolesPositive : 0<roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
  obtain ⟨basisConstant,constantPositive,bound⟩ := exists_role_cost_bound packingLimit roles rolesPositive
  refine ⟨basisConstant,constantPositive,?_⟩
  intro shape nodeLeft childExponent levels frames returned rows ell precision phaseCoordinate entryPath activeFits pair
    guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload stageSlots stagePacked call reverse
  exact bound shape (parent phaseCoordinate entryPath.visit activeFits pair) rows ell precision
    guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload stageSlots stagePacked
    (CompactComplexRolePhaseSite.pc call.site) reverse

private theorem nat_sum_real_le {α : Type*} (entries : List α) (cost : α → ℕ) (bound : ℝ)
    (entryBounds : ∀ entry ∈ entries,(cost entry : ℝ)≤bound) :
    ((entries.map cost).sum : ℝ)≤(entries.length : ℝ)*bound := by
  induction entries with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,zero_mul,le_refl]
  | cons entry entries inductionHypothesis =>
    have headBound := entryBounds entry (List.mem_cons_self ..)
    have tailBound := inductionHypothesis (fun tailEntry member => entryBounds tailEntry (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [headBound,tailBound]

/-- Complete actual local work is bounded before every node, call and dynamic
bank. Both physical basis passes use their certified stage scale; scalar,
entry/restoration, stopped bodies and joins retain the proved native-volume
coefficient. Recursive child work is the separate exact schedule sum. -/
theorem exists_local_budget_bound (packingLimit : ℕ) :
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
      ((CompactComplexScheduleRuntimeBudget.scalarCoefficient+CompactComplexScheduleRuntimeBudget.groupCount+
        ComplexRank25.rankSum*CompactComplexSourceReadyActualScheduleBudget.childLocalCoefficient shape childExponent : ℕ) : ℝ)*
        (CompactNativeRoleTransferBudget.volume rows shape ell precision : ℝ)+
      (ComplexRank25.rankSum : ℝ)*(2*basisConstant)*ActivePrefixStageInverseBudget.scale
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive) := by
  obtain ⟨basisConstant,constantPositive,basisBound⟩ := exists_basis_cost_bound packingLimit
  refine ⟨basisConstant,constantPositive,?_⟩
  intro shape nodeLeft childExponent levels frames returned rows ell precision phaseCoordinate entryPath activeFits pair
    guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload stageSlots stagePacked
  let basisCost := fun call reverse => CompactComplexSourceReadyRecursiveChildProvider.basisCost phaseCoordinate entryPath
    activeFits pair packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked call reverse
  let stageScale := ActivePrefixStageInverseBudget.scale
    (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
      (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive)
  have passBound (call : ComplexRecursiveCallSchema.Call) (reverse : Bool) :
      (basisCost call reverse : ℝ)≤basisConstant*stageScale :=
    basisBound phaseCoordinate entryPath activeFits pair guardPositive guardFitsChunk rowsPositive childRowsPositive
      rolesDivideRows unitPayload stageSlots stagePacked call reverse
  have basisSumBound := nat_sum_real_le ComplexRecursiveCallSchema.calls
    (fun call => basisCost call false+basisCost call true) (2*basisConstant*stageScale)
    (by
      intro call _
      have forwardBound := passBound call false
      have reverseBound := passBound call true
      push_cast
      linarith only [forwardBound,reverseBound])
  rw [ComplexRecursiveCallSchema.calls_rankSum] at basisSumBound
  have localBound := CompactComplexSourceReadyActualScheduleBudget.local_le phaseCoordinate entryPath activeFits pair
    packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked rowsPositive
  have localBoundReal := Nat.cast_le (α:=ℝ).mpr localBound
  rw [Nat.cast_add,Nat.cast_mul] at localBoundReal
  change _≤_+((ComplexRecursiveCallSchema.calls.map (fun call => basisCost call false+basisCost call true)).sum : ℝ)
    at localBoundReal
  exact localBoundReal.trans (by nlinarith only [basisSumBound])

end
end IntegerMultBounds.Machine.CompactComplexActualBasisCostBudget
