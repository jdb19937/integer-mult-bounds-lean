module

public import IntegerMultBounds.Machine.CompactComplexActualProviderRuntimeSum

/-! The stopped branch of the actual provider recurrence has an explicit
fixed-plus-leaf-width charge. This eliminates the unknown cutoff coefficient
from its geometric sum without assuming any recursive runtime bound. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualCutoffBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexActualProviderRuntime (pathCoefficient)
open CompactComplexActualProviderRuntimeSum (forcingCoefficient)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.sites CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient
  CompactComplexNonleafRolePreparationBudget.constant CompactComplexSourceReadyChildReturnPath.timeConstant
  CompactComplexSourceReadyOrientationInvariants.constant CompactComplexSourceReadyGuard.guardConstant
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

/-- The symbolic fixed stopped work includes every prefix and child boundary. -/
def cutoffFixedFactor (boundary scalar groups calls entry restoration orientation guard address : ℕ) :=
  boundary+(scalar+groups+calls*(entry+restoration+4+orientation+4*guard+1+address+7))

def cutoffLeafFactor (calls leaf orientation : ℕ) := calls*(leaf+orientation+1)

def cutoffFixedCoefficient : ℕ := cutoffFixedFactor
  CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient
  CompactComplexScheduleRuntimeBudget.scalarCoefficient CompactComplexScheduleRuntimeBudget.groupCount
  ComplexRank25.rankSum
  (CompactComplexNonleafRolePreparationBudget.constant roles ComplexRecursiveCallSchema.sites.length)
  (CompactComplexSourceReadyChildReturnPath.timeConstant roles)
  CompactComplexSourceReadyOrientationInvariants.constant CompactComplexSourceReadyGuard.guardConstant
  (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))

def cutoffLeafCoefficient : ℕ := cutoffLeafFactor ComplexRank25.rankSum
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant CompactComplexSourceReadyOrientationInvariants.constant

def basisCoefficient (shape : Shape) (basisConstant : ℝ) : ℝ :=
  6*(ComplexRank25.rankSum : ℝ)*basisConstant*(shape.guard : ℝ)^Parameters.tau

theorem basis_nonnegative (shape : Shape) (basisConstant : ℝ) (constantNonnegative : 0≤basisConstant) :
    0≤basisCoefficient shape basisConstant :=
  mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤6) (Nat.cast_nonneg _)) constantNonnegative)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem cutoff_algebra
    (boundary scalar groups calls entry restoration orientation guard leaf address width : ℕ)
    (basis widthPower recursive : ℝ) (stopped : Bool) (childrenStopped : stopped=true) :
    (boundary : ℝ)+
      (((scalar+groups+calls*(entry+restoration+4+
        if stopped then orientation+4*guard+1+(leaf+orientation+1)*width+address+7 else 0) : ℕ) : ℝ)+
        basis*widthPower)+(if stopped then 0 else recursive)=
      (cutoffFixedFactor boundary scalar groups calls entry restoration orientation guard address : ℝ)+
        (cutoffLeafFactor calls leaf orientation : ℝ)*width+basis*widthPower := by
  rw [childrenStopped]
  simp only [ite_true]
  unfold cutoffFixedFactor cutoffLeafFactor
  push_cast
  ring

/-- The exact stopped successor charge comes from the actual classifier
branch, complete stopped prefix and both real basis passes. -/
theorem stopped_coefficient_eq (shape : Shape) (basisConstant : ℝ) (childExponent : ℕ)
    (childrenStopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true) :
    pathCoefficient shape basisConstant (childExponent+1)=
      (cutoffFixedCoefficient : ℝ)+(cutoffLeafCoefficient : ℝ)*(arity^(childExponent+1) : ℕ)+
        basisCoefficient shape basisConstant*((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau :=
  cutoff_algebra
    CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient
    CompactComplexScheduleRuntimeBudget.scalarCoefficient CompactComplexScheduleRuntimeBudget.groupCount
    ComplexRank25.rankSum
    (CompactComplexNonleafRolePreparationBudget.constant roles ComplexRecursiveCallSchema.sites.length)
    (CompactComplexSourceReadyChildReturnPath.timeConstant roles)
    CompactComplexSourceReadyOrientationInvariants.constant CompactComplexSourceReadyGuard.guardConstant
    CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
    (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
    (arity^(childExponent+1)) (basisCoefficient shape basisConstant)
    (((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau)
    ((ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)
    (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) childrenStopped

/-- Exponent zero and every genuine positive stopped cutoff have the same
explicit fixed-plus-width allowance; no desired total-cost premise is used. -/
theorem stopped_coefficient_le (shape : Shape) (basisConstant : ℝ)
    (constantNonnegative : 0≤basisConstant) (leafExponent : ℕ)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped shape.axes leafExponent=true) :
    pathCoefficient shape basisConstant leafExponent≤
      (cutoffFixedCoefficient : ℝ)+(cutoffLeafCoefficient : ℝ)*(arity^leafExponent : ℕ)+
        basisCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau := by
  cases leafExponent with
  | zero =>
    exact add_nonneg
      (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_nonneg (basis_nonnegative shape basisConstant constantNonnegative)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  | succ childExponent =>
    exact (stopped_coefficient_eq shape basisConstant childExponent cutoffStopped).le

private theorem combine_cutoff (root fixed leaf basis forcing localConstant width widthPower : ℝ) :
    root+(fixed+leaf*width+basis*widthPower)+forcing*widthPower*localConstant=
      root+fixed+leaf*width+(basis+forcing*localConstant)*widthPower := by
  ring

/-- The same actual root coefficient is bounded with all cutoff work now
explicit. Leaf width and local tau power remain distinct, exactly as in the
original stopped recurrence. -/
theorem root_cutoff_bound (shape : Shape) (basisConstant : ℝ)
    (constantNonnegative : 0≤basisConstant) (childExponent leafExponent depth nativeVolume : ℕ)
    (nodeExponent : childExponent+1=leafExponent+depth)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped shape.axes leafExponent=true)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped shape.axes (leafExponent+1)=false) :
    ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
      CompactComplexActualProviderRuntime.localCoefficient shape basisConstant childExponent+
      if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
        (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)*
        (nativeVolume : ℝ)≤
      ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
        cutoffFixedCoefficient+(cutoffLeafCoefficient : ℝ)*(arity^leafExponent : ℕ)+
        (basisCoefficient shape basisConstant+forcingCoefficient shape basisConstant*
          CompactComplexRecursiveRuntimeSum.localConstant)*
          ((arity^leafExponent : ℕ) : ℝ)^Parameters.tau)*
        (nativeVolume : ℝ)*((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
  have sumBound := CompactComplexActualProviderRuntimeSum.root_coefficient_bound shape basisConstant
    constantNonnegative childExponent leafExponent depth nativeVolume nodeExponent aboveCutoff
  have cutoffBound := stopped_coefficient_le shape basisConstant constantNonnegative leafExponent cutoffStopped
  have coefficientBound := add_le_add (add_le_add
    (le_refl (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)) cutoffBound)
    (le_refl (forcingCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
      CompactComplexRecursiveRuntimeSum.localConstant))
  have combined := combine_cutoff
    (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)
    (cutoffFixedCoefficient : ℝ) (cutoffLeafCoefficient : ℝ)
    (basisCoefficient shape basisConstant) (forcingCoefficient shape basisConstant)
    CompactComplexRecursiveRuntimeSum.localConstant (arity^leafExponent : ℕ)
    (((arity^leafExponent : ℕ) : ℝ)^Parameters.tau)
  rw [combined] at coefficientBound
  exact sumBound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficientBound (Nat.cast_nonneg nativeVolume))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- A genuine nonstopped root determines an original stopping cutoff below
its schedule exponent. The cutoff and every suffix level come from the real
classifier, rather than a caller-supplied recursion-depth oracle. -/
theorem exists_cutoff (axes scheduleExponent : ℕ)
    (rootNonstopped : ComplexRecursiveCallSchema.stopped axes (scheduleExponent+1)=false) :
    ∃ leafExponent depth,scheduleExponent=leafExponent+depth ∧
      ComplexRecursiveCallSchema.stopped axes leafExponent=true ∧
      ComplexRecursiveCallSchema.stopped axes (leafExponent+1)=false := by
  have existsNonstopped : ∃ exponent,ComplexRecursiveCallSchema.stopped axes exponent=false :=
    ⟨scheduleExponent+1,rootNonstopped⟩
  let firstNonstopped := Nat.find existsNonstopped
  have firstNonstoppedSpec : ComplexRecursiveCallSchema.stopped axes firstNonstopped=false :=
    Nat.find_spec existsNonstopped
  have firstPositive : 0<firstNonstopped := by
    by_contra notPositive
    have firstZero : firstNonstopped=0 := by omega
    rw [firstZero] at firstNonstoppedSpec
    have zeroStopped := (ComplexRecursiveCallSchema.stopped_iff axes 0).2 (Or.inl rfl)
    rw [zeroStopped] at firstNonstoppedSpec
    contradiction
  have firstBelowRoot : firstNonstopped≤scheduleExponent+1 :=
    Nat.find_min' existsNonstopped rootNonstopped
  let leafExponent := firstNonstopped-1
  have leafBeforeFirst : leafExponent<firstNonstopped := by dsimp only [leafExponent]; omega
  have leafStopped : ComplexRecursiveCallSchema.stopped axes leafExponent=true := by
    cases leafClassifier : ComplexRecursiveCallSchema.stopped axes leafExponent with
    | false => exact False.elim (Nat.find_min existsNonstopped leafBeforeFirst leafClassifier)
    | true => rfl
  have aboveCutoff : ComplexRecursiveCallSchema.stopped axes (leafExponent+1)=false := by
    have aboveEquation : leafExponent+1=firstNonstopped := by dsimp only [leafExponent]; omega
    rw [aboveEquation]
    exact firstNonstoppedSpec
  refine ⟨leafExponent,scheduleExponent-leafExponent,?_,leafStopped,aboveCutoff⟩
  dsimp only [leafExponent]
  omega

/-- The explicit cutoff coefficient, with separate leaf and local powers. -/
def cutoffCoefficient (shape : Shape) (basisConstant : ℝ) (leafExponent : ℕ) : ℝ :=
  (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
    cutoffFixedCoefficient+(cutoffLeafCoefficient : ℝ)*(arity^leafExponent : ℕ)+
    (basisCoefficient shape basisConstant+forcingCoefficient shape basisConstant*
      CompactComplexRecursiveRuntimeSum.localConstant)*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau

private theorem rescale_algebra (coefficient nativeVolume leafScale depthScale : ℝ)
    (leafScaleNonzero : leafScale≠0) :
    coefficient*nativeVolume*depthScale=(coefficient/leafScale)*nativeVolume*(leafScale*depthScale) := by
  field_simp

/-- The explicit actual-root bound is expressed in the original uncontracted
width. Dividing by the retained cutoff sigma power exposes the manuscript's
separate leaf and local contributions, without a supplied cost premise. -/
theorem original_width_bound (shape : Shape) (basisConstant : ℝ)
    (constantNonnegative : 0≤basisConstant) (childExponent leafExponent depth nativeVolume : ℕ)
    (nodeExponent : childExponent+1=leafExponent+depth)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped shape.axes leafExponent=true)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped shape.axes (leafExponent+1)=false) :
    ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
      CompactComplexActualProviderRuntime.localCoefficient shape basisConstant childExponent+
      if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
        (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)*
        (nativeVolume : ℝ)≤
      (cutoffCoefficient shape basisConstant leafExponent/((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma)*
        (nativeVolume : ℝ)*((arity^(leafExponent+depth) : ℕ) : ℝ)^Parameters.sigma := by
  have bound := root_cutoff_bound shape basisConstant constantNonnegative childExponent leafExponent depth
    nativeVolume nodeExponent cutoffStopped aboveCutoff
  have leafScalePositive : 0<((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma :=
    Real.rpow_pos_of_pos (by exact_mod_cast (pow_pos (by decide : 0<arity) leafExponent)) _
  have widthEquation : ((arity^(leafExponent+depth) : ℕ) : ℝ)^Parameters.sigma=
      ((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma*((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
    rw [pow_add,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  apply bound.trans_eq
  rw [widthEquation]
  exact rescale_algebra (cutoffCoefficient shape basisConstant leafExponent) (nativeVolume : ℝ)
    (((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma) (((arity^depth : ℕ) : ℝ)^Parameters.sigma)
    leafScalePositive.ne'

/-- Every genuine nonstopped root has the explicit original-width estimate
with its stopping cutoff constructed internally from the actual classifier. -/
theorem root_original_width_bound (shape : Shape) (basisConstant : ℝ)
    (constantNonnegative : 0≤basisConstant) (childExponent nativeVolume : ℕ)
    (rootNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+2)=false) :
    ∃ leafExponent depth,childExponent+1=leafExponent+depth ∧
      ComplexRecursiveCallSchema.stopped shape.axes leafExponent=true ∧
      ComplexRecursiveCallSchema.stopped shape.axes (leafExponent+1)=false ∧
      ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
        CompactComplexActualProviderRuntime.localCoefficient shape basisConstant childExponent+
        if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
          (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)*
          (nativeVolume : ℝ)≤
        (cutoffCoefficient shape basisConstant leafExponent/((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma)*
          (nativeVolume : ℝ)*((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.sigma := by
  obtain ⟨leafExponent,depth,nodeExponent,cutoffStopped,aboveCutoff⟩ :=
    exists_cutoff shape.axes (childExponent+1) rootNonstopped
  have bound := original_width_bound shape basisConstant constantNonnegative childExponent leafExponent depth
    nativeVolume nodeExponent cutoffStopped aboveCutoff
  rw [←nodeExponent] at bound
  exact ⟨leafExponent,depth,nodeExponent,cutoffStopped,aboveCutoff,bound⟩

end
end IntegerMultBounds.Machine.CompactComplexActualCutoffBudget
