module

public import IntegerMultBounds.Machine.CompactComplexCutoffPowers

/-! A single machine coefficient, chosen before all shapes and recursion
exponents, absorbs the original cutoff powers into the uniform stage factor.
The estimate applies to the actual root runtime coefficient. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexUniformRuntimeCoefficient
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexActualCutoffBudget (cutoffCoefficient cutoffFixedCoefficient cutoffLeafCoefficient basisCoefficient)
open CompactComplexActualProviderRuntimeSum (forcingCoefficient fixedCoefficient)
open CompactComplexRecursiveRuntimeSum (localConstant)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.sites CompactComplexRolePhaseSite.roleCount

/-- Fixed machine constant, independent of axes, guards, node depth and volume. -/
def machineConstant (basisConstant : ℝ) : ℝ :=
  (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
    cutoffFixedCoefficient+cutoffLeafCoefficient+
    ((fixedCoefficient : ℝ)*localConstant+6*(ComplexRank25.rankSum : ℝ)*basisConstant*(1+localConstant))*
      (arity : ℝ)^(Parameters.sigma-Parameters.tau)+1

/-- The original leaf and local contributions, with their certified exponents. -/
def stageFactor (shape : Shape) (exponent : ℕ) : ℝ :=
  ((arity^exponent : ℕ) : ℝ)^Parameters.sigma*
    ((shape.axes : ℝ)^(Parameters.beta*(1-Parameters.sigma))+
      (shape.guard : ℝ)^Parameters.tau*(shape.axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma)))

private theorem normalize_algebra (fixedRoot leaf fixedLocal basis guard localSum width sigma tau : ℝ)
    (widthPositive : 0<width) :
    (fixedRoot+leaf*width+(basis*guard+(fixedLocal+basis*guard)*localSum)*width^tau)/width^sigma=
      fixedRoot/width^sigma+leaf*width^(1-sigma)+
        (fixedLocal*localSum+basis*(1+localSum)*guard)*width^(tau-sigma) := by
  rw [Real.rpow_sub widthPositive,Real.rpow_sub widthPositive,Real.rpow_one]
  have powerNonzero := (Real.rpow_pos_of_pos widthPositive sigma).ne'
  field_simp
  ring

private theorem normalized_factor_bound
    (fixedRoot leaf fixedLocal localBasis guard arityScale widthScale leafPower localPower axisLeaf axisLocal : ℝ)
    (fixedRootNonnegative : 0≤fixedRoot) (leafNonnegative : 0≤leaf)
    (fixedLocalNonnegative : 0≤fixedLocal) (localBasisNonnegative : 0≤localBasis)
    (arityScaleNonnegative : 0≤arityScale) (localPowerNonnegative : 0≤localPower)
    (axisLocalNonnegative : 0≤axisLocal) (guardAtLeastOne : 1≤guard)
    (widthScaleAtLeastOne : 1≤widthScale) (axisLeafAtLeastOne : 1≤axisLeaf)
    (leafPowerBound : leafPower≤axisLeaf) (localPowerBound : localPower≤arityScale*axisLocal) :
    fixedRoot/widthScale+leaf*leafPower+(fixedLocal+localBasis*guard)*localPower≤
      (fixedRoot+leaf+(fixedLocal+localBasis)*arityScale+1)*(axisLeaf+guard*axisLocal) := by
  have guardNonnegative : 0≤guard := le_trans (by norm_num) guardAtLeastOne
  have axisLeafNonnegative : 0≤axisLeaf := le_trans (by norm_num) axisLeafAtLeastOne
  have fixedRootBound : fixedRoot/widthScale≤fixedRoot*axisLeaf :=
    (div_le_self fixedRootNonnegative widthScaleAtLeastOne).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left axisLeafAtLeastOne fixedRootNonnegative)
  have fixedLocalBound : fixedLocal+localBasis*guard≤(fixedLocal+localBasis)*guard := by
    have fixedBound := mul_le_mul_of_nonneg_left guardAtLeastOne fixedLocalNonnegative
    nlinarith only [fixedBound]
  have localBound := mul_le_mul fixedLocalBound localPowerBound localPowerNonnegative
    (mul_nonneg (add_nonneg fixedLocalNonnegative localBasisNonnegative) guardNonnegative)
  have firstBound := add_le_add (add_le_add fixedRootBound
    (mul_le_mul_of_nonneg_left leafPowerBound leafNonnegative)) localBound
  have localCoefficientNonnegative := mul_nonneg (add_nonneg fixedLocalNonnegative localBasisNonnegative) arityScaleNonnegative
  have fixedCoefficientNonnegative := add_nonneg fixedRootNonnegative leafNonnegative
  have firstCoefficientBound : fixedRoot+leaf≤fixedRoot+leaf+(fixedLocal+localBasis)*arityScale+1 := by
    linarith only [localCoefficientNonnegative]
  have secondCoefficientBound : (fixedLocal+localBasis)*arityScale≤
      fixedRoot+leaf+(fixedLocal+localBasis)*arityScale+1 := by
    linarith only [fixedCoefficientNonnegative]
  have secondBound := add_le_add
    (mul_le_mul_of_nonneg_right firstCoefficientBound axisLeafNonnegative)
    (mul_le_mul_of_nonneg_right secondCoefficientBound (mul_nonneg guardNonnegative axisLocalNonnegative))
  have intermediate : fixedRoot/widthScale+leaf*leafPower+(fixedLocal+localBasis*guard)*localPower≤
      (fixedRoot+leaf)*axisLeaf+((fixedLocal+localBasis)*arityScale)*(guard*axisLocal) :=
    firstBound.trans_eq (by ring)
  exact intermediate.trans (secondBound.trans_eq (by ring))

/-- The cutoff coefficient is bounded by the original axis and guard powers
with one fixed machine constant before all geometry and recursion exponents. -/
theorem normalized_cutoff_bound (basisConstant : ℝ) (constantNonnegative : 0≤basisConstant)
    (shape : Shape) (axesPositive : 0<shape.axes) (guardPositive : 1≤shape.guard) (leafExponent : ℕ)
    (cutoffStopped : ComplexRecursiveCallSchema.stopped shape.axes leafExponent=true)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped shape.axes (leafExponent+1)=false) :
    cutoffCoefficient shape basisConstant leafExponent/((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma≤
      machineConstant basisConstant*
        ((shape.axes : ℝ)^(Parameters.beta*(1-Parameters.sigma))+
          (shape.guard : ℝ)^Parameters.tau*(shape.axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma))) := by
  have widthPositive : 0<((arity^leafExponent : ℕ) : ℝ) :=
    by exact_mod_cast (pow_pos (by decide : 0<arity) leafExponent)
  have normalized := normalize_algebra
    ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+(cutoffFixedCoefficient : ℝ))
    (cutoffLeafCoefficient : ℝ) (fixedCoefficient : ℝ) (6*(ComplexRank25.rankSum : ℝ)*basisConstant)
    ((shape.guard : ℝ)^Parameters.tau) localConstant (arity^leafExponent : ℕ)
    Parameters.sigma Parameters.tau widthPositive
  have basisNonnegative : 0≤6*(ComplexRank25.rankSum : ℝ)*basisConstant :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) constantNonnegative
  have sumNonnegative : 0≤localConstant := CompactComplexRecursiveRuntimeSum.localConstant_positive.le
  have sigmaNonnegative := le_trans CompactComplexRecursiveRuntimeSum.exponents.1.le
    CompactComplexRecursiveRuntimeSum.exponents.2.1
  have leafExponentNonnegative : 0≤Parameters.beta*(1-Parameters.sigma) :=
    mul_nonneg (by norm_num [Parameters.beta]) (sub_nonneg.mpr CompactComplexRecursiveRuntimeSum.exponents.2.2.le)
  have bound := normalized_factor_bound
    ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+(cutoffFixedCoefficient : ℝ))
    (cutoffLeafCoefficient : ℝ) ((fixedCoefficient : ℝ)*localConstant)
    (6*(ComplexRank25.rankSum : ℝ)*basisConstant*(1+localConstant)) ((shape.guard : ℝ)^Parameters.tau)
    ((arity : ℝ)^(Parameters.sigma-Parameters.tau)) (((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma)
    (((arity^leafExponent : ℕ) : ℝ)^(1-Parameters.sigma))
    (((arity^leafExponent : ℕ) : ℝ)^(Parameters.tau-Parameters.sigma))
    ((shape.axes : ℝ)^(Parameters.beta*(1-Parameters.sigma)))
    ((shape.axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma)))
    (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) sumNonnegative)
    (mul_nonneg basisNonnegative (add_nonneg (by norm_num) sumNonnegative))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.one_le_rpow (by exact_mod_cast guardPositive) CompactComplexRecursiveRuntimeSum.exponents.1.le)
    (Real.one_le_rpow (by exact_mod_cast (Nat.one_le_pow leafExponent arity (by decide))) sigmaNonnegative)
    (Real.one_le_rpow (by exact_mod_cast axesPositive) leafExponentNonnegative)
    (CompactComplexCutoffPowers.leaf_power_bound shape.axes leafExponent axesPositive cutoffStopped aboveCutoff)
    (CompactComplexCutoffPowers.local_power_bound shape.axes leafExponent axesPositive cutoffStopped aboveCutoff)
  exact normalized.trans_le bound

theorem machine_constant_positive (basisConstant : ℝ) (constantNonnegative : 0≤basisConstant) :
    0<machineConstant basisConstant := by
  have sumNonnegative : 0≤localConstant := CompactComplexRecursiveRuntimeSum.localConstant_positive.le
  have basisNonnegative : 0≤6*(ComplexRank25.rankSum : ℝ)*basisConstant :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) constantNonnegative
  exact add_pos_of_nonneg_of_pos
    (add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (mul_nonneg
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) sumNonnegative)
          (mul_nonneg basisNonnegative (add_nonneg (by norm_num) sumNonnegative)))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (by norm_num)

private theorem stage_algebra (machine leaf guard localPower nativeVolume widthPower : ℝ) :
    (machine*(leaf+guard*localPower)*nativeVolume)*widthPower=
      machine*nativeVolume*(widthPower*(leaf+guard*localPower)) := by
  ring

/-- The actual root runtime coefficient satisfies the original uniform stage
bound. Its one positive machine constant precedes every shape, volume and
node exponent, and the original classifier supplies its cutoff internally. -/
theorem root_runtime_coefficient_bound (basisConstant : ℝ) (constantNonnegative : 0≤basisConstant)
    (shape : Shape) (axesPositive : 0<shape.axes) (guardPositive : 1≤shape.guard)
    (childExponent nativeVolume : ℕ)
    (rootNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+2)=false) :
    ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
      CompactComplexActualProviderRuntime.localCoefficient shape basisConstant childExponent+
      if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
        (ComplexRank25.rankSum : ℝ)/roles*CompactComplexActualProviderRuntime.pathCoefficient shape basisConstant childExponent)*
        (nativeVolume : ℝ)≤
      machineConstant basisConstant*(nativeVolume : ℝ)*stageFactor shape (childExponent+1) := by
  obtain ⟨leafExponent,depth,nodeExponent,cutoffStopped,aboveCutoff,originalBound⟩ :=
    CompactComplexActualCutoffBudget.root_original_width_bound shape basisConstant constantNonnegative
      childExponent nativeVolume rootNonstopped
  have coefficientBound := normalized_cutoff_bound basisConstant constantNonnegative shape axesPositive
    guardPositive leafExponent cutoffStopped aboveCutoff
  have volumeBound := mul_le_mul_of_nonneg_right coefficientBound (Nat.cast_nonneg nativeVolume)
  have widthBound := mul_le_mul_of_nonneg_right volumeBound
    (Real.rpow_nonneg (Nat.cast_nonneg (arity^(childExponent+1))) Parameters.sigma)
  exact originalBound.trans (widthBound.trans_eq (stage_algebra (machineConstant basisConstant)
    ((shape.axes : ℝ)^(Parameters.beta*(1-Parameters.sigma))) ((shape.guard : ℝ)^Parameters.tau)
    ((shape.axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma))) (nativeVolume : ℝ)
    (((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.sigma)))

end
end IntegerMultBounds.Machine.CompactComplexUniformRuntimeCoefficient
