module

public import IntegerMultBounds.Machine.CompactComplexUniformRuntimeCoefficient
public import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedRootBudget

/-! The actual stopped-root allowance has the same original uniform stage
factor, including exponent zero. Its coefficient is fixed before all inputs,
geometry, recursion exponents and banks. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexUniformStoppedRootBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexUniformRuntimeCoefficient (stageFactor)
attribute [local irreducible] CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
  CompactComplexSourceReadyGuard.guardConstant

def constant : ℝ := CompactComplexCorrectedStoppedRootBudget.constant

private theorem coefficient_positive_algebra (leaf guard : ℕ) : 0<leaf+3*guard+12 := by
  omega

theorem constant_positive : 0<constant := by
  have nativePositive : 0<CompactComplexCorrectedStoppedRootBudget.constant :=
    coefficient_positive_algebra CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
      CompactComplexSourceReadyGuard.guardConstant
  change (0 : ℝ)<(CompactComplexCorrectedStoppedRootBudget.constant : ℝ)
  exact_mod_cast nativePositive

/-- Every actual stopped width is at most the original axis-to-beta threshold,
including the exponent-zero scalar branch. No next-level cutoff is assumed. -/
theorem stopped_width_bound (axes exponent : ℕ) (axesPositive : 0<axes)
    (rootStopped : ComplexRecursiveCallSchema.stopped axes exponent=true) :
    (arity^exponent : ℕ)≤(axes : ℝ)^Parameters.beta := by
  have betaNonnegative : 0≤Parameters.beta := by norm_num [Parameters.beta]
  rcases (ComplexRecursiveCallSchema.stopped_iff axes exponent).1 rootStopped with
    exponentZero | stoppedWidth
  · rw [exponentZero,pow_zero,Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast axesPositive) betaNonnegative
  · have bound := Real.rpow_le_rpow
      (Nat.cast_nonneg ((arity^exponent)^1000) : (0 : ℝ)≤((arity^exponent)^1000 : ℕ))
      (Nat.cast_le (α:=ℝ).mpr stoppedWidth.le) betaNonnegative
    rw [Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg _)] at bound
    norm_num only [Parameters.beta,show (1000 : ℝ)*(1/1000)=1 by norm_num,Real.rpow_one] at bound
    exact bound

/-- The actual stopped leaf width is absorbed by the same original leaf/local
stage factor as the nonstopped recurrence, without enlarging any exponent. -/
theorem leaf_width_le_stage (shape : Shape) (axesPositive : 0<shape.axes) (exponent : ℕ)
    (rootStopped : ComplexRecursiveCallSchema.stopped shape.axes exponent=true) :
    (arity^exponent : ℕ)≤stageFactor shape exponent := by
  have widthBound := stopped_width_bound shape.axes exponent axesPositive rootStopped
  have widthPositive : 0<((arity^exponent : ℕ) : ℝ) :=
    by exact_mod_cast (pow_pos (by decide : 0<arity) exponent)
  have leafPowerBound := Real.rpow_le_rpow (Nat.cast_nonneg _) widthBound
    (sub_nonneg.mpr CompactComplexRecursiveRuntimeSum.exponents.2.2.le)
  rw [←Real.rpow_mul (Nat.cast_nonneg shape.axes)] at leafPowerBound
  have widthEquation : ((arity^exponent : ℕ) : ℝ)=
      ((arity^exponent : ℕ) : ℝ)^Parameters.sigma*((arity^exponent : ℕ) : ℝ)^(1-Parameters.sigma) := by
    rw [←Real.rpow_add widthPositive]
    simp only [add_sub_cancel,Real.rpow_one]
  have leafBound := mul_le_mul_of_nonneg_left leafPowerBound
    (Real.rpow_nonneg (Nat.cast_nonneg (arity^exponent)) Parameters.sigma)
  have extraNonnegative := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg shape.guard) Parameters.tau)
    (Real.rpow_nonneg (Nat.cast_nonneg shape.axes) (Parameters.beta*(Parameters.tau-Parameters.sigma)))
  have stageBound : ((arity^exponent : ℕ) : ℝ)^Parameters.sigma*
      (shape.axes : ℝ)^(Parameters.beta*(1-Parameters.sigma))≤stageFactor shape exponent :=
    mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right extraNonnegative)
    (Real.rpow_nonneg (Nat.cast_nonneg (arity^exponent)) Parameters.sigma)
  exact widthEquation.le.trans (leafBound.trans stageBound)

/-- The complete physical classifier, leaf, joins and empty-root halt have the
original uniform stage-factor bound from their genuine dependency geometry. -/
theorem cost_uniform {shape : Shape} {left exponent levels frames returned : ℕ}
    (rows ell precision : ℕ) (phaseCoordinate : Fin shape.chunk)
    (dependency : Path shape.active left exponent levels frames returned)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (rootStopped : ComplexRecursiveCallSchema.stopped shape.axes exponent=true) :
    (CompactComplexCorrectedStoppedRootBudget.cost shape rows ell precision exponent : ℝ)≤
      constant*(volume rows shape ell precision : ℝ)*stageFactor shape exponent := by
  have nativeBound := CompactComplexCorrectedStoppedRootBudget.cost_from_path rows ell precision
    phaseCoordinate dependency rowsPositive guardPositive
  have realBound := Nat.cast_le (α:=ℝ).mpr nativeBound
  rw [Nat.cast_mul,Nat.cast_mul] at realBound
  exact realBound.trans (mul_le_mul_of_nonneg_left
    (leaf_width_le_stage shape axesPositive exponent rootStopped)
    (mul_nonneg constant_positive.le (Nat.cast_nonneg _)))

private theorem stopped_cost_algebra (setup cleanup leaf nativeVolume width : ℕ) :
    setup+cleanup+8+(leaf+4)*nativeVolume*width+3=
      ((setup+cleanup+7+1)+((leaf+4)*nativeVolume*width+1)+2) := by
  omega

/-- The actual aligned stopped-root allowance is precisely the already paid
complete root cost, including all classifier, leaf and halt transitions. -/
theorem aligned_cost_eq (shape : Shape) (rows ell precision exponent : ℕ) :
    CompactComplexSourceReadyGuard.setupCost shape.axes exponent+
      CompactComplexSourceReadyGuard.cleanupCost shape.axes exponent+8+
      (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
        volume rows shape ell precision*arity^exponent+3=
      CompactComplexCorrectedStoppedRootBudget.cost shape rows ell precision exponent :=
  stopped_cost_algebra (CompactComplexSourceReadyGuard.setupCost shape.axes exponent)
    (CompactComplexSourceReadyGuard.cleanupCost shape.axes exponent)
    CompactComplexSourceReadyStoppedLeafDispatchBudget.constant (volume rows shape ell precision) (arity^exponent)

end
end IntegerMultBounds.Machine.CompactComplexUniformStoppedRootBudget
