module

public import IntegerMultBounds.Machine.CompactComplexUniformStoppedRootBudget

/-! One positive machine coefficient covers both actual root classifier
branches, selected before every shape, exponent, input and saved history. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexUniformRootConstant
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexUniformRuntimeCoefficient (machineConstant stageFactor)
open CompactComplexActualProviderRuntime (uniformBasisConstant)

def constant (packingLimit : ℕ) : ℝ :=
  machineConstant (uniformBasisConstant packingLimit)+CompactComplexUniformStoppedRootBudget.constant

theorem constant_positive (packingLimit : ℕ) : 0<constant packingLimit :=
  add_pos (CompactComplexUniformRuntimeCoefficient.machine_constant_positive _
    (CompactComplexActualProviderRuntime.uniform_basis_constant_positive packingLimit).le)
    CompactComplexUniformStoppedRootBudget.constant_positive

theorem nonstopped_bound (packingLimit : ℕ) (shape : Shape) (exponent nativeVolume : ℕ) :
    machineConstant (uniformBasisConstant packingLimit)*(nativeVolume : ℝ)*stageFactor shape exponent≤
      constant packingLimit*(nativeVolume : ℝ)*stageFactor shape exponent := by
  have coefficientBound : machineConstant (uniformBasisConstant packingLimit)≤constant packingLimit :=
    le_add_of_nonneg_right CompactComplexUniformStoppedRootBudget.constant_positive.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficientBound (Nat.cast_nonneg nativeVolume))
    (CompactComplexUniformRuntimeCoefficient.stage_factor_nonnegative shape exponent)

theorem stopped_bound (packingLimit : ℕ) (shape : Shape) (exponent nativeVolume : ℕ) :
    CompactComplexUniformStoppedRootBudget.constant*(nativeVolume : ℝ)*stageFactor shape exponent≤
      constant packingLimit*(nativeVolume : ℝ)*stageFactor shape exponent := by
  have coefficientBound : CompactComplexUniformStoppedRootBudget.constant≤constant packingLimit :=
    le_add_of_nonneg_left (CompactComplexUniformRuntimeCoefficient.machine_constant_positive _
      (CompactComplexActualProviderRuntime.uniform_basis_constant_positive packingLimit).le).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficientBound (Nat.cast_nonneg nativeVolume))
    (CompactComplexUniformRuntimeCoefficient.stage_factor_nonnegative shape exponent)

end
end IntegerMultBounds.Machine.CompactComplexUniformRootConstant
