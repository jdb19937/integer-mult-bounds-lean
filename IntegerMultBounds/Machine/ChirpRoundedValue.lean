module

public import IntegerMultBounds.Machine.ChirpExactProduct
public import IntegerMultBounds.Resampling.WindowSum

/-! Exact numerical meaning of rounding after full complex numerator sums.
These identities connect the tape truncation's signed integer quotients to
the manuscript's componentwise Gaussian-dyadic rounding operation. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpRoundedValue
noncomputable section
open ButterflySigned (complexValue)

theorem components (real imaginary : ℤ) (precision : ℕ) :
    complexValue real imaginary precision=
      (⟨(real : ℝ)/2^precision,(imaginary : ℝ)/2^precision⟩ : ℂ) := by
  have denominator : (2 : ℂ)^precision=((2 : ℝ)^precision : ℂ) := by norm_cast
  unfold complexValue
  rw [denominator, ← Complex.ofReal_pow, Complex.div_ofReal]
  simp

theorem numerator_mul (leftReal leftImaginary rightReal rightImaginary : ℤ) (precision : ℕ) :
    complexValue (leftReal*rightReal-leftImaginary*rightImaginary)
      (leftReal*rightImaginary+leftImaginary*rightReal) (2*precision)=
      complexValue leftReal leftImaginary precision*complexValue rightReal rightImaginary precision := by
  unfold complexValue
  push_cast
  rw [pow_mul']
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem round_scaled (real imaginary : ℤ) (precision : ℕ) :
    complexValue (real.tdiv (2^precision)) (imaginary.tdiv (2^precision)) precision=
      NLogN.rhoC precision (complexValue real imaginary (2*precision)) := by
  have scaled (numerator : ℤ) : (2 : ℝ)^precision*((numerator : ℝ)/2^(2*precision))=(numerator : ℝ)/2^precision := by
    rw [pow_mul']
    field_simp
  rw [components,components]
  apply Complex.ext <;> simp only [NLogN.rhoC,scaled,Resampling.WindowSum.rho0_div_pow]

theorem rounded_mul (leftReal leftImaginary rightReal rightImaginary : ℤ) (precision : ℕ) :
    complexValue ((leftReal*rightReal-leftImaginary*rightImaginary).tdiv (2^precision))
      ((leftReal*rightImaginary+leftImaginary*rightReal).tdiv (2^precision)) precision=
      NLogN.rhoC precision (complexValue leftReal leftImaginary precision*complexValue rightReal rightImaginary precision) := by
  rw [←numerator_mul]
  exact round_scaled _ _ _

end
end IntegerMultBounds.Machine.ChirpRoundedValue
