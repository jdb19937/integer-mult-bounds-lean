module

public import IntegerMultBounds.Machine.RecoverNumericalBridge
public import IntegerMultBounds.Spec.SignedRingProductFacts

/-! Public MSB-first component words and native LSB-first signed recovery.
For power-of-two convolution lengths, the final numerator scaling can be
absorbed into the fractional precision: no arithmetic pass over the numerator
is needed. The physical real-field selection and reversal are separate tape
obligations; these lemmas certify their required representation and scaling. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverRecordFormat
noncomputable section
open Spec.SignedRingProduct NLogN

/-- Reversing a public signed component changes bit order without changing its
signed value, including the empty-word convention. -/
theorem signed_reverse (component : List Bool) :
    TwosComplement.signed component.reverse = compValue component := by
  rw [TwosComplement.signed, ElementaryMultiplyCore.value_reverse, List.length_reverse]
  cases component with
  | nil => rfl
  | cons sign payload => simp [compValue, List.getLastD_eq_getLast?]

theorem signed_compWord_reverse (wordWidth : ℕ) (numerator : ℤ)
    (widthPositive : 1 ≤ wordWidth)
    (lowerBound : -(2 : ℤ) ^ (wordWidth - 1) ≤ numerator)
    (upperBound : numerator < (2 : ℤ) ^ (wordWidth - 1)) :
    TwosComplement.signed (compWord wordWidth numerator).reverse = numerator := by
  rw [signed_reverse]
  exact compValue_compWord widthPositive lowerBound upperBound

/-- Public signed real components become native recovery words after bit
reversal. This lemma also covers negative approximations of a zero target. -/
theorem good_component (wordWidth precision coefficient : ℕ) (numerator : ℤ)
    (widthPositive : 1 ≤ wordWidth)
    (lowerBound : -(2 : ℤ) ^ (wordWidth - 1) ≤ numerator)
    (upperBound : numerator < (2 : ℤ) ^ (wordWidth - 1))
    (coefficientMargin : |(numerator : ℝ) / 2 ^ precision - coefficient| < 1 / 2) :
    RecoverArray.Good wordWidth precision
      ⟨(compWord wordWidth numerator).reverse, coefficient⟩ := by
  refine ⟨by simp, ?_⟩
  change |(TwosComplement.signed (compWord wordWidth numerator).reverse : ℝ) /
    2 ^ precision - coefficient| < 1 / 2
  rw [signed_compWord_reverse wordWidth numerator widthPositive lowerBound upperBound]
  exact coefficientMargin

/-- Multiplication by an exact power of two is a change of dyadic denominator
when the original precision has enough fractional bits. -/
theorem dyadic_rescale (numerator : ℤ) (precision shift : ℕ) (shiftFits : shift ≤ precision) :
    (2 : ℝ) ^ shift * ((numerator : ℝ) / 2 ^ precision) =
      (numerator : ℝ) / 2 ^ (precision - shift) := by
  have precisionSplit : precision = shift + (precision - shift) := by omega
  conv_lhs => rw [precisionSplit, pow_add]
  have scaleNonzero : (2 : ℝ) ^ shift ≠ 0 := by positivity
  have denominatorNonzero : (2 : ℝ) ^ (precision - shift) ≠ 0 := by positivity
  field_simp

/-- The complete section 8 scaling is `2^(2k+4+2ℓ)` for size `2^ℓ`.
Consequently the same stored real numerator is suitable for recovery at the
smaller precision, after only reversing its public MSB-first component. -/
theorem computed_readout {coordinates : Type*} [Fintype coordinates]
    (chunkWidth lengthExponent transformPrecision wordWidth : ℕ)
    (leftInput rightInput : List Bool) (realNumerators : Fin (2 ^ lengthExponent) → ℤ)
    (computedForward : (ZMod (2 ^ lengthExponent) → ℂ) → (coordinates → ℂ))
    (computedBackward : (coordinates → ℂ) → (ZMod (2 ^ lengthExponent) → ℂ))
    (shiftFits : 2 * chunkWidth + 4 + 2 * lengthExponent ≤ transformPrecision)
    (widthPositive : 1 ≤ wordWidth)
    (lowerBounds : ∀ index, -(2 : ℤ) ^ (wordWidth - 1) ≤ realNumerators index)
    (upperBounds : ∀ index, realNumerators index < (2 : ℤ) ^ (wordWidth - 1))
    (transformReadout : ∀ index,
      (ExactRecovery.computed (p := transformPrecision) computedForward computedBackward
        (ExactRecovery.scaledDigits (2 ^ lengthExponent) chunkWidth (digitsOf chunkWidth leftInput))
        (ExactRecovery.scaledDigits (2 ^ lengthExponent) chunkWidth (digitsOf chunkWidth rightInput))
        (index.val : ZMod (2 ^ lengthExponent))).re =
          (realNumerators index : ℝ) / 2 ^ transformPrecision) :
    ∀ index,
      (TwosComplement.signed (compWord wordWidth (realNumerators index)).reverse : ℝ) /
        2 ^ (transformPrecision - (2 * chunkWidth + 4 + 2 * lengthExponent)) =
      (((2 : ℂ) ^ (2 * chunkWidth) * (2 ^ lengthExponent : ℕ)) *
        ExactRecovery.computedConv (p := transformPrecision) (k := chunkWidth)
          computedForward computedBackward leftInput rightInput
          (index.val : ZMod (2 ^ lengthExponent))).re := by
  intro index
  rw [signed_compWord_reverse wordWidth (realNumerators index) widthPositive
    (lowerBounds index) (upperBounds index)]
  unfold ExactRecovery.computedConv
  simp only [Pi.smul_apply, smul_eq_mul]
  have scaleReal : ((2 : ℂ) ^ (2 * chunkWidth) * (2 ^ lengthExponent : ℕ)) *
      (16 * (2 ^ lengthExponent : ℕ)) =
        Complex.ofReal ((2 : ℝ) ^ (2 * chunkWidth + 4 + 2 * lengthExponent)) := by
    push_cast
    simp only [two_mul, pow_add]
    norm_num
    ring
  rw [← mul_assoc, scaleReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [transformReadout]
  exact (dyadic_rescale (realNumerators index) transformPrecision _ shiftFits).symm

/-- A positive residual fractional precision and a public word at least as
wide as the original precision automatically fit the native recovery rulers. -/
theorem precision_controls (chunkWidth lengthExponent transformPrecision wordWidth : ℕ)
    (shiftStrict : 2 * chunkWidth + 4 + 2 * lengthExponent < transformPrecision)
    (wordFits : transformPrecision ≤ wordWidth) :
    0 < transformPrecision - (2 * chunkWidth + 4 + 2 * lengthExponent) ∧
      transformPrecision - (2 * chunkWidth + 4 + 2 * lengthExponent) ≤ wordWidth ∧
      chunkWidth ≤ wordWidth - (transformPrecision - (2 * chunkWidth + 4 + 2 * lengthExponent)) := by
  omega

/-- The manuscript precision `6k` leaves enough fractional and integer bits
for native recovery once `k ≥ 3` and the convolution exponent is at most `k`. -/
theorem precision_controls_six (chunkWidth lengthExponent wordWidth : ℕ)
    (chunkLarge : 3 ≤ chunkWidth) (lengthFits : lengthExponent ≤ chunkWidth)
    (wordFits : 6 * chunkWidth ≤ wordWidth) :
    0 < 6 * chunkWidth - (2 * chunkWidth + 4 + 2 * lengthExponent) ∧
      6 * chunkWidth - (2 * chunkWidth + 4 + 2 * lengthExponent) ≤ wordWidth ∧
      chunkWidth ≤ wordWidth - (6 * chunkWidth - (2 * chunkWidth + 4 + 2 * lengthExponent)) := by
  exact precision_controls chunkWidth lengthExponent (6 * chunkWidth) wordWidth (by omega) wordFits

/-- Public transform numerators yield a correct native recovery array. The
actual transform readout and signed range bounds replace any independently
assumed coefficient correctness or scaled native readout. -/
theorem records_good_public_computed {coordinates : Type*} [Fintype coordinates] {scaledError : ℝ}
    (chunkWidth lengthExponent transformPrecision wordWidth : ℕ)
    (leftInput rightInput : List Bool) (realNumerators : Fin (2 ^ lengthExponent) → ℤ)
    (forward : (ZMod (2 ^ lengthExponent) → ℂ) →L[ℂ] (coordinates → ℂ))
    (computedForward : (ZMod (2 ^ lengthExponent) → ℂ) → (coordinates → ℂ))
    (backward : (coordinates → ℂ) →L[ℂ] (ZMod (2 ^ lengthExponent) → ℂ))
    (computedBackward : (coordinates → ℂ) → (ZMod (2 ^ lengthExponent) → ℂ))
    (chunkPositive : 0 < chunkWidth)
    (shiftFits : 2 * chunkWidth + 4 + 2 * lengthExponent ≤ transformPrecision)
    (widthPositive : 1 ≤ wordWidth)
    (lowerBounds : ∀ index, -(2 : ℤ) ^ (wordWidth - 1) ≤ realNumerators index)
    (upperBounds : ∀ index, realNumerators index < (2 : ℤ) ^ (wordWidth - 1))
    (transformReadout : ∀ index,
      (ExactRecovery.computed (p := transformPrecision) computedForward computedBackward
        (ExactRecovery.scaledDigits (2 ^ lengthExponent) chunkWidth (digitsOf chunkWidth leftInput))
        (ExactRecovery.scaledDigits (2 ^ lengthExponent) chunkWidth (digitsOf chunkWidth rightInput))
        (index.val : ZMod (2 ^ lengthExponent))).re =
          (realNumerators index : ℝ) / 2 ^ transformPrecision)
    (forwardContractive : ‖forward‖ ≤ 1)
    (forwardError : ∀ input : ZMod (2 ^ lengthExponent) → ℂ, ‖input‖ ≤ 1 / 2 →
      2 ^ transformPrecision * ‖computedForward input - forward input‖ ≤ scaledError)
    (backwardContractive : ‖backward‖ ≤ 1)
    (backwardError : ∀ input : coordinates → ℂ, ‖input‖ ≤ 1 / 2 →
      2 ^ transformPrecision * ‖computedBackward input - backward input‖ ≤ scaledError)
    (errorSmall : scaledError ≤ 2 ^ transformPrecision / 100)
    (convolutionIdentity : ∀ left right : ZMod (2 ^ lengthExponent) → ℂ,
      backward (fun coordinate => forward left coordinate * forward right coordinate) =
        fun index => cconv left right index / ((2 ^ lengthExponent : ℕ) : ℂ) ^ 2)
    (finalMargin : (2 : ℝ) ^ (2 * chunkWidth + 4) * (2 ^ lengthExponent : ℕ) ^ 2 *
      (3 * scaledError + 2) < 2 ^ transformPrecision / 2) :
    ∀ record ∈ RecoverNumericalBridge.records chunkWidth leftInput rightInput
        (fun index => (compWord wordWidth (realNumerators index)).reverse),
      RecoverArray.Good wordWidth
        (transformPrecision - (2 * chunkWidth + 4 + 2 * lengthExponent)) record := by
  exact RecoverNumericalBridge.records_good_computed chunkWidth
    (transformPrecision - (2 * chunkWidth + 4 + 2 * lengthExponent)) wordWidth leftInput rightInput
    (fun index => (compWord wordWidth (realNumerators index)).reverse)
    forward computedForward backward computedBackward chunkPositive (by intro index; simp)
    (computed_readout chunkWidth lengthExponent transformPrecision wordWidth leftInput rightInput realNumerators
      computedForward computedBackward shiftFits widthPositive lowerBounds upperBounds transformReadout)
    forwardContractive forwardError backwardContractive backwardError errorSmall convolutionIdentity finalMargin

end
end IntegerMultBounds.Machine.RecoverRecordFormat
