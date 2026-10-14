module

public import IntegerMultBounds.Machine.RecoverOutput
public import IntegerMultBounds.ExactRecovery

/-! Numerical-to-native recovery bridge. Exact coefficient labels are derived
from the input digits, rather than supplied by a caller. A representation
readout equation connects the physical signed words to a computed convolution;
pointwise approximation then supplies every half-unit margin. This does not
construct or execute the upstream transform-record format adapter. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverNumericalBridge
noncomputable section
open NLogN

/-- The exact labels are mathematical convolution coefficients, never data
read by the recovery program. -/
def records {size : ℕ} [NeZero size] (chunkWidth : ℕ) (leftInput rightInput : List Bool)
    (coefficientWords : Fin size → List Bool) : List RecoverArray.Coefficient :=
  List.ofFn fun index => ⟨coefficientWords index,
    (cconvList size (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput)).getD index.val 0⟩

theorem records_good {size : ℕ} [NeZero size]
    (chunkWidth precision wordWidth : ℕ) (leftInput rightInput : List Bool)
    (coefficientWords : Fin size → List Bool) (approximation : ZMod size → ℂ) (error : ℝ)
    (wordLengths : ∀ index, (coefficientWords index).length = wordWidth)
    (readout : ∀ index, (TwosComplement.signed (coefficientWords index) : ℝ) / 2 ^ precision =
      (((2 : ℂ) ^ (2 * chunkWidth) * size) * approximation (index.val : ZMod size)).re)
    (approximationBound : ∀ index, ‖approximation index -
      scaledConv size chunkWidth (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput) index‖ ≤ error)
    (recoveryMargin : (2 : ℝ) ^ (2 * chunkWidth) * size * error < 1 / 2) :
    ∀ record ∈ records chunkWidth leftInput rightInput coefficientWords,
      RecoverArray.Good wordWidth precision record := by
  intro record member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  refine ⟨wordLengths index, ?_⟩
  change |(TwosComplement.signed (coefficientWords index) : ℝ) / 2 ^ precision -
    ((cconvList size (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput)).getD index.val 0 : ℝ)| < 1 / 2
  rw [readout]
  have coefficientError := recover_coefficient_real_error
    (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput)
    approximationBound recoveryMargin (index.val : ZMod size)
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt index.isLt] using coefficientError

theorem records_product {size : ℕ} [NeZero size]
    (chunkWidth : ℕ) (leftInput rightInput : List Bool) (coefficientWords : Fin size → List Bool)
    (chunkPositive : 0 < chunkWidth)
    (convolutionFits : (digitsOf chunkWidth leftInput).length +
      (digitsOf chunkWidth rightInput).length ≤ size + 1) :
    evalBase (2 ^ chunkWidth)
      ((records chunkWidth leftInput rightInput coefficientWords).map RecoverArray.Coefficient.exact) =
        binaryValue leftInput * binaryValue rightInput := by
  have labels : (records chunkWidth leftInput rightInput coefficientWords).map RecoverArray.Coefficient.exact =
      cconvList size (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput) := by
    apply List.ext_getElem
    · simp [records]
    · intro index leftBound rightBound
      have indexBound : index < size := by simpa using rightBound
      simp only [records, List.getElem_map, List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ rightBound
  rw [labels]
  exact reduce_to_cconv chunkPositive convolutionFits

/-- Actual transform contraction and approximation guarantees supply the
native array's margins. Only the physical word readout remains to be established
by the upstream format/scaling procedure. Transform and recovery precisions may
differ, since rescaling changes the dyadic denominator. -/
theorem records_good_computed {size transformPrecision : ℕ} [NeZero size]
    {coordinates : Type*} [Fintype coordinates] {scaledError : ℝ}
    (chunkWidth precision wordWidth : ℕ) (leftInput rightInput : List Bool)
    (coefficientWords : Fin size → List Bool)
    (forward : (ZMod size → ℂ) →L[ℂ] (coordinates → ℂ))
    (computedForward : (ZMod size → ℂ) → (coordinates → ℂ))
    (backward : (coordinates → ℂ) →L[ℂ] (ZMod size → ℂ))
    (computedBackward : (coordinates → ℂ) → (ZMod size → ℂ))
    (chunkPositive : 0 < chunkWidth)
    (wordLengths : ∀ index, (coefficientWords index).length = wordWidth)
    (readout : ∀ index, (TwosComplement.signed (coefficientWords index) : ℝ) / 2 ^ precision =
      (((2 : ℂ) ^ (2 * chunkWidth) * size) * ExactRecovery.computedConv
        (p := transformPrecision) (k := chunkWidth) computedForward computedBackward leftInput rightInput
        (index.val : ZMod size)).re)
    (forwardContractive : ‖forward‖ ≤ 1)
    (forwardError : ∀ input : ZMod size → ℂ, ‖input‖ ≤ 1 / 2 →
      2 ^ transformPrecision * ‖computedForward input - forward input‖ ≤ scaledError)
    (backwardContractive : ‖backward‖ ≤ 1)
    (backwardError : ∀ input : coordinates → ℂ, ‖input‖ ≤ 1 / 2 →
      2 ^ transformPrecision * ‖computedBackward input - backward input‖ ≤ scaledError)
    (errorSmall : scaledError ≤ 2 ^ transformPrecision / 100)
    (convolutionIdentity : ∀ left right : ZMod size → ℂ,
      backward (fun coordinate => forward left coordinate * forward right coordinate) =
        fun index => cconv left right index / (size : ℂ) ^ 2)
    (finalMargin : (2 : ℝ) ^ (2 * chunkWidth + 4) * size ^ 2 * (3 * scaledError + 2) <
      2 ^ transformPrecision / 2) :
    ∀ record ∈ records chunkWidth leftInput rightInput coefficientWords,
      RecoverArray.Good wordWidth precision record := by
  intro record member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  refine ⟨wordLengths index, ?_⟩
  change |(TwosComplement.signed (coefficientWords index) : ℝ) / 2 ^ precision -
    ((cconvList size (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput)).getD index.val 0 : ℝ)| < 1 / 2
  rw [readout]
  have coefficientError := ExactRecovery.computedConv_coefficient_real_error (x := leftInput) (y := rightInput)
    forward computedForward backward computedBackward chunkPositive forwardContractive forwardError
    backwardContractive backwardError errorSmall convolutionIdentity finalMargin (index.val : ZMod size)
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt index.isLt] using coefficientError

/-- A genuine halted recovery execution from encoded approximate convolution
words. Coefficient half-unit margins and the product identity are conclusions
of the numerical bridge, rather than independent caller hypotheses. -/
theorem runs_correct {alphabet size : ℕ} [NeZero size]
    (chunkWidth precision wordWidth inputLength : ℕ) (leftInput rightInput : List Bool)
    (coefficientWords : Fin size → List Bool) (approximation : ZMod size → ℂ) (error : ℝ)
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (convolutionFits : (digitsOf chunkWidth leftInput).length +
      (digitsOf chunkWidth rightInput).length ≤ size + 1)
    (wordLengths : ∀ index, (coefficientWords index).length = wordWidth)
    (readout : ∀ index, (TwosComplement.signed (coefficientWords index) : ℝ) / 2 ^ precision =
      (((2 : ℂ) ^ (2 * chunkWidth) * size) * approximation (index.val : ZMod size)).re)
    (approximationBound : ∀ index, ‖approximation index -
      scaledConv size chunkWidth (digitsOf chunkWidth leftInput) (digitsOf chunkWidth rightInput) index‖ ≤ error)
    (recoveryMargin : (2 : ℝ) ^ (2 * chunkWidth) * size * error < 1 / 2) :
    ∃ elapsed finalConfig,
      elapsed ≤ 160 * (Schoenhage.clen ((records chunkWidth leftInput rightInput coefficientWords).map
        RecoverArray.Coefficient.bits) + wordWidth + inputLength + 1) ∧
      run (RecoverOutput.program (alphabet := alphabet)) elapsed
        ((RecoverOutput.input (records chunkWidth leftInput rightInput coefficientWords)
          chunkWidth precision leftInput).start RecoverOutput.program) = some finalConfig ∧
      step RecoverOutput.program finalConfig = none ∧
      outputCorrect RecoverOutput.program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 12, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧
        finalConfig.tapes.head slot = 0) := by
  exact RecoverOutput.runs_correct _ chunkWidth precision wordWidth inputLength leftInput rightInput
    leftLength rightLength precisionPositive precisionFits chunkPositive chunkFits
    (records_good chunkWidth precision wordWidth leftInput rightInput coefficientWords approximation error
      wordLengths readout approximationBound recoveryMargin)
    (records_product chunkWidth leftInput rightInput coefficientWords chunkPositive convolutionFits)

end
end IntegerMultBounds.Machine.RecoverNumericalBridge
