module

public import IntegerMultBounds.Machine.RecoverHeaderControlBudget

/-! The original public record pays the operand-width clock and recovery
controls. Chunk coverage is proved from the actual input list, including a
short final chunk; no separate source-volume premise is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverRecordBudget
open NLogN

/-- Every input cell belongs to a chunk of at most the selected width. -/
theorem chunks_cover_length (chunkPred : ℕ) (digits : List ℕ) :
    digits.length ≤ (chunkPred + 1) * (chunks (chunkPred + 1) digits).length := by
  match digits with
  | [] => simp
  | digit :: rest =>
    have remainingCovered := chunks_cover_length chunkPred (rest.drop chunkPred)
    rw [List.length_drop] at remainingCovered
    rw [chunks_cons,List.length_cons]
    simp only [List.length_cons]
    by_cases fullChunk : chunkPred ≤ rest.length
    · nlinarith [Nat.sub_add_cancel fullChunk]
    · nlinarith
termination_by digits.length
decreasing_by all_goals (simp [List.length_drop]; try omega)

/-- Exact input length is paid by digit count times chunk width, including
padding of the last chunk and leading zero bits in the original operand. -/
theorem digits_cover_length (chunkWidth : ℕ) (inputBits : List Bool) (chunkPositive : 0 < chunkWidth) :
    inputBits.length ≤ chunkWidth * (digitsOf chunkWidth inputBits).length := by
  obtain ⟨chunkPred,rfl⟩ := Nat.exists_eq_succ_of_ne_zero chunkPositive.ne'
  have covered := chunks_cover_length chunkPred (inputBits.reverse.map bitDigit)
  simpa only [digitsOf,List.length_map,List.length_reverse] using covered

/-- The physical public transform record pays the original operand clock.
This follows from convolution capacity and field width, not a tape premise. -/
theorem clock_le_public_length (chunkWidth lengthExponent wordWidth : ℕ)
    (leftInput rightInput : List Bool) (real imaginary : Fin (2 ^ lengthExponent) → ℤ)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth)
    (convolutionFits : (digitsOf chunkWidth leftInput).length +
      (digitsOf chunkWidth rightInput).length ≤ 2 ^ lengthExponent + 1) :
    leftInput.length ≤ (Spec.SignedRingProduct.record wordWidth real imaginary).length := by
  have covered := digits_cover_length chunkWidth leftInput chunkPositive
  have countPositive := Nat.two_pow_pos lengthExponent
  have countBound : (digitsOf chunkWidth leftInput).length ≤ 2 * 2 ^ lengthExponent := by omega
  have digitVolume := Nat.mul_le_mul_left chunkWidth countBound
  have fieldVolume := Nat.mul_le_mul_right (2 * 2 ^ lengthExponent) chunkFits
  rw [Spec.SignedRingProduct.length_record]
  nlinarith

/-- The same nonempty public array pays word width and a fixed constant. -/
theorem width_and_one_le_public_length (lengthExponent wordWidth : ℕ)
    (real imaginary : Fin (2 ^ lengthExponent) → ℤ) (widthPositive : 0 < wordWidth) :
    wordWidth ≤ (Spec.SignedRingProduct.record wordWidth real imaginary).length ∧
      1 ≤ (Spec.SignedRingProduct.record wordWidth real imaginary).length := by
  have countPositive := Nat.two_pow_pos lengthExponent
  rw [Spec.SignedRingProduct.length_record]
  constructor <;> nlinarith

/-- A linear record charge is a bounded multiple of the padded volume used
by the section 8 cost table. The width-factor premise is the public format's
original word-width allowance, not an execution-cost assumption. -/
theorem record_cost_le_padded_volume (costPerBit widthFactor precision lengthExponent wordWidth : ℕ)
    (real imaginary : Fin (2 ^ lengthExponent) → ℤ) (widthBound : wordWidth ≤ widthFactor * precision) :
    costPerBit * (Spec.SignedRingProduct.record wordWidth real imaginary).length ≤
      (2 * costPerBit * widthFactor) * (2 ^ lengthExponent * precision) := by
  calc
    costPerBit * (Spec.SignedRingProduct.record wordWidth real imaginary).length =
        (costPerBit * (2 * 2 ^ lengthExponent)) * wordWidth := by
      rw [Spec.SignedRingProduct.length_record]
      ring
    _ ≤ (costPerBit * (2 * 2 ^ lengthExponent)) * (widthFactor * precision) :=
      Nat.mul_le_mul_left _ widthBound
    _ = (2 * costPerBit * widthFactor) * (2 ^ lengthExponent * precision) := by ring

end IntegerMultBounds.Machine.RecoverRecordBudget
