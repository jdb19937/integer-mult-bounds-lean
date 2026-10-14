module

public import IntegerMultBounds.Machine.RecoverIterationFinish

/-! A recurring section 8 iteration from a loaded signed numerator. Recovery,
all workspace cleanup, carry rollover and chunk publication execute on the same
ten-tape bank. Both rulers and every scratch tape are ready for the next load.
The uniform cost is linear in the signed input word width. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverIteration
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (sumBits)
open RecoverCoefficientRound (roundedBits)
open RecoverPrecisionSplit (fractionBits)

def program : Program 10 83 alphabet :=
  seq (seq (extend RecoverSignedCoefficient.program 1) (extend RecoverWorkspace.program 1))
    RecoverIterationFinish.program

def input (signedLowBits : List Bool) (sign : Bool) (carryBits : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :=
  (RecoverSignedCoefficient.input (alphabet := alphabet) signedLowBits sign carryBits chunkWidth precision).append
    (⟨fun _ => streamHead,fun _ => stream⟩ : Tapes 1 alphabet)

def digit (integerBits carryBits : List Bool) (guard : Bool) (chunkWidth : ℕ) :=
  (sumBits (roundedBits guard integerBits) carryBits).take chunkWidth
def nextCarry (integerBits carryBits : List Bool) (guard : Bool) (chunkWidth : ℕ) :=
  (sumBits (roundedBits guard integerBits) carryBits).drop chunkWidth

private theorem clean_bank (lowerBits integerBits carryBits : List Bool) (guard : Bool) (chunkWidth : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ)
    (chunkLength : (digit integerBits carryBits guard chunkWidth).length = chunkWidth) :
    (RecoverWorkspace.output (alphabet := alphabet) lowerBits integerBits carryBits guard chunkWidth).append
      (⟨fun _ => streamHead,fun _ => stream⟩ : Tapes 1 alphabet) =
      RecoverIterationFinish.input (nextCarry integerBits carryBits guard chunkWidth)
        (digit integerBits carryBits guard chunkWidth) chunkWidth (fractionBits lowerBits guard).length stream streamHead := by
  unfold RecoverWorkspace.output RecoverIterationFinish.input RecoverIterationFinish.bank Tapes.append
  rw [chunkLength]
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_iteration (signedLowBits : List Bool) (sign : Bool)
    (lowerBits integerBits carryBits : List Bool) (guard : Bool) (coefficient chunkWidth : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ)
    (layout : RecoverMagnitude.magnitude signedLowBits sign = RecoverPrecisionSplit.sourceBits lowerBits guard integerBits)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ integerBits.length)
    (carryWidth : carryBits.length ≤ (signedLowBits ++ [sign]).length)
    (approximationClose : |(TwosComplement.signed (signedLowBits ++ [sign]) : ℝ) /
      2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2) :
    HoareTime (program (alphabet := alphabet))
      (· = input signedLowBits sign carryBits chunkWidth (lowerBits.length + 1) stream streamHead)
      (fun finalBank => finalBank = RecoverIterationFinish.output (nextCarry integerBits carryBits guard chunkWidth)
          (digit integerBits carryBits guard chunkWidth) chunkWidth (lowerBits.length + 1) stream streamHead ∧
        (digit integerBits carryBits guard chunkWidth).length = chunkWidth ∧
        Counter.value (digit integerBits carryBits guard chunkWidth) =
          (coefficient + Counter.value carryBits) % 2 ^ chunkWidth ∧
        Counter.value (nextCarry integerBits carryBits guard chunkWidth) =
          (coefficient + Counter.value carryBits) / 2 ^ chunkWidth ∧
        (nextCarry integerBits carryBits guard chunkWidth).length ≤ (signedLowBits ++ [sign]).length)
      (128 * (signedLowBits ++ [sign]).length) := by
  have native := RecoverSignedCoefficient.runs_signed (alphabet := alphabet) signedLowBits sign lowerBits integerBits
    carryBits guard coefficient chunkWidth layout chunkFits approximationClose
  have nativeExact := native.consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis.1) le_rfl
  have recovered := FamilyPlacementAlphabet.extend_hoare nativeExact
    (⟨fun _ => streamHead,fun _ => stream⟩ : Tapes 1 alphabet)
  have clean := FamilyPlacementAlphabet.extend_hoare
    (RecoverWorkspace.runs_cleanup (alphabet := alphabet) signedLowBits sign lowerBits integerBits carryBits guard chunkWidth layout)
    (⟨fun _ => streamHead,fun _ => stream⟩ : Tapes 1 alphabet)
  have roundedWidths := RecoverCoefficientStep.rounded_length guard integerBits
  have sumLowerWidth := BinaryAccumulate.sumWord_length_ge (roundedBits guard integerBits) carryBits
  have sumUpperWidth := BinaryAccumulate.sumWord_length_le (roundedBits guard integerBits) carryBits
  have widths : (signedLowBits ++ [sign]).length = (fractionBits lowerBits guard).length + integerBits.length := by
    rw [← RecoverMagnitude.magnitude_length signedLowBits sign,layout]
    simp [RecoverPrecisionSplit.sourceBits]
  have chunkLength : (digit integerBits carryBits guard chunkWidth).length = chunkWidth := by
    simp only [digit,List.length_take,sumBits]
    dsimp only [sumBits,BinaryAccumulate.width] at sumLowerWidth
    omega
  have fractionalPositive : 0 < (fractionBits lowerBits guard).length := by simp [fractionBits]
  have coefficientWidth : (roundedBits guard integerBits).length ≤ (signedLowBits ++ [sign]).length := by omega
  have nextWidth : (nextCarry integerBits carryBits guard chunkWidth).length ≤ (signedLowBits ++ [sign]).length :=
    RecoverCarryStep.outgoing_width _ _ chunkWidth _ chunkPositive coefficientWidth carryWidth
  have published := RecoverIterationFinish.runs_finish (alphabet := alphabet)
    (nextCarry integerBits carryBits guard chunkWidth) (digit integerBits carryBits guard chunkWidth)
    chunkWidth (fractionBits lowerBits guard).length stream streamHead
  have cleanReady := clean.consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis.trans (clean_bank _ _ _ _ _ _ _ chunkLength)) le_rfl
  have stages := (recovered.seq cleanReady).seq published
  have values := RecoverCoefficientStep.step_values integerBits lowerBits carryBits guard coefficient chunkWidth chunkFits
    (RecoverMagnitude.split_magnitude_margin signedLowBits sign lowerBits integerBits guard coefficient layout approximationClose)
  apply stages.consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => ⟨by simpa only [fractionBits,List.length_append,List.length_cons,List.length_nil] using hypothesis,
      chunkLength,values.1,values.2,nextWidth⟩)
  rw [chunkLength]
  have inputPositive : 0 < (signedLowBits ++ [sign]).length := by simp
  omega

/-- Original-input form, deriving the split fields and preserving the recurring
carry-width invariant needed by the array loop. -/
theorem runs_iteration_exists (signedLowBits : List Bool) (sign : Bool) (carryBits : List Bool)
    (coefficient chunkWidth precision : ℕ) (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ (signedLowBits ++ [sign]).length)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ (signedLowBits ++ [sign]).length - precision)
    (carryWidth : carryBits.length ≤ (signedLowBits ++ [sign]).length)
    (approximationClose : |(TwosComplement.signed (signedLowBits ++ [sign]) : ℝ) /
      2 ^ precision - coefficient| < 1 / 2) :
    ∃ chunk nextCarryBits : List Bool, chunk.length = chunkWidth ∧
      Counter.value chunk = (coefficient + Counter.value carryBits) % 2 ^ chunkWidth ∧
      Counter.value nextCarryBits = (coefficient + Counter.value carryBits) / 2 ^ chunkWidth ∧
      nextCarryBits.length ≤ (signedLowBits ++ [sign]).length ∧
      HoareTime (program (alphabet := alphabet))
        (· = input signedLowBits sign carryBits chunkWidth precision stream streamHead)
        (· = RecoverIterationFinish.output nextCarryBits chunk chunkWidth precision stream streamHead)
        (128 * (signedLowBits ++ [sign]).length) := by
  obtain ⟨lowerBits,integerBits,guard,lowerLength,integerLength,layout,_⟩ :=
    RecoverSignedCoefficient.runs_signed_exists (alphabet := alphabet) signedLowBits sign carryBits coefficient chunkWidth
      precision precisionPositive precisionFits chunkFits approximationClose
  have executed := runs_iteration (alphabet := alphabet) signedLowBits sign lowerBits integerBits carryBits guard coefficient
    chunkWidth stream streamHead layout chunkPositive (by rw [integerLength]; exact chunkFits) carryWidth
    (by simpa only [lowerLength] using approximationClose)
  obtain ⟨elapsed,finalConfig,bounded,run,halted,endpoint,chunkLength,chunkValue,carryValue,nextWidth⟩ := executed _ rfl
  refine ⟨digit integerBits carryBits guard chunkWidth,nextCarry integerBits carryBits guard chunkWidth,
    chunkLength,chunkValue,carryValue,nextWidth,?_⟩
  have exactRun := executed.consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis.1) le_rfl
  simpa only [lowerLength] using exactRun

end
end IntegerMultBounds.Machine.RecoverIteration
