module

public import IntegerMultBounds.Machine.RecoverControlSetup

/-! Recovery from contiguous public transform records with binary controls.
The single fixed program constructs all unary rulers, consumes their binary
descriptors, executes public-record adaptation and exact product recovery, and
leaves every non-output tape blank. Header decoding and computation of the
binary parameter descriptors remain upstream fast-program obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverBinaryOutput
noncomputable section
variable {alphabet : ℕ}
open RecoverRecordArray (Pair raw)

def program : Program 20 252 alphabet :=
  seq RecoverControlSetup.program (extend RecoverPublicOutput.program 6)

def input (pairs : List Pair) (chunkBits precisionBits widthBits clock : List Bool) : Tapes 20 alphabet :=
  RecoverControlSetup.input pairs chunkBits precisionBits widthBits clock

def output (recovered : List Bool) (inputLength : ℕ) : Tapes 20 alphabet :=
  (RecoverPublicOutput.output recovered inputLength).append RecoverControlSetup.emptyWork

def cost (pairs : List Pair) (chunkWidth precision wordWidth inputLength : ℕ)
    (chunkBits precisionBits widthBits : List Bool) :=
  8 * (chunkWidth + precision + wordWidth) +
    9 * (chunkBits.length + precisionBits.length + widthBits.length) + 96 +
    RecoverPublicOutput.cost (alphabet := alphabet) pairs wordWidth inputLength

/-- The original record and binary descriptor volumes pay for all control
construction and recovery, without a canonical descriptor-width assumption. -/
theorem cost_le (pairs : List Pair) (chunkWidth precision wordWidth inputLength : ℕ)
    (chunkBits precisionBits widthBits : List Bool)
    (widthPositive : 0 < wordWidth) (precisionFits : precision ≤ wordWidth) (chunkFits : chunkWidth ≤ wordWidth)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth) :
    cost (alphabet := alphabet) pairs chunkWidth precision wordWidth inputLength chunkBits precisionBits widthBits ≤
      300 * ((raw pairs).length + wordWidth + inputLength + chunkBits.length + precisionBits.length + widthBits.length + 1) := by
  have recoveryBound := RecoverPublicOutput.cost_le (alphabet := alphabet) pairs wordWidth inputLength widthPositive fieldWidths
  unfold cost
  omega

theorem runs_recover (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkBits precisionBits widthBits : List Bool) (chunkWidth precision wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool)
    (chunkValue : Counter.value chunkBits = chunkWidth) (precisionValue : Counter.value precisionBits = precision)
    (widthValue : Counter.value widthBits = wordWidth)
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth)
    (encodedWords : records.map RecoverArray.Coefficient.bits = pairs.map fun pair => pair.1.reverse)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ recovered,
      HoareTime (program (alphabet := alphabet))
        (· = input pairs chunkBits precisionBits widthBits leftInput) (· = output recovered inputLength)
        (cost (alphabet := alphabet) pairs chunkWidth precision wordWidth inputLength chunkBits precisionBits widthBits) ∧
      (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength).length = 2 * inputLength ∧
      binaryValue (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength) =
        binaryValue leftInput * binaryValue rightInput := by
  have setup := RecoverControlSetup.runs_setup (alphabet := alphabet) pairs chunkBits precisionBits widthBits leftInput
    chunkWidth precision wordWidth chunkValue precisionValue widthValue
  obtain ⟨recovered, publicRun, wordLength, wordValue⟩ := RecoverPublicOutput.runs_recover (alphabet := alphabet)
    pairs records chunkWidth precision wordWidth inputLength leftInput rightInput leftLength rightLength
    precisionPositive precisionFits chunkPositive chunkFits fieldWidths encodedWords recordsGood coefficientsCorrect
  have recovery := FamilyPlacementAlphabet.extend_hoare publicRun (RecoverControlSetup.emptyWork (alphabet := alphabet))
  refine ⟨recovered, ?_, wordLength, wordValue⟩
  unfold program
  apply (setup.seq recovery).consequence (fun _ ready => ready) (fun _ finished => finished)
  unfold cost
  omega

theorem workspace_blank (recovered : List Bool) (inputLength : ℕ) (slot : Fin 20) (notOutput : slot ≠ 0) :
    (output (alphabet := alphabet) recovered inputLength).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) recovered inputLength).head slot = 0 := by
  fin_cases slot
  · exact False.elim (notOutput rfl)
  all_goals exact ⟨rfl,rfl⟩

/-- Actual halted multiplication output from public record bits and three
binary descriptors. All generated rulers and private controller storage are
consumed and physically blank on the same final twenty-tape bank. -/
theorem runs_correct (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkBits precisionBits widthBits : List Bool) (chunkWidth precision wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool)
    (chunkValue : Counter.value chunkBits = chunkWidth) (precisionValue : Counter.value precisionBits = precision)
    (widthValue : Counter.value widthBits = wordWidth)
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth)
    (encodedWords : records.map RecoverArray.Coefficient.bits = pairs.map fun pair => pair.1.reverse)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ elapsed finalConfig,
      elapsed ≤ 300 * ((raw pairs).length + wordWidth + inputLength + chunkBits.length + precisionBits.length + widthBits.length + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input pairs chunkBits precisionBits widthBits leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 20, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
  obtain ⟨recovered, execution, wordLength, wordValue⟩ := runs_recover (alphabet := alphabet) pairs records
    chunkBits precisionBits widthBits chunkWidth precision wordWidth inputLength leftInput rightInput
    chunkValue precisionValue widthValue leftLength rightLength precisionPositive precisionFits chunkPositive
    chunkFits fieldWidths encodedWords recordsGood coefficientsCorrect
  obtain ⟨elapsed, finalConfig, bounded, executed, halted, endpoint⟩ := execution _ rfl
  refine ⟨elapsed, finalConfig, bounded.trans
    (cost_le pairs chunkWidth precision wordWidth inputLength chunkBits precisionBits widthBits
      (by omega) precisionFits (by omega) fieldWidths), executed, halted, ?_, ?_⟩
  · refine ⟨RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength, wordLength, wordValue, ?_⟩
    change finalConfig.tapes.tape (0 : Fin 20) = _
    rw [endpoint]
    exact putWord_blank_origin _
  · intro slot notOutput
    rw [endpoint]
    exact workspace_blank recovered inputLength slot notOutput

/-- Actual computed-transform numerators with binary controls yield the exact
product. The program synthesizes every unary ruler; coefficient margins,
packing correctness and ruler fits follow from the transform/size guarantees.
The three marked binary descriptors are still supplied by upstream setup. -/
theorem runs_computed {coordinates : Type*} [Fintype coordinates] {scaledError : ℝ}
    (chunkWidth lengthExponent wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool) (real imaginary : Fin (2 ^ lengthExponent) → ℤ)
    (chunkBits precisionBits widthBits : List Bool)
    (chunkValue : Counter.value chunkBits = chunkWidth)
    (precisionValue : Counter.value precisionBits = 6 * chunkWidth - (2 * chunkWidth + 4 + 2 * lengthExponent))
    (widthValue : Counter.value widthBits = wordWidth)
    (forward : (ZMod (2 ^ lengthExponent) → ℂ) →L[ℂ] (coordinates → ℂ))
    (computedForward : (ZMod (2 ^ lengthExponent) → ℂ) → (coordinates → ℂ))
    (backward : (coordinates → ℂ) →L[ℂ] (ZMod (2 ^ lengthExponent) → ℂ))
    (computedBackward : (coordinates → ℂ) → (ZMod (2 ^ lengthExponent) → ℂ))
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (chunkLarge : 3 ≤ chunkWidth) (lengthFits : lengthExponent ≤ chunkWidth)
    (wordFits : 6 * chunkWidth ≤ wordWidth)
    (convolutionFits : (NLogN.digitsOf chunkWidth leftInput).length +
      (NLogN.digitsOf chunkWidth rightInput).length ≤ 2 ^ lengthExponent + 1)
    (lowerBounds : ∀ index, -(2 : ℤ) ^ (wordWidth - 1) ≤ real index)
    (upperBounds : ∀ index, real index < (2 : ℤ) ^ (wordWidth - 1))
    (transformReadout : ∀ index,
      (ExactRecovery.computed (p := 6 * chunkWidth) computedForward computedBackward
        (ExactRecovery.scaledDigits (2 ^ lengthExponent) chunkWidth (NLogN.digitsOf chunkWidth leftInput))
        (ExactRecovery.scaledDigits (2 ^ lengthExponent) chunkWidth (NLogN.digitsOf chunkWidth rightInput))
        (index.val : ZMod (2 ^ lengthExponent))).re = (real index : ℝ) / 2 ^ (6 * chunkWidth))
    (forwardContractive : ‖forward‖ ≤ 1)
    (forwardError : ∀ input : ZMod (2 ^ lengthExponent) → ℂ, ‖input‖ ≤ 1 / 2 →
      2 ^ (6 * chunkWidth) * ‖computedForward input - forward input‖ ≤ scaledError)
    (backwardContractive : ‖backward‖ ≤ 1)
    (backwardError : ∀ input : coordinates → ℂ, ‖input‖ ≤ 1 / 2 →
      2 ^ (6 * chunkWidth) * ‖computedBackward input - backward input‖ ≤ scaledError)
    (errorSmall : scaledError ≤ 2 ^ (6 * chunkWidth) / 100)
    (convolutionIdentity : ∀ left right : ZMod (2 ^ lengthExponent) → ℂ,
      backward (fun coordinate => forward left coordinate * forward right coordinate) =
        fun index => NLogN.cconv left right index / ((2 ^ lengthExponent : ℕ) : ℂ) ^ 2)
    (finalMargin : (2 : ℝ) ^ (2 * chunkWidth + 4) * (2 ^ lengthExponent : ℕ) ^ 2 *
      (3 * scaledError + 2) < 2 ^ (6 * chunkWidth) / 2) :
    ∃ elapsed finalConfig,
      elapsed ≤ 300 * ((Spec.SignedRingProduct.record wordWidth real imaginary).length + wordWidth + inputLength +
        chunkBits.length + precisionBits.length + widthBits.length + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input (RecoverRecordArray.publicPairs wordWidth real imaginary) chunkBits precisionBits widthBits leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 20, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
  let coefficientWords := fun index => (Spec.SignedRingProduct.compWord wordWidth (real index)).reverse
  let records := RecoverNumericalBridge.records chunkWidth leftInput rightInput coefficientWords
  have widthPositive : 1 ≤ wordWidth := by omega
  have chunkPositive : 0 < chunkWidth := by omega
  obtain ⟨precisionPositive, precisionFits, chunkFits⟩ := RecoverRecordFormat.precision_controls_six
    chunkWidth lengthExponent wordWidth chunkLarge lengthFits wordFits
  have goodRecords := RecoverRecordFormat.records_good_public_computed chunkWidth lengthExponent (6 * chunkWidth)
    wordWidth leftInput rightInput real forward computedForward backward computedBackward chunkPositive (by omega)
    widthPositive lowerBounds upperBounds transformReadout forwardContractive forwardError backwardContractive
    backwardError errorSmall convolutionIdentity finalMargin
  have encodedWords : records.map RecoverArray.Coefficient.bits =
      (RecoverRecordArray.publicPairs wordWidth real imaginary).map fun pair => pair.1.reverse := by
    simp only [records, coefficientWords, RecoverNumericalBridge.records, RecoverRecordArray.publicPairs,
      List.ofFn_eq_map, List.map_map, Function.comp_def]
  have productIdentity := RecoverNumericalBridge.records_product chunkWidth leftInput rightInput coefficientWords
    chunkPositive convolutionFits
  have execution := runs_correct (alphabet := alphabet) (RecoverRecordArray.publicPairs wordWidth real imaginary)
    records chunkBits precisionBits widthBits chunkWidth _ wordWidth inputLength leftInput rightInput
    chunkValue precisionValue widthValue leftLength rightLength precisionPositive
    precisionFits chunkPositive chunkFits (by
      intro pair member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      simp) encodedWords goodRecords productIdentity
  simpa only [RecoverRecordArray.raw_public] using execution

end
end IntegerMultBounds.Machine.RecoverBinaryOutput
