module

public import IntegerMultBounds.Machine.RecoverRecordReady

/-! Public contiguous record extraction and native recovery execute as one
fixed machine. Adapter source/ruler tapes are reclaimed before native recovery;
only the exact-width product remains at the end. The supplied numerical
coefficient interface can be discharged by RecoverRecordFormat's transform
bridge; synthesizing the chunk/precision/width rulers remains upstream work. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverPublicOutput
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverRecordArray (Pair raw native)

def slots : Fin (3+11) ≃ Fin 14 where
  toFun := ![13,12,10,0,1,2,3,4,5,6,7,8,9,11]
  invFun := ![3,4,5,6,7,8,9,10,11,12,2,13,1,0]
  left_inv := by decide
  right_inv := by decide

def controls (chunkWidth precision : ℕ) (clock : List Bool) : Tapes 11 alphabet :=
  ⟨fun _ => 0, ![fun _ => blank,fun _ => blank,word (List.replicate chunkWidth true),
    fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
    word (List.replicate precision true),fun _ => blank,word clock]⟩

def emptyBank : Tapes 2 alphabet := ⟨fun _ => 0,fun _ => fun _ => blank⟩

def adapter : Program 14 32 alphabet := reindex (extend RecoverRecordReady.program 11) slots
def program : Program 14 159 alphabet := seq adapter (extend RecoverOutput.program 2)

def input (pairs : List Pair) (wordWidth chunkWidth precision : ℕ) (clock : List Bool) : Tapes 14 alphabet :=
  ((RecoverRecordReady.input pairs (List.replicate wordWidth true)).append (controls chunkWidth precision clock)).reindex slots

def output (recovered : List Bool) (inputLength : ℕ) : Tapes 14 alphabet :=
  (RecoverOutput.output recovered inputLength).append emptyBank

private theorem ready_bank (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkWidth precision : ℕ) (clock : List Bool)
    (encodedWords : records.map RecoverArray.Coefficient.bits = pairs.map fun pair => pair.1.reverse) :
    ((RecoverRecordReady.output (alphabet := alphabet) pairs).append (controls chunkWidth precision clock)).reindex slots =
      (RecoverOutput.input records chunkWidth precision clock).append emptyBank := by
  unfold RecoverOutput.input RecoverLoad.input RecoverLoad.bank
  rw [encodedWords]
  unfold RecoverRecordReady.output RecoverRecordField.bank RulerCopy.cfg Config.tapes
    controls Tapes.append Tapes.reindex slots emptyBank RecoverLoad.ready RecoverIterationFinish.bank
  congr 1
  · apply List.ofFn_injective; rfl
  · apply List.ofFn_injective
    simp only [RecoverRecordReady.native_cells, putWord_blank_origin, Schoenhage.WTape.tape,
      Schoenhage.WTape.words, List.reverse_nil, List.nil_append]
    rfl

def cost (pairs : List Pair) (wordWidth inputLength : ℕ) :=
  (8 * wordWidth + 21) * pairs.length +
    (native (alphabet := alphabet) pairs).length + (raw pairs).length + 2 * wordWidth + 11 +
    160 * ((native (alphabet := alphabet) pairs).length + wordWidth + inputLength + 1)

/-- Both stream volumes are determined by the actual fixed-width fields. -/
theorem stream_lengths (pairs : List Pair) (wordWidth : ℕ)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth) :
    (raw pairs).length = 2 * wordWidth * pairs.length ∧
      (native (alphabet := alphabet) pairs).length = (wordWidth + 1) * pairs.length := by
  induction pairs with
  | nil => simp [raw, native]
  | cons pair rest inductionHypothesis =>
    obtain ⟨realWidth, imaginaryWidth⟩ := fieldWidths pair (by simp)
    obtain ⟨tailRaw, tailNative⟩ := inductionHypothesis
      (fun next member => fieldWidths next (List.mem_cons_of_mem pair member))
    simp only [raw, native, List.flatMap_cons, List.length_append, List.length_map,
      List.length_reverse, List.length_nil, List.length_cons] at *
    constructor <;> nlinarith

/-- The entire public adaptation, cleanup and exact output pipeline is linear
in the original contiguous source volume, word width and input clock length. -/
theorem cost_le (pairs : List Pair) (wordWidth inputLength : ℕ) (widthPositive : 0 < wordWidth)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth) :
    cost (alphabet := alphabet) pairs wordWidth inputLength ≤
      200 * ((raw pairs).length + wordWidth + inputLength + 1) := by
  obtain ⟨sourceLength, nativeLength⟩ := stream_lengths (alphabet := alphabet) pairs wordWidth fieldWidths
  have countPaid := Nat.mul_le_mul_right pairs.length (show 1 ≤ wordWidth by omega)
  simp only [one_mul] at countPaid
  unfold cost
  rw [sourceLength, nativeLength]
  nlinarith

/-- One executed pipeline begins with contiguous public fields and ends with
only the exact product. No pre-extracted native source or head-positioning
premise is supplied. The coefficient labels are mathematical ghosts, and
matching the physical words is a representation equality. -/
theorem runs_recover (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkWidth precision wordWidth inputLength : ℕ) (leftInput rightInput : List Bool)
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
        (· = input pairs wordWidth chunkWidth precision leftInput) (· = output recovered inputLength)
        (cost (alphabet := alphabet) pairs wordWidth inputLength) ∧
      (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength).length = 2 * inputLength ∧
      binaryValue (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength) =
        binaryValue leftInput * binaryValue rightInput := by
  have prepared := hoare_place
    (RecoverRecordReady.runs_ready (alphabet := alphabet) pairs (List.replicate wordWidth true)
      (by simpa using (show 0 < wordWidth by omega)) (by simpa using fieldWidths))
    slots (controls (alphabet := alphabet) chunkWidth precision leftInput)
  rw [ready_bank pairs records chunkWidth precision leftInput encodedWords] at prepared
  obtain ⟨recovered, nativeRun, outputLength, outputValue⟩ := RecoverOutput.runs_recover (alphabet := alphabet)
    records chunkWidth precision wordWidth inputLength leftInput rightInput leftLength rightLength
    precisionPositive precisionFits chunkPositive chunkFits recordsGood coefficientsCorrect
  have recoveredRun := FamilyPlacementAlphabet.extend_hoare nativeRun (emptyBank (alphabet := alphabet))
  have sourceVolume : Schoenhage.clen (records.map RecoverArray.Coefficient.bits) =
      (native (alphabet := alphabet) pairs).length := by
    rw [encodedWords, RecoverRecordReady.native_cells, Schoenhage.length_cells]
  refine ⟨recovered, ?_, outputLength, outputValue⟩
  unfold program adapter
  apply (prepared.seq recoveredRun).consequence (fun _ ready => ready) (fun _ finished => finished)
  simp only [List.length_replicate, sourceVolume]
  unfold cost
  omega

/-- The complete adapter/recovery bank has no retained transform source,
controls, clock or scratch after the product is installed. -/
theorem workspace_blank (recovered : List Bool) (inputLength : ℕ) (slot : Fin 14) (notOutput : slot ≠ 0) :
    (output (alphabet := alphabet) recovered inputLength).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) recovered inputLength).head slot = 0 := by
  fin_cases slot
  · exact False.elim (notOutput rfl)
  all_goals exact ⟨rfl,rfl⟩
/-- Actual halted execution from public fields, the EndToEnd product output
contract, and a completely blank workspace. The original contiguous source
volume pays for extraction, all cleanup, and the native recovery execution. -/
theorem runs_correct (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkWidth precision wordWidth inputLength : ℕ) (leftInput rightInput : List Bool)
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth)
    (encodedWords : records.map RecoverArray.Coefficient.bits = pairs.map fun pair => pair.1.reverse)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ elapsed finalConfig,
      elapsed ≤ 200 * ((raw pairs).length + wordWidth + inputLength + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input pairs wordWidth chunkWidth precision leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 14, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
  obtain ⟨recovered, execution, wordLength, wordValue⟩ := runs_recover (alphabet := alphabet) pairs records
    chunkWidth precision wordWidth inputLength leftInput rightInput leftLength rightLength
    precisionPositive precisionFits chunkPositive chunkFits fieldWidths encodedWords recordsGood coefficientsCorrect
  obtain ⟨elapsed, finalConfig, bounded, executed, halted, endpoint⟩ := execution _ rfl
  refine ⟨elapsed, finalConfig, bounded.trans (cost_le pairs wordWidth inputLength (by omega) fieldWidths),
    executed, halted, ?_, ?_⟩
  · refine ⟨RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength, wordLength, wordValue, ?_⟩
    change finalConfig.tapes.tape (0 : Fin 14) = _
    rw [endpoint]
    exact putWord_blank_origin _
  · intro slot notOutput
    rw [endpoint]
    exact workspace_blank recovered inputLength slot notOutput

/-- At the manuscript precision, actual public transform numerator words
suffice for the same genuine product execution. Every rounding margin, packing
identity and recovery-ruler fit is derived here from the numerical guarantees
and size relations; no exact coefficient array is a caller hypothesis. -/
theorem runs_computed {coordinates : Type*} [Fintype coordinates] {scaledError : ℝ}
    (chunkWidth lengthExponent wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool) (real imaginary : Fin (2 ^ lengthExponent) → ℤ)
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
      elapsed ≤ 200 * ((Spec.SignedRingProduct.record wordWidth real imaginary).length + wordWidth + inputLength + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input (RecoverRecordArray.publicPairs wordWidth real imaginary) wordWidth chunkWidth
          (6 * chunkWidth - (2 * chunkWidth + 4 + 2 * lengthExponent)) leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 14, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
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
    records chunkWidth _ wordWidth inputLength leftInput rightInput leftLength rightLength precisionPositive
    precisionFits chunkPositive chunkFits (by
      intro pair member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      simp) encodedWords goodRecords productIdentity
  simpa only [RecoverRecordArray.raw_public] using execution

end
end IntegerMultBounds.Machine.RecoverPublicOutput
