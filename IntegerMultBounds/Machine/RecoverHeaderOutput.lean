module

public import IntegerMultBounds.Machine.RecoverHeaderControlSetup

/-! The public gamma header and contiguous transform record suffice for actual
exact multiplication recovery. One fixed program derives its own parameters
and rulers, executes native recovery, and leaves only the twice-width product. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverHeaderOutput
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverRecordArray (Pair raw)

def recoverySlots : Fin (14+8) ≃ Fin 22 where
  toFun := ![0,1,18,3,4,5,6,7,17,9,10,21,20,19,2,8,11,12,13,14,15,16]
  invFun := ![0,1,14,3,4,5,6,7,15,9,10,16,17,18,19,20,21,8,2,13,12,11]
  left_inv := by decide
  right_inv := by decide

def program := seq (extend (RecoverHeaderControlSetup.program (alphabet := alphabet)) 2)
  (Placement.placed RecoverPublicOutput.program recoverySlots)

def source (pairs : List Pair) (clock : List Bool) : Tapes 2 alphabet :=
  ⟨fun _ => 0,![word (raw pairs),word clock]⟩

def input (pairs : List Pair) (precision lengthExponent wordWidth : ℕ) (clock : List Bool) : Tapes 22 alphabet :=
  (RecoverHeaderControlSetup.input precision lengthExponent wordWidth).append (source pairs clock)

def output (recovered : List Bool) (inputLength : ℕ) : Tapes 22 alphabet :=
  ((RecoverPublicOutput.output recovered inputLength).append (SharedBank.empty 8 alphabet)).reindex recoverySlots

def cost (pairs : List Pair) (chunkWidth lengthExponent wordWidth inputLength : ℕ) :=
  RecoverHeaderControlSetup.cost (6*chunkWidth) lengthExponent wordWidth + 1 +
    RecoverPublicOutput.cost (alphabet := alphabet) pairs wordWidth inputLength

private theorem ready_bank (pairs : List Pair) (chunkWidth lengthExponent wordWidth : ℕ) (clock : List Bool) :
    ((RecoverPublicOutput.input pairs wordWidth chunkWidth (6*chunkWidth-(2*chunkWidth+4+2*lengthExponent)) clock).append
      (SharedBank.empty 8 alphabet)).reindex recoverySlots =
        (RecoverHeaderControlSetup.output (6*chunkWidth) lengthExponent wordWidth).append (source pairs clock) := by
  have quotient : 6*chunkWidth/6 = chunkWidth := by omega
  unfold RecoverHeaderControlSetup.output
  rw [quotient]
  unfold RecoverPublicOutput.input RecoverPublicOutput.controls RecoverPublicOutput.slots Tapes.reindex Tapes.append
    RecoverRecordReady.input RecoverRecordField.bank RulerCopy.cfg Config.tapes SharedBank.empty source recoverySlots
    SharedPlacementAlphabet.setTape
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_recover (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkWidth lengthExponent wordWidth inputLength : ℕ) (leftInput rightInput : List Bool)
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (chunkLarge : 3 ≤ chunkWidth) (lengthFits : lengthExponent ≤ chunkWidth) (wordFits : 6*chunkWidth ≤ wordWidth)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth)
    (encodedWords : records.map RecoverArray.Coefficient.bits = pairs.map fun pair => pair.1.reverse)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth (6*chunkWidth-(2*chunkWidth+4+2*lengthExponent)) record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ recovered,
      HoareTime (program (alphabet := alphabet))
        (· = input pairs (6*chunkWidth) lengthExponent wordWidth leftInput) (· = output recovered inputLength)
        (cost (alphabet := alphabet) pairs chunkWidth lengthExponent wordWidth inputLength) ∧
      (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength).length = 2 * inputLength ∧
      binaryValue (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength) =
        binaryValue leftInput * binaryValue rightInput := by
  have setup := FamilyPlacementAlphabet.extend_hoare
    (RecoverHeaderControlSetup.runs_six (alphabet := alphabet) chunkWidth lengthExponent wordWidth chunkLarge lengthFits (by omega))
    (source (alphabet := alphabet) pairs leftInput)
  obtain ⟨precisionPositive,precisionFits,chunkFits⟩ := RecoverRecordFormat.precision_controls_six
    chunkWidth lengthExponent wordWidth chunkLarge lengthFits wordFits
  obtain ⟨recovered,publicRun,wordLength,wordValue⟩ := RecoverPublicOutput.runs_recover (alphabet := alphabet)
    pairs records chunkWidth _ wordWidth inputLength leftInput rightInput leftLength rightLength
    precisionPositive precisionFits (by omega) chunkFits fieldWidths encodedWords recordsGood coefficientsCorrect
  have recovery := hoare_place publicRun recoverySlots (SharedBank.empty 8 alphabet)
  rw [ready_bank] at recovery
  refine ⟨recovered,?_,wordLength,wordValue⟩
  unfold program
  apply (setup.seq recovery).consequence (fun _ ready => ready) (fun _ finished => finished)
  exact le_rfl

theorem workspace_blank (recovered : List Bool) (inputLength : ℕ) (slot : Fin 22) (notOutput : slot ≠ 0) :
    (output (alphabet := alphabet) recovered inputLength).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) recovered inputLength).head slot = 0 := by
  fin_cases slot
  · exact False.elim (notOutput rfl)
  all_goals exact ⟨rfl,rfl⟩

theorem runs_correct (pairs : List Pair) (records : List RecoverArray.Coefficient)
    (chunkWidth lengthExponent wordWidth inputLength : ℕ) (leftInput rightInput : List Bool)
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (chunkLarge : 3 ≤ chunkWidth) (lengthFits : lengthExponent ≤ chunkWidth) (wordFits : 6*chunkWidth ≤ wordWidth)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = wordWidth ∧ pair.2.length = wordWidth)
    (encodedWords : records.map RecoverArray.Coefficient.bits = pairs.map fun pair => pair.1.reverse)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth (6*chunkWidth-(2*chunkWidth+4+2*lengthExponent)) record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ elapsed finalConfig,
      elapsed ≤ RecoverHeaderControlSetup.cost (6*chunkWidth) lengthExponent wordWidth + 1 +
        200 * ((raw pairs).length + wordWidth + inputLength + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input pairs (6*chunkWidth) lengthExponent wordWidth leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 22, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
  obtain ⟨recovered,execution,wordLength,wordValue⟩ := runs_recover (alphabet := alphabet) pairs records
    chunkWidth lengthExponent wordWidth inputLength leftInput rightInput leftLength rightLength
    chunkLarge lengthFits wordFits fieldWidths encodedWords recordsGood coefficientsCorrect
  obtain ⟨elapsed,finalConfig,bounded,executed,halted,endpoint⟩ := execution _ rfl
  have recoveryBound := RecoverPublicOutput.cost_le (alphabet := alphabet) pairs wordWidth inputLength (by omega) fieldWidths
  refine ⟨elapsed,finalConfig,?_,executed,halted,?_,?_⟩
  · unfold cost at bounded
    omega
  · refine ⟨RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength,wordLength,wordValue,?_⟩
    change finalConfig.tapes.tape (0 : Fin 22) = _
    rw [endpoint]
    exact putWord_blank_origin _
  · intro slot notOutput
    rw [endpoint]
    exact workspace_blank recovered inputLength slot notOutput

/-- Computed-transform guarantees give exact multiplication using only the
original public gamma header, signed record and input-width clock. No decoded
parameters, prebuilt rulers or residual-precision descriptor are supplied. -/
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
      elapsed ≤ RecoverHeaderControlSetup.cost (6*chunkWidth) lengthExponent wordWidth + 1 +
        200 * ((Spec.SignedRingProduct.record wordWidth real imaginary).length + wordWidth + inputLength + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input (RecoverRecordArray.publicPairs wordWidth real imaginary) (6*chunkWidth) lengthExponent wordWidth leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 22, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
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
    records chunkWidth lengthExponent wordWidth inputLength leftInput rightInput
    leftLength rightLength chunkLarge lengthFits wordFits (by
      intro pair member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      simp) encodedWords goodRecords productIdentity
  simpa only [RecoverRecordArray.raw_public] using execution


end
end IntegerMultBounds.Machine.RecoverHeaderOutput
