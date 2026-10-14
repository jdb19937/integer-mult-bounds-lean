module

public import IntegerMultBounds.Machine.RecoverCarryFlush
public import IntegerMultBounds.ExactRecoveryOutput

/-! Complete native section 8 recovery from a signed dyadic coefficient array.
One fixed program loads/rounds/carries every coefficient, erases the retained
array and controls, serializes exactly 2n MSB bits to tape zero using an original
n-bit operand as a clock, and erases every remaining work tape. The input is the
coefficient array and control words, never an already recovered output word. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverOutput
noncomputable section
variable {alphabet : ℕ}
open Schoenhage
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)

def serializeSlots : Fin (3+9) ≃ Fin 12 where
  toFun := ![9,11,0,1,2,3,4,5,6,7,8,10]
  invFun := ![2,3,4,5,6,7,8,9,10,0,11,1]
  left_inv := by decide
  right_inv := by decide

def serializePart : Program 12 12 alphabet := reindex (extend RecoverOutputSerialize.program 9) serializeSlots
def sourceClear : Program 12 6 alphabet :=
  seq (RecoverWorkspace.atProgram (MultiplicationInputSplit.shift .right) (9 : Fin 12))
    (RecoverWorkspace.atProgram RecoverArrayCleanup.eraseOrigin (9 : Fin 12))
def clockClear : Program 12 3 alphabet := RecoverWorkspace.atProgram EraseBack.program (11 : Fin 12)

def program : Program 12 127 alphabet :=
  seq (seq (seq (seq (seq (extend RecoverArray.program 1) RecoverCarryFlush.program)
    RecoverArrayCleanup.program) serializePart) sourceClear) clockClear

def input (records : List RecoverArray.Coefficient) (chunkWidth precision : ℕ) (clock : List Bool) :=
  (RecoverLoad.input (alphabet := alphabet) ⟨[],records.map RecoverArray.Coefficient.bits⟩ [] chunkWidth precision
    (fun _ => blank) 0).append (⟨fun _ => 0,fun _ => word clock⟩ : Tapes 1 alphabet)

def bank (source clock destination : ℤ → Fin (alphabet+4))
    (sourceHead clockHead destinationHead : ℤ) : Tapes 12 alphabet :=
  ⟨![destinationHead,0,0,0,0,0,0,0,0,sourceHead,0,clockHead],
    ![destination,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
      fun _ => blank,fun _ => blank,fun _ => blank,source,fun _ => blank,clock]⟩

def output (recovered : List Bool) (inputLength : ℕ) : Tapes 12 alphabet :=
  bank (fun _ => blank) (fun _ => blank)
    (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength)) 0 0 (2 * inputLength)

private theorem serialize_bank (source clock destination : ℤ → Fin (alphabet+4))
    (sourceHead clockHead destinationHead : ℤ) :
    ((RecoverOutputSerialize.bank source clock destination sourceHead clockHead destinationHead).append
      (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 9 alphabet)).reindex serializeSlots =
      bank source clock destination sourceHead clockHead destinationHead := by
  unfold RecoverOutputSerialize.bank Tapes.append Tapes.reindex serializeSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem runs_source_clear (recovered clock : List Bool) :
    HoareTime (sourceClear (alphabet := alphabet))
      (· = bank (word recovered) (word clock)
        (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered clock.length)) (-1) clock.length (2 * clock.length))
      (· = bank (fun _ => blank) (word clock)
        (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered clock.length)) 0 clock.length (2 * clock.length))
      (2 * recovered.length + 5) := by
  let initial := bank (alphabet := alphabet) (word recovered) (word clock)
    (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered clock.length)) (-1) clock.length (2 * clock.length)
  let shifted := setTape initial (9 : Fin 12) (initial.tape 9) (initial.head 9 + Move.right.offset)
  have moved := RecoverWorkspace.shift_at (9 : Fin 12) initial .right
  have cleared := RecoverArrayCleanup.erase_origin_at (9 : Fin 12) shifted (recovered.map bitSymbol) (nonblank _)
    (by simp [shifted,setTape]; rfl) (by simp [shifted,setTape]; rfl)
  have endpoint : RecoverWorkspace.erased shifted (9 : Fin 12) =
      bank (alphabet := alphabet) (fun _ => blank) (word clock)
        (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered clock.length)) 0 clock.length (2 * clock.length) := by
    unfold RecoverWorkspace.erased shifted initial setTape bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  apply (moved.seq cleared).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis.trans endpoint)
  simp only [List.length_map]
  omega

theorem runs_clock_clear (recovered clock : List Bool) :
    HoareTime (clockClear (alphabet := alphabet))
      (· = bank (fun _ => blank) (word clock)
        (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered clock.length)) 0 clock.length (2 * clock.length))
      (· = output recovered clock.length) (clock.length + 2) := by
  let initial := bank (alphabet := alphabet) (fun _ => blank) (word clock)
    (word (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered clock.length)) 0 clock.length (2 * clock.length)
  have cleared := RecoverWorkspace.erase_at (11 : Fin 12) initial (clock.map bitSymbol) (nonblank _)
    (by simp only [List.length_map]; rfl) (by rfl)
  have endpoint : RecoverWorkspace.erased initial (11 : Fin 12) = output (alphabet := alphabet) recovered clock.length := by
    unfold RecoverWorkspace.erased initial setTape bank output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  apply cleared.consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis.trans endpoint)
  simp only [List.length_map]
  omega

theorem source_volume (records : List RecoverArray.Coefficient) (wordWidth precision : ℕ)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record) :
    clen (records.map RecoverArray.Coefficient.bits) = (wordWidth + 1) * records.length := by
  induction records with
  | nil => simp
  | cons record records inductionHypothesis =>
    have width := (recordsGood record (by simp)).1
    have tail := inductionHypothesis (fun next member => recordsGood next (List.mem_cons_of_mem record member))
    simp only [List.map_cons,clen_cons,width,tail,List.length_cons]
    ring

/-- The complete fixed recovery machine produces the multiplication output
contract and leaves only tape zero nonblank. Numerical coefficient facts are
the mathematical recovery interface; no output word or execution is assumed. -/
theorem runs_recover (records : List RecoverArray.Coefficient) (chunkWidth precision wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool) (leftLength : leftInput.length = inputLength)
    (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ recovered : List Bool,
      HoareTime (program (alphabet := alphabet)) (· = input records chunkWidth precision leftInput)
        (· = output recovered inputLength)
        (160 * (clen (records.map RecoverArray.Coefficient.bits) + wordWidth + inputLength + 1)) ∧
      (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength).length = 2 * inputLength ∧
      binaryValue (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength) =
        binaryValue leftInput * binaryValue rightInput := by
  have productFits := product_fits leftLength rightLength
  obtain ⟨chunks,finalCarry,partialLength,carryWidth,valueEquation,arrayRun⟩ :=
    RecoverArray.runs_array (alphabet := alphabet) records [] [] [] chunkWidth precision wordWidth
      precisionPositive precisionFits chunkPositive chunkFits (by simp) recordsGood
  simp only [Counter.value,List.nil_append,List.append_nil] at valueEquation arrayRun
  let recovered := chunks.flatten ++ finalCarry
  have recoveredValue : Counter.value recovered = NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) := by
    simp only [recovered,TwosComplement.value_append,partialLength,pow_mul]
    simpa only [Nat.add_zero] using valueEquation
  have arrayFramed := FamilyPlacementAlphabet.extend_hoare arrayRun
    (⟨fun _ => 0,fun _ => word leftInput⟩ : Tapes 1 alphabet)
  have flushed := RecoverCarryFlush.runs_flush (alphabet := alphabet)
    (records.map RecoverArray.Coefficient.bits) finalCarry chunks.flatten leftInput chunkWidth precision
  have cleaned := RecoverArrayCleanup.runs_cleanup (alphabet := alphabet)
    (records.map RecoverArray.Coefficient.bits) finalCarry recovered leftInput chunkWidth precision
  have serialized := hoare_place (RecoverOutputSerialize.runs_serialize (alphabet := alphabet) recovered leftInput)
    serializeSlots (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 9 alphabet)
  unfold RecoverOutputSerialize.input RecoverOutputSerialize.output at serialized
  rw [serialize_bank,serialize_bank] at serialized
  have complete := (((((arrayFramed.seq flushed).seq cleaned).seq serialized).seq (runs_source_clear recovered leftInput)).seq
    (runs_clock_clear recovered leftInput))
  have exactValue : Counter.value recovered = binaryValue leftInput * binaryValue rightInput :=
    recoveredValue.trans coefficientsCorrect
  obtain ⟨outputLength,outputValue⟩ := RecoverOutputSerialize.output_spec (alphabet := alphabet) recovered inputLength
    (by rw [exactValue]; exact productFits)
  refine ⟨recovered,?_,outputLength,outputValue.trans exactValue⟩
  apply complete.consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => by simpa only [leftLength] using hypothesis)
  rw [leftLength]
  have chunkBound : chunkWidth ≤ wordWidth := by omega
  have volume := source_volume records wordWidth precision recordsGood
  have payloadBound : wordWidth * records.length ≤ clen (records.map RecoverArray.Coefficient.bits) := by rw [volume]; nlinarith
  have partialBound : chunks.flatten.length ≤ clen (records.map RecoverArray.Coefficient.bits) := by
    rw [partialLength]
    exact (Nat.mul_le_mul_right records.length chunkBound).trans payloadBound
  have recoveredBound : recovered.length ≤ clen (records.map RecoverArray.Coefficient.bits) + wordWidth := by
    simp only [recovered,List.length_append]
    omega
  nlinarith

theorem workspace_blank (recovered : List Bool) (inputLength : ℕ) (slot : Fin 12) (notOutput : slot ≠ 0) :
    (output (alphabet := alphabet) recovered inputLength).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) recovered inputLength).head slot = 0 := by
  fin_cases slot <;> first | contradiction | exact ⟨rfl,rfl⟩

/-- In the nonempty fast-path array, both controls and the original operand
clock are paid by source volume; no additional per-record canonicalization or
separate output-installation budget is needed. -/
theorem runs_recover_volume (records : List RecoverArray.Coefficient) (chunkWidth precision wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool) (leftLength : leftInput.length = inputLength)
    (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record) (recordsNonempty : records ≠ [])
    (clockVolume : inputLength ≤ clen (records.map RecoverArray.Coefficient.bits))
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ recovered : List Bool,
      HoareTime (program (alphabet := alphabet)) (· = input records chunkWidth precision leftInput)
        (· = output recovered inputLength) (640 * clen (records.map RecoverArray.Coefficient.bits)) ∧
      (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength).length = 2 * inputLength ∧
      binaryValue (RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength) =
        binaryValue leftInput * binaryValue rightInput := by
  obtain ⟨recovered,execution,wordLength,wordValue⟩ := runs_recover (alphabet := alphabet) records chunkWidth precision wordWidth
    inputLength leftInput rightInput leftLength rightLength precisionPositive precisionFits chunkPositive chunkFits
    recordsGood coefficientsCorrect
  refine ⟨recovered,?_,wordLength,wordValue⟩
  apply execution.consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  have countPositive := List.length_pos_of_ne_nil recordsNonempty
  have volume := source_volume records wordWidth precision recordsGood
  have chunkBound : chunkWidth ≤ wordWidth := by omega
  have productBound : chunkWidth * records.length ≤ wordWidth * records.length := Nat.mul_le_mul_right _ chunkBound
  have widthPositive : 0 < wordWidth := by omega
  nlinarith

/-- Genuine halted execution, the EndToEnd output contract, and every work
tape/head blank at origin, all from the original native recovery input. -/
theorem runs_correct (records : List RecoverArray.Coefficient) (chunkWidth precision wordWidth inputLength : ℕ)
    (leftInput rightInput : List Bool) (leftLength : leftInput.length = inputLength)
    (rightLength : rightInput.length = inputLength)
    (precisionPositive : 0 < precision) (precisionFits : precision ≤ wordWidth)
    (chunkPositive : 0 < chunkWidth) (chunkFits : chunkWidth ≤ wordWidth - precision)
    (recordsGood : ∀ record ∈ records, RecoverArray.Good wordWidth precision record)
    (coefficientsCorrect : NLogN.evalBase (2 ^ chunkWidth) (records.map RecoverArray.Coefficient.exact) =
      binaryValue leftInput * binaryValue rightInput) :
    ∃ elapsed finalConfig,
      elapsed ≤ 160 * (clen (records.map RecoverArray.Coefficient.bits) + wordWidth + inputLength + 1) ∧
      run (program (alphabet := alphabet)) elapsed
        ((input records chunkWidth precision leftInput).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      (∀ slot : Fin 12, slot ≠ 0 → finalConfig.tapes.tape slot = (fun _ => blank) ∧ finalConfig.tapes.head slot = 0) := by
  obtain ⟨recovered,execution,wordLength,wordValue⟩ := runs_recover (alphabet := alphabet) records chunkWidth precision wordWidth
    inputLength leftInput rightInput leftLength rightLength precisionPositive precisionFits chunkPositive chunkFits
    recordsGood coefficientsCorrect
  obtain ⟨elapsed,finalConfig,bounded,executed,halted,endpoint⟩ := execution _ rfl
  refine ⟨elapsed,finalConfig,bounded,executed,halted,?_,?_⟩
  · refine ⟨RecoverOutputSerialize.outputWord (alphabet := alphabet) recovered inputLength,wordLength,wordValue,?_⟩
    change finalConfig.tapes.tape (0 : Fin 12) = _
    rw [endpoint]
    exact putWord_blank_origin _
  · intro slot notOutput
    rw [endpoint]
    exact workspace_blank recovered inputLength slot notOutput

end
end IntegerMultBounds.Machine.RecoverOutput
