module

public import IntegerMultBounds.Machine.RecoverArray
public import IntegerMultBounds.Machine.ElementaryMultiplyOutputData

/-! Serialize the recovered little-endian value into exactly twice the input
length in MSB order. A retained original operand word clocks the existing
double-seek/reverse-copy machine. Extra high padding is ignored, missing high
bits are zero-filled, and correctness follows from the value fitting 2n bits. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverOutputSerialize
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open DoubleClockReverseCopy (copied)

def outputWord (bits : List Bool) (inputLength : ℕ) :=
  copied (word (alphabet := alphabet) bits) (2 * inputLength - 1) inputLength

theorem copied_prefix (bits : List Bool) (inputLength : ℕ) :
    outputWord (alphabet := alphabet) bits inputLength = outputWord (alphabet := alphabet) (bits.take (2 * inputLength)) inputLength := by
  apply List.ext_getElem
  · simp [outputWord]
  · intro index inLeft inRight
    have indexBound : index < 2 * inputLength := by simpa only [outputWord,DoubleClockReverseCopy.copied_length] using inLeft
    simp only [outputWord] at *
    rw [ElementaryMultiplyOutputData.copied_entry _ _ _ _ indexBound,
      ElementaryMultiplyOutputData.copied_entry _ _ _ _ indexBound]
    have position : (2 : ℤ) * inputLength - 1 - index = ((2 * inputLength - 1 - index : ℕ) : ℤ) := by omega
    rw [position]
    simp only [word]
    have leftCell := ElementaryMultiplyOutputData.accumulator_cell (a := alphabet) bits 0 (2 * inputLength - 1 - index)
    have rightCell := ElementaryMultiplyOutputData.accumulator_cell (a := alphabet) (bits.take (2 * inputLength)) 0
      (2 * inputLength - 1 - index)
    simp only [zero_add] at leftCell rightCell
    rw [leftCell,rightCell,List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]

theorem prefix_value (bits : List Bool) (width : ℕ) (valueFits : Counter.value bits < 2 ^ width) :
    Counter.value (bits.take width) = Counter.value bits := by
  by_cases short : bits.length ≤ width
  · rw [List.take_of_length_le short]
  · have widthFits : width ≤ bits.length := by omega
    have split := Compact.PowerTwo.value_take_add_drop bits width
    rw [List.length_take,Nat.min_eq_left widthFits] at split
    have carryZero : Counter.value (bits.drop width) = 0 := by
      by_contra nonzero
      have atLeastOne : 1 ≤ Counter.value (bits.drop width) := by omega
      have capacityPositive : 0 < 2 ^ width := by positivity
      nlinarith
    simpa only [carryZero,Nat.mul_zero,Nat.add_zero] using split.symm

theorem output_spec (bits : List Bool) (inputLength : ℕ) (valueFits : Counter.value bits < 2 ^ (2 * inputLength)) :
    (outputWord (alphabet := alphabet) bits inputLength).length = 2 * inputLength ∧
      binaryValue (outputWord (alphabet := alphabet) bits inputLength) = Counter.value bits := by
  refine ⟨DoubleClockReverseCopy.copied_length _ _ _,?_⟩
  rw [copied_prefix]
  have copiedValue := ElementaryMultiplyOutputData.copied_accumulator_value (a := alphabet)
    (bits.take (2 * inputLength)) 0 inputLength (by simp)
  simp only [zero_add] at copiedValue
  simpa only [outputWord,word] using copiedValue.trans (prefix_value bits (2 * inputLength) valueFits)

def bank (source clock destination : ℤ → Fin (alphabet+4))
    (sourceHead clockHead destinationHead : ℤ) : Tapes 3 alphabet :=
  ⟨![sourceHead,clockHead,destinationHead],![source,clock,destination]⟩

def clockSlots : Fin (1+2) ≃ Fin 3 where
  toFun := ![1,0,2]
  invFun := ![1,0,2]
  left_inv := by decide
  right_inv := by decide

def program : Program 3 12 alphabet :=
  seq (seq (seq (seq (extend ReturnOrigin.program 2) (extend (DoubleClockReverseCopy.doubleSeekProgram alphabet) 1))
    (reindex (extend ReturnOrigin.program 2) clockSlots))
    (extend (MultiplicationInputSplit.shift .left) 2)) (DoubleClockReverseCopy.reverseCopyProgram alphabet)

def input (bits clock : List Bool) : Tapes 3 alphabet := bank (word bits) (word clock) (fun _ => blank) bits.length 0 0
def output (bits clock : List Bool) : Tapes 3 alphabet :=
  bank (word bits) (word clock) (word (outputWord (alphabet := alphabet) bits clock.length)) (-1) clock.length (2 * clock.length)

private theorem source_bank (source clock destination : ℤ → Fin (alphabet+4))
    (sourceHead clockHead destinationHead : ℤ) :
    ((⟨fun _ => sourceHead,fun _ => source⟩ : Tapes 1 alphabet).append
      (⟨![clockHead,destinationHead],![clock,destination]⟩ : Tapes 2 alphabet)) =
      bank source clock destination sourceHead clockHead destinationHead := by
  unfold Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem seek_bank (source clock destination : ℤ → Fin (alphabet+4))
    (sourceHead clockHead destinationHead : ℤ) :
    ((DoubleClockReverseCopy.seekBank source clock sourceHead clockHead).append
      (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 alphabet)) =
      bank source clock destination sourceHead clockHead destinationHead := by
  unfold DoubleClockReverseCopy.seekBank Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem clock_bank (source clock destination : ℤ → Fin (alphabet+4))
    (sourceHead clockHead destinationHead : ℤ) :
    ((⟨fun _ => clockHead,fun _ => clock⟩ : Tapes 1 alphabet).append
      (⟨![sourceHead,destinationHead],![source,destination]⟩ : Tapes 2 alphabet)).reindex clockSlots =
      bank source clock destination sourceHead clockHead destinationHead := by
  unfold Tapes.append Tapes.reindex clockSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem runs_serialize (bits clock : List Bool) :
    HoareTime (program (alphabet := alphabet)) (· = input bits clock) (· = output bits clock)
      (bits.length + 5 * clock.length + 9) := by
  have returned := FamilyPlacementAlphabet.extend_hoare
    (ReturnOrigin.return_hoare (bits.map (bitSymbol (a := alphabet))) (nonblank _))
    (⟨![0,0],![word clock,fun _ => blank]⟩ : Tapes 2 alphabet)
  simp only [ReturnOrigin.cfg,Config.tapes,List.length_map] at returned
  rw [source_bank,source_bank] at returned
  have sought := FamilyPlacementAlphabet.extend_hoare
    (DoubleClockReverseCopy.doubleSeek_hoare (word bits) (fun _ => blank) 0 0 clock (by rfl))
    (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 1 alphabet)
  simp only [zero_add] at sought
  rw [seek_bank,seek_bank] at sought
  have clockReturned := hoare_place
    (ReturnOrigin.return_hoare (clock.map (bitSymbol (a := alphabet))) (nonblank _)) clockSlots
    (⟨![2 * clock.length,0],![word bits,fun _ => blank]⟩ : Tapes 2 alphabet)
  simp only [ReturnOrigin.cfg,Config.tapes,List.length_map] at clockReturned
  rw [clock_bank,clock_bank] at clockReturned
  have shifted := FamilyPlacementAlphabet.extend_hoare
    (MultiplicationInputSplit.shifts (a := alphabet) .left (word bits) (2 * clock.length))
    (⟨![0,0],![word clock,fun _ => blank]⟩ : Tapes 2 alphabet)
  simp only [Move.offset,Int.add_neg_one] at shifted
  rw [source_bank,source_bank] at shifted
  have copied := DoubleClockReverseCopy.reverseCopy_hoare (a := alphabet) (word bits) (fun _ => blank) (fun _ => blank)
    (2 * clock.length - 1) 0 0 clock (by rfl)
  have endPosition : (2 : ℤ) * clock.length - 1 - 2 * clock.length = -1 := by ring
  simp only [zero_add] at copied
  rw [endPosition] at copied
  apply ((((returned.seq sought).seq clockReturned).seq shifted).seq copied).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

end
end IntegerMultBounds.Machine.RecoverOutputSerialize
