module

public import IntegerMultBounds.Machine.RecoverCoefficientRound
public import IntegerMultBounds.Machine.RecoverCarryStep
public import IntegerMultBounds.Machine.RecoverMagnitude

/-! A literal section 8 coefficient step: round the encoded fractional guard,
copy the rounded descriptor into raw coefficient storage, rewind that storage,
then run the complete chunk/carry machine. All representation conversions and
joins are paid. Signed record decoding and repeated-array control remain open. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverCoefficientStep
variable {alphabet : ℕ}
open RecoverCoefficientRound (roundedBits)
open RecoverCarryStep (word sumBits)

def descriptorBank (integerBits : List Bool) (descriptorHead : ℤ)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ) : Tapes 2 alphabet :=
  Copy.tapes (BinaryDescriptorStack.descriptor integerBits) fractionTape descriptorHead guardHead

def bank (carryBank : Tapes 5 alphabet) (integerBits : List Bool) (descriptorHead : ℤ)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ) :=
  carryBank.append (descriptorBank integerBits descriptorHead fractionTape guardHead)

def unpackProgram : Program 2 4 alphabet :=
  seq (Copy.program blank false)
    (reindex (extend ReturnOrigin.program 1) (Equiv.swap 0 1))

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem unpack_rewind_bank (source destination : ℤ → Fin (alphabet+4))
    (sourceHead destinationHead : ℤ) (state : Fin 3) :
    ((ReturnOrigin.cfg destination destinationHead state).tapes.append
      (⟨fun _ => sourceHead,fun _ => source⟩ : Tapes 1 alphabet)).reindex (Equiv.swap 0 1) =
      Copy.tapes source destination sourceHead destinationHead := by
  unfold ReturnOrigin.cfg Config.tapes Tapes.append Tapes.reindex Copy.tapes Copy.cfg
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- This is a physical representation conversion, not a relabeling of the
rounded output. The descriptor sentinel stays on its source tape. -/
theorem runs_unpack (integerBits : List Bool) :
    HoareTime (unpackProgram (alphabet := alphabet))
      (· = Copy.tapes (BinaryDescriptorStack.descriptor integerBits) (fun _ => blank) 1 0)
      (· = Copy.tapes (BinaryDescriptorStack.descriptor integerBits) (word integerBits)
        (1 + integerBits.length) 0) (2 * integerBits.length + 3) := by
  have copied := Copy.copy_hoare (a := alphabet) blank false BinaryDescriptorStack.empty
    (fun _ => blank) 1 0 (integerBits.map bitSymbol) (bits_nonblank _)
    (by
      simp only [List.length_map,BinaryDescriptorStack.empty]
      split_ifs with markerZero
      · omega
      · rfl)
  have retained : (Copy.retained false : Fin (alphabet+4) → Fin (alphabet+4)) = id := by funext symbol; rfl
  simp only [retained,List.map_id,List.length_map,zero_add] at copied
  have rewound := hoare_place (ReturnOrigin.return_hoare
    (integerBits.map (bitSymbol (a := alphabet))) (bits_nonblank _))
    (Equiv.swap 0 1)
    (⟨fun _ => 1 + integerBits.length,fun _ => BinaryDescriptorStack.descriptor integerBits⟩ : Tapes 1 alphabet)
  simp only [List.length_map] at rewound
  rw [unpack_rewind_bank,unpack_rewind_bank] at rewound
  apply (copied.seq rewound).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis)
  omega

def roundSlots : Fin (2+5) ≃ Fin 7 where
  toFun := ![5,6,0,1,2,3,4]
  invFun := ![2,3,4,5,6,0,1]
  left_inv := by decide
  right_inv := by decide

def unpackSlots : Fin (2+5) ≃ Fin 7 where
  toFun := ![5,0,1,2,3,4,6]
  invFun := ![1,2,3,4,5,0,6]
  left_inv := by decide
  right_inv := by decide

def program : Program 7 20 alphabet :=
  seq (seq (reindex (extend RecoverCoefficientRound.program 5) roundSlots)
    (reindex (extend unpackProgram 5) unpackSlots))
    (extend RecoverCarryStep.completeProgram 2)

def input (integerBits carryBits : List Bool) (chunkWidth : ℕ)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ) :=
  bank (RecoverCarryStep.completeInput [] carryBits chunkWidth) integerBits 1 fractionTape guardHead

def output (guard : Bool) (integerBits carryBits : List Bool) (chunkWidth : ℕ)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ) :=
  bank (RecoverCarryStep.completeOutput (roundedBits guard integerBits) carryBits chunkWidth)
    (roundedBits guard integerBits) (1 + (roundedBits guard integerBits).length) fractionTape guardHead

private theorem round_bank (integerBits : List Bool) (fractionTape : ℤ → Fin (alphabet+4))
    (guardHead : ℤ) (carryBank : Tapes 5 alphabet) :
    ((RecoverCoefficientRound.bank integerBits fractionTape guardHead).append carryBank).reindex roundSlots =
      bank carryBank integerBits 1 fractionTape guardHead := by
  unfold RecoverCoefficientRound.bank BinaryDescriptorIncrement.bank RecoverCoefficientRound.fractionBank
    bank descriptorBank Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex roundSlots
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem unpack_bank (integerBits : List Bool) (coefficient carry ruler digit nextCarry fraction : ℤ → Fin (alphabet+4))
    (descriptorHead coefficientHead carryHead rulerHead digitHead nextCarryHead guardHead : ℤ) :
    ((Copy.tapes (BinaryDescriptorStack.descriptor integerBits) coefficient descriptorHead coefficientHead).append
      (⟨![carryHead,rulerHead,digitHead,nextCarryHead,guardHead],![carry,ruler,digit,nextCarry,fraction]⟩ : Tapes 5 alphabet)).reindex unpackSlots =
      bank ((RecoverCarryStep.bank coefficient carry ruler digit coefficientHead carryHead rulerHead digitHead).append
        (⟨fun _ => nextCarryHead,fun _ => nextCarry⟩ : Tapes 1 alphabet))
        integerBits descriptorHead fraction guardHead := by
  unfold bank descriptorBank Copy.tapes Copy.cfg Config.tapes RecoverCarryStep.bank
    Tapes.append Tapes.reindex unpackSlots
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem rounded_length (guard : Bool) (integerBits : List Bool) :
    integerBits.length ≤ (roundedBits guard integerBits).length ∧
      (roundedBits guard integerBits).length ≤ integerBits.length + 1 := by
  cases guard
  · simp [roundedBits]
  · exact GrowingCounterData.increment_length integerBits

/-- One fixed program rounds, converts, emits a digit and returns a reusable
carry. Arbitrary fractional tapes remain completely unchanged. -/
theorem runs_step (guard : Bool) (integerBits carryBits : List Bool) (chunkWidth : ℕ)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ)
    (guardRead : fractionTape guardHead = bitSymbol guard)
    (coefficientWidth : chunkWidth ≤ integerBits.length) :
    HoareTime program (· = input integerBits carryBits chunkWidth fractionTape guardHead)
      (· = output guard integerBits carryBits chunkWidth fractionTape guardHead)
      (8 * integerBits.length + 4 * carryBits.length + chunkWidth + 26) := by
  have rounded := hoare_place (RecoverCoefficientRound.runs_round guard integerBits fractionTape guardHead guardRead)
    roundSlots (RecoverCarryStep.completeInput [] carryBits chunkWidth)
  rw [round_bank,round_bank] at rounded
  have unpacked := hoare_place (runs_unpack (alphabet := alphabet) (roundedBits guard integerBits))
    unpackSlots (⟨![0,0,0,0,guardHead],![word carryBits,word (List.replicate chunkWidth true),
      fun _ => blank,fun _ => blank,fractionTape]⟩ : Tapes 5 alphabet)
  rw [unpack_bank,unpack_bank] at unpacked
  have capacity : chunkWidth ≤ (roundedBits guard integerBits).length :=
    coefficientWidth.trans (rounded_length guard integerBits).1
  have carried := FamilyPlacementAlphabet.extend_hoare
    (RecoverCarryStep.runs_complete_step_of_width (alphabet := alphabet)
      (roundedBits guard integerBits) carryBits chunkWidth capacity)
    (descriptorBank (roundedBits guard integerBits) (1 + (roundedBits guard integerBits).length) fractionTape guardHead)
  apply ((rounded.seq unpacked).seq carried).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis)
  have roundingCost := RecoverCoefficientRound.cost_linear guard integerBits
  have roundedWidth := (rounded_length guard integerBits).2
  have maxWidth := Nat.max_le.mpr
    ⟨Nat.le_add_right (roundedBits guard integerBits).length carryBits.length,
      Nat.le_add_left carryBits.length (roundedBits guard integerBits).length⟩
  omega

/-- The approximation margin yields the coefficient consumed by this same
round-and-carry execution, without assuming correctness of the rounded word. -/
theorem step_values (integerBits lowerBits carryBits : List Bool) (guard : Bool)
    (coefficient chunkWidth : ℕ) (coefficientWidth : chunkWidth ≤ integerBits.length)
    (approximationClose : |(Counter.value integerBits : ℝ) +
      (Counter.value (lowerBits ++ [guard]) : ℝ) / 2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2) :
    Counter.value ((sumBits (roundedBits guard integerBits) carryBits).take chunkWidth) =
      (coefficient + Counter.value carryBits) % 2 ^ chunkWidth ∧
    Counter.value ((sumBits (roundedBits guard integerBits) carryBits).drop chunkWidth) =
      (coefficient + Counter.value carryBits) / 2 ^ chunkWidth := by
  obtain ⟨fractionNonnegative,fractionBelowOne,guardCorrect⟩ := RecoverCoefficientRound.fractionOf_spec lowerBits guard
  have exactRound : round ((Counter.value integerBits : ℝ) + RecoverCoefficientRound.fractionOf lowerBits guard) =
      (coefficient : ℤ) := by
    apply round_eq_iff.mpr
    rw [RecoverCoefficientRound.fractionOf_value]
    obtain ⟨lowerError,upperError⟩ := abs_lt.mp approximationClose
    simp only [Int.cast_natCast]
    constructor <;> linarith
  have coefficientValue : Counter.value (roundedBits guard integerBits) = coefficient := by
    exact_mod_cast (RecoverCoefficientRound.rounded_eq_round guard integerBits
      (RecoverCoefficientRound.fractionOf lowerBits guard) fractionNonnegative fractionBelowOne guardCorrect).trans exactRound
  have sumWidth := BinaryAccumulate.sumWord_length_ge (roundedBits guard integerBits) carryBits
  have roundedWidth := (rounded_length guard integerBits).1
  have capacity : chunkWidth ≤ (sumBits (roundedBits guard integerBits) carryBits).length := by
    dsimp only [sumBits,BinaryAccumulate.width] at *
    omega
  simpa only [coefficientValue] using RecoverCarryStep.step_values
    (roundedBits guard integerBits) carryBits chunkWidth capacity

theorem runs_recover_step (integerBits lowerBits carryBits : List Bool) (guard : Bool)
    (coefficient chunkWidth : ℕ) (coefficientWidth : chunkWidth ≤ integerBits.length)
    (approximationClose : |(Counter.value integerBits : ℝ) +
      (Counter.value (lowerBits ++ [guard]) : ℝ) / 2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2) :
    HoareTime (program (alphabet := alphabet))
      (· = input integerBits carryBits chunkWidth (BinaryDescriptorStack.descriptor (lowerBits ++ [guard])) (1 + lowerBits.length))
      (fun finalBank => finalBank = output guard integerBits carryBits chunkWidth
        (BinaryDescriptorStack.descriptor (lowerBits ++ [guard])) (1 + lowerBits.length) ∧
        Counter.value ((sumBits (roundedBits guard integerBits) carryBits).take chunkWidth) =
          (coefficient + Counter.value carryBits) % 2 ^ chunkWidth ∧
        Counter.value ((sumBits (roundedBits guard integerBits) carryBits).drop chunkWidth) =
          (coefficient + Counter.value carryBits) / 2 ^ chunkWidth)
      (8 * integerBits.length + 4 * carryBits.length + chunkWidth + 26) := by
  have values := step_values integerBits lowerBits carryBits guard coefficient chunkWidth coefficientWidth approximationClose
  exact (runs_step guard integerBits carryBits chunkWidth _ _
    (RecoverCoefficientRound.fractional_guard_read lowerBits guard) coefficientWidth).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => ⟨hypothesis,values⟩) le_rfl

/-- The same literal rounding/carry program consumes a prepared split of the
signed magnitude. Its error premise refers to the original signed numerator,
including slightly negative approximations of a zero coefficient. Physical
record splitting and connection to `RecoverMagnitude.program` remain upstream. -/
theorem runs_recover_signed_split (signedLowBits : List Bool) (sign : Bool)
    (integerBits lowerBits carryBits : List Bool) (guard : Bool)
    (coefficient chunkWidth : ℕ) (coefficientWidth : chunkWidth ≤ integerBits.length)
    (layout : RecoverMagnitude.magnitude signedLowBits sign = (lowerBits ++ [guard]) ++ integerBits)
    (approximationClose : |(TwosComplement.signed (signedLowBits ++ [sign]) : ℝ) /
      2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2) :
    HoareTime (program (alphabet := alphabet))
      (· = input integerBits carryBits chunkWidth (BinaryDescriptorStack.descriptor (lowerBits ++ [guard])) (1 + lowerBits.length))
      (fun finalBank => finalBank = output guard integerBits carryBits chunkWidth
        (BinaryDescriptorStack.descriptor (lowerBits ++ [guard])) (1 + lowerBits.length) ∧
        Counter.value ((sumBits (roundedBits guard integerBits) carryBits).take chunkWidth) =
          (coefficient + Counter.value carryBits) % 2 ^ chunkWidth ∧
        Counter.value ((sumBits (roundedBits guard integerBits) carryBits).drop chunkWidth) =
          (coefficient + Counter.value carryBits) / 2 ^ chunkWidth)
      (8 * integerBits.length + 4 * carryBits.length + chunkWidth + 26) :=
  runs_recover_step integerBits lowerBits carryBits guard coefficient chunkWidth coefficientWidth
    (RecoverMagnitude.split_magnitude_margin signedLowBits sign lowerBits integerBits guard coefficient layout approximationClose)

end IntegerMultBounds.Machine.RecoverCoefficientStep
