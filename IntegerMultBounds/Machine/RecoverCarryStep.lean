module

public import IntegerMultBounds.Machine.BinaryAccumulate
public import IntegerMultBounds.Machine.RulerCopy
public import IntegerMultBounds.Machine.ReturnOrigin
public import IntegerMultBounds.Machine.ExactFrame
public import IntegerMultBounds.Machine.Copy
public import IntegerMultBounds.Machine.FamilyPlacementAlphabet
public import IntegerMultBounds.Compact.PowerTwoDigits

/-! One physical section 8 carry step. Add the incoming carry to a recovered
coefficient, rewind the resulting word, and emit its low chunk using a retained
width ruler. The sum head is left at the high suffix representing the outgoing
carry. The complete step additionally exports and rewinds that carry on a fifth
tape. Array iteration and final workspace cleanup are separate obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverCarryStep
variable {alphabet : ℕ}

def word (bits : List Bool) : ℤ → Fin (alphabet+4) :=
  putWord (fun _ => blank) 0 (bits.map bitSymbol)

def bank (coefficient sum ruler digit : ℤ → Fin (alphabet+4))
    (coefficientHead sumHead rulerHead digitHead : ℤ) : Tapes 4 alphabet :=
  ⟨![coefficientHead,sumHead,rulerHead,digitHead],![coefficient,sum,ruler,digit]⟩

def sumBits (coefficientBits carryBits : List Bool) :=
  BinaryAccumulate.sumWord coefficientBits carryBits

def input (coefficientBits carryBits : List Bool) (chunkWidth : ℕ) : Tapes 4 alphabet :=
  bank (word coefficientBits) (word carryBits) (word (List.replicate chunkWidth true))
    (fun _ => blank) 0 0 0 0

def output (coefficientBits carryBits : List Bool) (chunkWidth : ℕ) : Tapes 4 alphabet :=
  bank (word coefficientBits) (word (sumBits coefficientBits carryBits))
    (word (List.replicate chunkWidth true))
    (word ((sumBits coefficientBits carryBits).take chunkWidth))
    coefficientBits.length chunkWidth chunkWidth chunkWidth

def rewindSlots : Fin (1+3) ≃ Fin 4 where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by decide
  right_inv := by decide

def copySlots : Fin (3+1) ≃ Fin 4 where
  toFun := ![2,1,3,0]
  invFun := ![3,1,0,2]
  left_inv := by decide
  right_inv := by decide

def program : Program 4 7 alphabet :=
  seq (seq (extend (BinaryAccumulate.program alphabet) 2)
    (reindex (extend ReturnOrigin.program 3) rewindSlots))
    (reindex (extend RulerCopy.program 1) copySlots)

private theorem accumulate_bank (coefficient sum ruler digit : ℤ → Fin (alphabet+4))
    (coefficientHead sumHead rulerHead digitHead : ℤ) :
    (BinaryAccumulate.cfg coefficient sum coefficientHead sumHead 0).tapes.append
      (⟨![rulerHead,digitHead],![ruler,digit]⟩ : Tapes 2 alphabet) =
      bank coefficient sum ruler digit coefficientHead sumHead rulerHead digitHead := by
  unfold BinaryAccumulate.cfg Config.tapes Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem rewind_bank (coefficient sum ruler digit : ℤ → Fin (alphabet+4))
    (coefficientHead sumHead rulerHead digitHead : ℤ) (state : Fin 3) :
    ((ReturnOrigin.cfg sum sumHead state).tapes.append
      (⟨![coefficientHead,rulerHead,digitHead],![coefficient,ruler,digit]⟩ : Tapes 3 alphabet)).reindex rewindSlots =
      bank coefficient sum ruler digit coefficientHead sumHead rulerHead digitHead := by
  unfold ReturnOrigin.cfg Config.tapes Tapes.append Tapes.reindex rewindSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem copy_bank (coefficient sum ruler digit : ℤ → Fin (alphabet+4))
    (coefficientHead sumHead rulerHead digitHead : ℤ) :
    ((RulerCopy.cfg ruler sum digit rulerHead sumHead digitHead).tapes.append
      (⟨fun _ => coefficientHead,fun _ => coefficient⟩ : Tapes 1 alphabet)).reindex copySlots =
      bank coefficient sum ruler digit coefficientHead sumHead rulerHead digitHead := by
  unfold RulerCopy.cfg Config.tapes Tapes.append Tapes.reindex copySlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem copied_chunk (bits : List Bool) (chunkWidth : ℕ) (widthFits : chunkWidth ≤ bits.length) :
    CopyCells.cells (word (alphabet := alphabet) bits) 0 chunkWidth =
      (bits.take chunkWidth).map bitSymbol := by
  have prefixLength : (bits.take chunkWidth).length = chunkWidth := by simp [widthFits]
  have splitWord : word (alphabet := alphabet) bits =
      putWord (putWord (fun _ => blank) chunkWidth ((bits.drop chunkWidth).map bitSymbol))
        0 ((bits.take chunkWidth).map bitSymbol) := by
    conv_lhs => rw [word,← List.take_append_drop chunkWidth bits,List.map_append]
    rw [putWord_append,List.length_map,prefixLength,zero_add]
  rw [splitWord]
  simpa only [prefixLength] using CopyCells.cells_putWord
    (putWord (fun _ => (blank : Fin (alphabet+4))) chunkWidth ((bits.drop chunkWidth).map bitSymbol))
    0 (bits.take chunkWidth)

/-- A fixed seven-state machine executes addition, the real rewind, and the
low-chunk copy. Padded binary inputs allow zero coefficients and zero carries. -/
theorem runs_step (coefficientBits carryBits : List Bool) (chunkWidth : ℕ)
    (widthFits : chunkWidth ≤ (sumBits coefficientBits carryBits).length) :
    HoareTime (program (alphabet := alphabet)) (· = input coefficientBits carryBits chunkWidth)
      (· = output coefficientBits carryBits chunkWidth)
      (2 * max coefficientBits.length carryBits.length + chunkWidth + 6) := by
  have added := (BinaryAccumulate.accumulate_hoare coefficientBits carryBits
    (fun _ => (blank : Fin (alphabet+4))) (fun _ => blank) 0 0 (by rfl) (by intros; rfl)).extend
      (⟨![0,0],![word (List.replicate chunkWidth true),fun _ => blank]⟩ : Tapes 2 alphabet)
  have addedExact := added.consequence
    (pre' := fun current => current = input coefficientBits carryBits chunkWidth)
    (post' := fun current => current = bank (word coefficientBits) (word (sumBits coefficientBits carryBits))
      (word (List.replicate chunkWidth true)) (fun _ => blank) coefficientBits.length
      (sumBits coefficientBits carryBits).length 0 0)
    (by intro current equal; exact ⟨_,rfl,by simpa only [accumulate_bank,word,zero_add,input] using equal⟩)
    (by rintro current ⟨localBank,rfl,rfl⟩; simp only [accumulate_bank,word,sumBits,zero_add]) le_rfl
  have rewound := hoare_place (ReturnOrigin.return_hoare
    ((sumBits coefficientBits carryBits).map (bitSymbol (a := alphabet))) (bits_nonblank _)) rewindSlots
    (⟨![coefficientBits.length,0,0],![word coefficientBits,word (List.replicate chunkWidth true),fun _ => blank]⟩ : Tapes 3 alphabet)
  simp only [List.length_map] at rewound
  rw [rewind_bank,rewind_bank] at rewound
  have copied := hoare_place (RulerCopy.copy_hoare (fun _ => (blank : Fin (alphabet+4)))
    (word (sumBits coefficientBits carryBits)) (fun _ => blank) 0 0 0
    ((List.replicate chunkWidth true).map bitSymbol) (bits_nonblank _) (by rfl)) copySlots
    (⟨fun _ => coefficientBits.length,fun _ => word coefficientBits⟩ : Tapes 1 alphabet)
  simp only [List.length_map,List.length_replicate,zero_add] at copied
  rw [copy_bank,copy_bank,copied_chunk _ _ widthFits] at copied
  apply ((addedExact.seq rewound).seq copied).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis) ?_
  have sumWidth := BinaryAccumulate.sumWord_length_le coefficientBits carryBits
  change max coefficientBits.length carryBits.length + 1 + 1 +
    ((sumBits coefficientBits carryBits).length + 2) + 1 + chunkWidth ≤ _
  dsimp only [sumBits,BinaryAccumulate.width] at *
  omega

/-- The emitted chunk and the high suffix have exactly the remainder and
quotient required by the list-level carry recurrence. -/
theorem step_values (coefficientBits carryBits : List Bool) (chunkWidth : ℕ)
    (widthFits : chunkWidth ≤ (sumBits coefficientBits carryBits).length) :
    Counter.value ((sumBits coefficientBits carryBits).take chunkWidth) =
      (Counter.value coefficientBits + Counter.value carryBits) % 2 ^ chunkWidth ∧
    Counter.value ((sumBits coefficientBits carryBits).drop chunkWidth) =
      (Counter.value coefficientBits + Counter.value carryBits) / 2 ^ chunkWidth := by
  have split := Compact.PowerTwo.value_take_add_drop (sumBits coefficientBits carryBits) chunkWidth
  have lowBound := Counter.value_lt ((sumBits coefficientBits carryBits).take chunkWidth)
  rw [List.length_take,Nat.min_eq_left widthFits] at lowBound
  rw [List.length_take,Nat.min_eq_left widthFits] at split
  have sumValue : Counter.value (sumBits coefficientBits carryBits) =
      Counter.value coefficientBits + Counter.value carryBits := BinaryAccumulate.sumWord_value _ _
  rw [sumValue] at split
  constructor
  · rw [split,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lowBound]
  · rw [split,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt lowBound,zero_add]

/-- Copy the outgoing carry to reusable blank storage, then physically rewind
that new word. This control is independent of the chunk width and sum width. -/
def exportProgram : Program 2 4 alphabet :=
  seq (Copy.program blank false)
    (reindex (extend ReturnOrigin.program 1) (Equiv.swap 0 1))

private theorem export_rewind_bank (source destination : ℤ → Fin (alphabet+4))
    (sourceHead destinationHead : ℤ) (state : Fin 3) :
    ((ReturnOrigin.cfg destination destinationHead state).tapes.append
      (⟨fun _ => sourceHead,fun _ => source⟩ : Tapes 1 alphabet)).reindex (Equiv.swap 0 1) =
      Copy.tapes source destination sourceHead destinationHead := by
  unfold ReturnOrigin.cfg Config.tapes Tapes.append Tapes.reindex Copy.tapes Copy.cfg
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_export (bits : List Bool) (chunkWidth : ℕ) (widthFits : chunkWidth ≤ bits.length) :
    HoareTime (exportProgram (alphabet := alphabet))
      (· = Copy.tapes (word bits) (fun _ => blank) chunkWidth 0)
      (· = Copy.tapes (word bits) (word (bits.drop chunkWidth)) bits.length 0)
      (2 * (bits.length - chunkWidth) + 3) := by
  have prefixLength : (bits.take chunkWidth).length = chunkWidth := by simp [widthFits]
  have splitWord : putWord (word (alphabet := alphabet) (bits.take chunkWidth)) chunkWidth
      ((bits.drop chunkWidth).map bitSymbol) = word bits := by
    unfold word
    have joined := putWord_append_forward (fun _ => (blank : Fin (alphabet+4))) 0
      ((bits.take chunkWidth).map bitSymbol) ((bits.drop chunkWidth).map bitSymbol)
    simpa only [List.length_map,prefixLength,zero_add,← List.map_append,List.take_append_drop] using joined
  have copied := Copy.copy_hoare (a := alphabet) blank false (word (bits.take chunkWidth))
    (fun _ => blank) chunkWidth 0 ((bits.drop chunkWidth).map bitSymbol)
    (bits_nonblank _) (by
      unfold word
      rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map,prefixLength]; omega))])
  simp only [List.map_map,Copy.retained,Bool.false_eq_true,ite_false,Function.comp_def,List.length_map,zero_add,
    List.length_drop] at copied
  rw [splitWord] at copied
  have sourceEnd : (chunkWidth : ℤ) + (bits.length - chunkWidth : ℕ) = bits.length := by omega
  rw [sourceEnd] at copied
  have rewound := hoare_place (ReturnOrigin.return_hoare
    ((bits.drop chunkWidth).map (bitSymbol (a := alphabet))) (bits_nonblank _))
    (Equiv.swap 0 1) (⟨fun _ => bits.length,fun _ => word bits⟩ : Tapes 1 alphabet)
  simp only [List.length_map,List.length_drop] at rewound
  rw [export_rewind_bank,export_rewind_bank] at rewound
  apply (copied.seq rewound).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis)
  omega

def exportSlots : Fin (2+3) ≃ Fin 5 where
  toFun := ![1,4,0,2,3]
  invFun := ![2,0,3,4,1]
  left_inv := by decide
  right_inv := by decide

def completeProgram : Program 5 11 alphabet :=
  seq (extend program 1) (reindex (extend exportProgram 3) exportSlots)

def completeInput (coefficientBits carryBits : List Bool) (chunkWidth : ℕ) :=
  (input (alphabet := alphabet) coefficientBits carryBits chunkWidth).append
    (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 1 alphabet)

def completeOutput (coefficientBits carryBits : List Bool) (chunkWidth : ℕ) :=
  (bank (word coefficientBits) (word (sumBits coefficientBits carryBits))
    (word (List.replicate chunkWidth true))
    (word ((sumBits coefficientBits carryBits).take chunkWidth)) coefficientBits.length
    (sumBits coefficientBits carryBits).length chunkWidth chunkWidth).append
    (⟨fun _ => 0,fun _ => word ((sumBits coefficientBits carryBits).drop chunkWidth)⟩ : Tapes 1 alphabet)

private theorem export_bank (coefficient sum ruler digit carry : ℤ → Fin (alphabet+4))
    (coefficientHead sumHead rulerHead digitHead carryHead : ℤ) :
    ((Copy.tapes sum carry sumHead carryHead).append
      (⟨![coefficientHead,rulerHead,digitHead],![coefficient,ruler,digit]⟩ : Tapes 3 alphabet)).reindex exportSlots =
      (bank coefficient sum ruler digit coefficientHead sumHead rulerHead digitHead).append
        (⟨fun _ => carryHead,fun _ => carry⟩ : Tapes 1 alphabet) := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex exportSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- Actual chunk emission and an outgoing carry ready at its origin. The
coefficient, width ruler, and whole resulting tapes are specified exactly. -/
theorem runs_complete_step (coefficientBits carryBits : List Bool) (chunkWidth : ℕ)
    (widthFits : chunkWidth ≤ (sumBits coefficientBits carryBits).length) :
    HoareTime (completeProgram (alphabet := alphabet))
      (· = completeInput coefficientBits carryBits chunkWidth)
      (· = completeOutput coefficientBits carryBits chunkWidth)
      (4 * max coefficientBits.length carryBits.length + chunkWidth + 12) := by
  have emitted := FamilyPlacementAlphabet.extend_hoare
    (runs_step (alphabet := alphabet) coefficientBits carryBits chunkWidth widthFits)
    (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 1 alphabet)
  have exported := hoare_place
    (runs_export (alphabet := alphabet) (sumBits coefficientBits carryBits) chunkWidth widthFits)
    exportSlots (⟨![coefficientBits.length,chunkWidth,chunkWidth],
      ![word coefficientBits,word (List.replicate chunkWidth true),
        word ((sumBits coefficientBits carryBits).take chunkWidth)]⟩ : Tapes 3 alphabet)
  rw [export_bank,export_bank] at exported
  apply (emitted.seq exported).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis)
  have sumWidth := BinaryAccumulate.sumWord_length_le coefficientBits carryBits
  dsimp only [sumBits,BinaryAccumulate.width] at *
  omega

/-- A fixed-width coefficient representation supplies sufficient low bits,
including an all-zero coefficient; no lower bound on its value is required. -/
theorem runs_complete_step_of_width (coefficientBits carryBits : List Bool) (chunkWidth : ℕ)
    (coefficientWidth : chunkWidth ≤ coefficientBits.length) :
    HoareTime (completeProgram (alphabet := alphabet))
      (· = completeInput coefficientBits carryBits chunkWidth)
      (· = completeOutput coefficientBits carryBits chunkWidth)
      (4 * max coefficientBits.length carryBits.length + chunkWidth + 12) := by
  apply runs_complete_step
  have sumWidth := BinaryAccumulate.sumWord_length_ge coefficientBits carryBits
  dsimp only [sumBits,BinaryAccumulate.width] at *
  omega

/-- Positive-width chunk emission prevents carry words from growing across
records. Padded high zeroes are harmless, so the array loop need not canonicalize
the outgoing carry after every coefficient. -/
theorem outgoing_width (coefficientBits carryBits : List Bool) (chunkWidth wordWidth : ℕ)
    (chunkPositive : 0 < chunkWidth) (coefficientWidth : coefficientBits.length ≤ wordWidth)
    (carryWidth : carryBits.length ≤ wordWidth) :
    ((sumBits coefficientBits carryBits).drop chunkWidth).length ≤ wordWidth := by
  have sumWidth := BinaryAccumulate.sumWord_length_le coefficientBits carryBits
  simp only [List.length_drop]
  dsimp only [sumBits,BinaryAccumulate.width] at *
  omega

/-- Uniform per-record execution bound on the recurring carry-width invariant. -/
theorem runs_complete_step_uniform (coefficientBits carryBits : List Bool) (chunkWidth wordWidth : ℕ)
    (chunkFits : chunkWidth ≤ coefficientBits.length)
    (coefficientWidth : coefficientBits.length ≤ wordWidth) (carryWidth : carryBits.length ≤ wordWidth) :
    HoareTime (completeProgram (alphabet := alphabet))
      (· = completeInput coefficientBits carryBits chunkWidth)
      (· = completeOutput coefficientBits carryBits chunkWidth)
      (4 * wordWidth + chunkWidth + 12) := by
  apply (runs_complete_step_of_width coefficientBits carryBits chunkWidth chunkFits).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

end IntegerMultBounds.Machine.RecoverCarryStep
