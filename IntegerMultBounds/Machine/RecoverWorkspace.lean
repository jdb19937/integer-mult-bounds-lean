module

public import IntegerMultBounds.Machine.RecoverSignedCoefficient
public import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! Physical cleanup after one signed coefficient. Preserve the emitted chunk
and outgoing carry, erase all five scratch words (including both descriptor
sentinels), and return both width rulers to origin. All complete tapes and heads
are specified; no post-execution cleanliness premise is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverWorkspace
noncomputable section
variable {alphabet : ℕ}
open SharedPlacementAlphabet (setTape)
open RecoverCarryStep (word sumBits)
open RecoverCoefficientRound (roundedBits)
open RecoverPrecisionSplit (fractionBits)

def atProgram {t states : ℕ} (machine : Program 1 states alphabet) (slot : Fin t) :=
  Placement.placed machine (FiniteReturnStackAt.placement slot)

/-- Lift a complete single-tape contract to a selected tape, retaining the
exact entire complementary bank. Shared by every cleanup operation below. -/
theorem runs_one_at {t states cost : ℕ} (machine : Program 1 states alphabet) (slot : Fin t)
    (current : Tapes t alphabet) (before after : ℤ → Fin (alphabet+4)) (beforeHead afterHead : ℤ)
    (headReady : current.head slot = beforeHead) (tapeReady : current.tape slot = before)
    (localRun : HoareTime machine (· = FiniteReturnStack.bank before beforeHead)
      (· = FiniteReturnStack.bank after afterHead) cost) :
    HoareTime (atProgram machine slot) (· = current) (· = setTape current slot after afterHead) cost := by
  have active := FiniteReturnStackAt.active_bank slot current
  rw [headReady,tapeReady] at active
  have placed := Placement.hoare_at localRun (FiniteReturnStackAt.placement slot) current active
  apply placed.consequence (fun _ hypothesis => hypothesis) _ le_rfl
  rintro finalBank ⟨localBank,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank slot current after afterHead

def erased {t : ℕ} (current : Tapes t alphabet) (slot : Fin t) :=
  setTape current slot (fun _ => blank) 0
def restored {t : ℕ} (current : Tapes t alphabet) (slot : Fin t) :=
  setTape current slot (current.tape slot) 0

theorem erase_at {t : ℕ} (slot : Fin t) (current : Tapes t alphabet)
    (symbols : List (Fin (alphabet+4))) (nonblank : ∀ symbol ∈ symbols, symbol ≠ blank)
    (headReady : current.head slot = symbols.length)
    (tapeReady : current.tape slot = putWord (fun _ => blank) 0 symbols) :
    HoareTime (atProgram EraseBack.program slot) (· = current) (· = erased current slot) (symbols.length + 2) := by
  apply runs_one_at EraseBack.program slot current _ _ _ _ headReady tapeReady
  simpa only [EraseBack.cfg,Config.tapes,FiniteReturnStack.bank,zero_add] using
    EraseBack.erase_hoare (fun _ => (blank : Fin (alphabet+4))) 0 symbols nonblank (by rfl) (by intros; rfl)

theorem return_at {t : ℕ} (slot : Fin t) (current : Tapes t alphabet)
    (symbols : List (Fin (alphabet+4))) (nonblank : ∀ symbol ∈ symbols, symbol ≠ blank)
    (headReady : current.head slot = symbols.length)
    (tapeReady : current.tape slot = putWord (fun _ => blank) 0 symbols) :
    HoareTime (atProgram ReturnOrigin.program slot) (· = current) (· = restored current slot) (symbols.length + 2) := by
  have localRun := ReturnOrigin.return_hoare symbols nonblank
  have placed := runs_one_at ReturnOrigin.program slot current _ _ _ _ headReady tapeReady
    (by simpa only [ReturnOrigin.cfg,Config.tapes,FiniteReturnStack.bank] using localRun)
  simpa only [restored,tapeReady] using placed

theorem shift_at {t : ℕ} (slot : Fin t) (current : Tapes t alphabet) (direction : Move) :
    HoareTime (atProgram (MultiplicationInputSplit.shift direction) slot) (· = current)
      (· = setTape current slot (current.tape slot) (current.head slot + direction.offset)) 1 :=
  runs_one_at (MultiplicationInputSplit.shift direction) slot current _ _ _ _ rfl rfl
    (MultiplicationInputSplit.shifts direction (current.tape slot) (current.head slot))

def fractionClear : Program 9 5 alphabet :=
  seq (atProgram (MultiplicationInputSplit.shift .right) (6 : Fin 9))
    (atProgram EraseBack.program (6 : Fin 9))

def program : Program 9 23 alphabet :=
  seq (seq (seq (seq (seq (seq (atProgram EraseBack.program (0 : Fin 9))
    (atProgram EraseBack.program (1 : Fin 9))) (atProgram EraseBack.program (5 : Fin 9)))
    (atProgram EraseBack.program (7 : Fin 9))) fractionClear)
    (atProgram ReturnOrigin.program (2 : Fin 9))) (atProgram ReturnOrigin.program (8 : Fin 9))

def output (lowerBits integerBits carryBits : List Bool) (guard : Bool) (chunkWidth : ℕ) : Tapes 9 alphabet :=
  ⟨![0,0,0,chunkWidth,0,0,0,0,0],
    ![fun _ => blank,fun _ => blank,word (List.replicate chunkWidth true),
      word ((sumBits (roundedBits guard integerBits) carryBits).take chunkWidth),
      word ((sumBits (roundedBits guard integerBits) carryBits).drop chunkWidth),
      fun _ => blank,fun _ => blank,fun _ => blank,
      word (List.replicate (fractionBits lowerBits guard).length true)]⟩

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem descriptor_nonblank (bits : List Bool) :
    ∀ symbol ∈ separator :: bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  rcases List.mem_cons.mp member with rfl | member
  · simp [separator,blank,Fin.ext_iff]
  · exact bits_nonblank bits symbol member

theorem runs_cleanup (signedLowBits : List Bool) (sign : Bool)
    (lowerBits integerBits carryBits : List Bool) (guard : Bool) (chunkWidth : ℕ)
    (layout : RecoverMagnitude.magnitude signedLowBits sign = RecoverPrecisionSplit.sourceBits lowerBits guard integerBits) :
    HoareTime (program (alphabet := alphabet))
      (· = RecoverSignedCoefficient.output signedLowBits sign lowerBits integerBits carryBits guard chunkWidth)
      (· = output lowerBits integerBits carryBits guard chunkWidth)
      (4 * (signedLowBits ++ [sign]).length + carryBits.length + chunkWidth + 28) := by
  let initial := RecoverSignedCoefficient.output (alphabet := alphabet) signedLowBits sign
    lowerBits integerBits carryBits guard chunkWidth
  let stage0 := erased initial (0 : Fin 9)
  let stage1 := erased stage0 (1 : Fin 9)
  let stage2 := erased stage1 (5 : Fin 9)
  let stage3 := erased stage2 (7 : Fin 9)
  let shifted := setTape stage3 (6 : Fin 9) (stage3.tape 6) (stage3.head 6 + Move.right.offset)
  let stage4 := erased shifted (6 : Fin 9)
  let stage5 := restored stage4 (2 : Fin 9)
  let stage6 := restored stage5 (8 : Fin 9)
  have clearCoefficient := erase_at (0 : Fin 9) initial
    ((roundedBits guard integerBits).map bitSymbol) (bits_nonblank _) (by simp only [List.length_map]; rfl) (by rfl)
  have clearSum := erase_at (1 : Fin 9) stage0
    ((sumBits (roundedBits guard integerBits) carryBits).map bitSymbol) (bits_nonblank _)
    (by simp [stage0,erased,setTape,List.length_map]; rfl) (by simp [stage0,erased,setTape]; rfl)
  have clearInteger := erase_at (5 : Fin 9) stage1
    (separator :: (roundedBits guard integerBits).map bitSymbol) (descriptor_nonblank _)
    (by simp [stage1,stage0,erased,setTape,List.length_map]; change (1 : ℤ) + (roundedBits guard integerBits).length = _; omega)
    (by simp [stage1,stage0,erased,setTape]; exact RecoverPrecisionSplit.descriptor_word _)
  have clearSource := erase_at (7 : Fin 9) stage2
    ((RecoverMagnitude.magnitude signedLowBits sign).map bitSymbol) (bits_nonblank _)
    (by simp [stage2,stage1,stage0,erased,setTape,List.length_map]; rfl)
    (by simp [stage2,stage1,stage0,erased,setTape]; rfl)
  have shiftFraction := shift_at (6 : Fin 9) stage3 .right
  have clearFraction := erase_at (6 : Fin 9) shifted
    (separator :: (fractionBits lowerBits guard).map bitSymbol) (descriptor_nonblank _)
    (by simp [shifted,stage3,stage2,stage1,stage0,erased,setTape,Move.offset,List.length_map]; rfl)
    (by simp [shifted,stage3,stage2,stage1,stage0,erased,setTape]; exact RecoverPrecisionSplit.descriptor_word _)
  have returnChunkRuler := return_at (2 : Fin 9) stage4
    ((List.replicate chunkWidth true).map bitSymbol) (bits_nonblank _)
    (by simp [stage4,shifted,stage3,stage2,stage1,stage0,erased,setTape]; rfl)
    (by simp [stage4,shifted,stage3,stage2,stage1,stage0,erased,setTape]
        change word (List.replicate chunkWidth true) = _
        simp [word])
  have returnPrecisionRuler := return_at (8 : Fin 9) stage5
    ((List.replicate (fractionBits lowerBits guard).length true).map bitSymbol) (bits_nonblank _)
    (by simp [stage5,restored,stage4,shifted,stage3,stage2,stage1,stage0,erased,setTape]; rfl)
    (by simp [stage5,restored,stage4,shifted,stage3,stage2,stage1,stage0,erased,setTape]
        change word (List.replicate (fractionBits lowerBits guard).length true) = _
        simp [word])
  have endpoint : stage6 = output (alphabet := alphabet) lowerBits integerBits carryBits guard chunkWidth := by
    unfold stage6 stage5 stage4 shifted stage3 stage2 stage1 stage0 restored erased setTape initial
      RecoverSignedCoefficient.output RecoverCoefficientStep.output RecoverCoefficientStep.bank
      RecoverCoefficientStep.descriptorBank RecoverCarryStep.completeOutput RecoverCarryStep.bank
      Copy.tapes Copy.cfg Config.tapes Tapes.append output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have executed := ((((((clearCoefficient.seq clearSum).seq clearInteger).seq clearSource).seq
    (shiftFraction.seq clearFraction)).seq returnChunkRuler).seq returnPrecisionRuler)
  apply executed.consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis.trans endpoint)
  have roundedWidth := (RecoverCoefficientStep.rounded_length guard integerBits).2
  have sumWidth := BinaryAccumulate.sumWord_length_le (roundedBits guard integerBits) carryBits
  have magnitudeWidth := RecoverMagnitude.magnitude_length signedLowBits sign
  have widths : (signedLowBits ++ [sign]).length = (fractionBits lowerBits guard).length + integerBits.length := by
    rw [← RecoverMagnitude.magnitude_length signedLowBits sign,layout]
    simp [RecoverPrecisionSplit.sourceBits]
  simp only [List.length_map,List.length_cons,List.length_replicate]
  dsimp only [sumBits,BinaryAccumulate.width] at *
  omega

end
end IntegerMultBounds.Machine.RecoverWorkspace
