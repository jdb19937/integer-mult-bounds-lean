module

public import IntegerMultBounds.Machine.GuardedMapCopy
public import IntegerMultBounds.Machine.ChirpPublicDecode

/-! Emit one native delimiter-terminated LSB radix-two field in public MSB
Boolean order. Both native boundaries are read physically; no width ruler,
count descriptor or decoded source is supplied. Original cells are retained. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicEmitField
noncomputable section
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)
open ChirpPublicDecode (live decode publicWord)

def scan := atProgram (MultiplicationInputSplit.scan (separator : Fin 6)) (0 : Fin 2)
def shift (direction : Move) := atProgram (MultiplicationInputSplit.shift (a := 2) direction) (0 : Fin 2)
def program := seq (seq (seq (seq (seq scan (shift .left))
  (GuardedMapCopy.reverseProgram live decode)) (shift .right)) scan) (shift .right)

private theorem set_source (source destination updated : ℤ → Fin 6)
    (sourceHead destinationHead updatedHead : ℤ) :
    setTape (Copy.tapes source destination sourceHead destinationHead) (0 : Fin 2) updated updatedHead=
      Copy.tapes updated destination updatedHead destinationHead := by
  unfold setTape Copy.tapes Copy.cfg Config.tapes
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem source_run {states cost : ℕ} (machine : Program 1 states 2)
    (source destination updated : ℤ → Fin 6) (sourceHead destinationHead updatedHead : ℤ)
    (localRun : HoareTime machine (· = FiniteReturnStack.bank source sourceHead)
      (· = FiniteReturnStack.bank updated updatedHead) cost) :
    HoareTime (atProgram machine (0 : Fin 2)) (· = Copy.tapes source destination sourceHead destinationHead)
      (· = Copy.tapes updated destination updatedHead destinationHead) cost := by
  have placed := RecoverWorkspace.runs_one_at machine (0 : Fin 2)
    (Copy.tapes source destination sourceHead destinationHead) source updated sourceHead updatedHead rfl rfl localRun
  rw [set_source] at placed
  exact placed

private theorem scan_field (background destination : ℤ → Fin 6) (origin destinationHead : ℤ)
    (digits : List (Fin 2)) (endSeparator : background (origin+digits.length)=separator) :
    HoareTime scan
      (· = Copy.tapes (putWord background origin (digits.map RadixDigits.digitSymbol)) destination origin destinationHead)
      (· = Copy.tapes (putWord background origin (digits.map RadixDigits.digitSymbol)) destination
        (origin+digits.length) destinationHead) digits.length := by
  have localRun := MultiplicationInputSplit.scan_hoare (a := 2) separator background origin
    (digits.map RadixDigits.digitSymbol) (by
      intro symbol member
      obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
      exact DelimitedRadixRecord.digit_ne_separator digit) (by simpa using endSeparator)
  simp only [List.length_map] at localRun
  exact source_run _ _ _ _ _ _ _ (by
    simpa only [MultiplicationInputSplit.oneCfg,Config.tapes,FiniteReturnStack.bank] using localRun)

private theorem shift_source (direction : Move) (source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ) :
    HoareTime (shift direction) (· = Copy.tapes source destination sourceHead destinationHead)
      (· = Copy.tapes source destination (sourceHead+direction.offset) destinationHead) 1 :=
  source_run _ _ _ _ _ _ _ (MultiplicationInputSplit.shifts direction source sourceHead)

/-- Exact native/public field emission. The preceding stop may be a blank or
native separator, so first and later fields use the same fixed program.
Empty fields are supported and the destination gains no delimiter. -/
theorem runs_field (background destination : ℤ → Fin 6) (origin destinationHead : ℤ) (digits : List (Fin 2))
    (beforeStopped : live (background (origin-1))=false) (endSeparator : background (origin+digits.length)=separator) :
    HoareTime program
      (· = Copy.tapes (putWord background origin (digits.map RadixDigits.digitSymbol)) destination origin destinationHead)
      (· = Copy.tapes (putWord background origin (digits.map RadixDigits.digitSymbol))
        (putWord destination destinationHead ((publicWord digits).map bitSymbol))
        (origin+digits.length+1) (destinationHead+digits.length)) (3*digits.length+8) := by
  let source := putWord background origin (digits.map RadixDigits.digitSymbol)
  let published := putWord destination destinationHead ((publicWord digits).map (bitSymbol (a := 2)))
  have firstScan := scan_field background destination origin destinationHead digits endSeparator
  have firstShift := shift_source .left source destination (origin+digits.length) destinationHead
  simp only [Move.offset,Int.add_neg_one] at firstShift
  have copied := GuardedMapCopy.reverse_hoare live decode background destination origin destinationHead
    (digits.map RadixDigits.digitSymbol) (by
      intro symbol member
      obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
      exact ChirpPublicDecode.live_digit digit) beforeStopped
  simp only [List.length_map] at copied
  rw [ChirpPublicDecode.decoded_symbols digits] at copied
  have returnStart := shift_source .right source published (origin-1) (destinationHead+digits.length)
  simp only [Move.offset,sub_add_cancel] at returnStart
  have secondScan := scan_field background published origin (destinationHead+digits.length) digits endSeparator
  have advanceNext := shift_source .right source published (origin+digits.length) (destinationHead+digits.length)
  simp only [Move.offset] at advanceNext
  unfold program scan shift
  apply (((((firstScan.seq firstShift).seq copied).seq returnStart).seq secondScan).seq advanceNext).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  omega

end
end IntegerMultBounds.Machine.ChirpPublicEmitField
