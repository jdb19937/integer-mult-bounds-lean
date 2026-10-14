module

public import IntegerMultBounds.Machine.RulerMapCopy
public import IntegerMultBounds.Machine.ChirpPublicCodec

/-! One public MSB component field becomes one delimited native LSB radix-two
field. The reusable width ruler discovers the high boundary; mapped backwards
copy converts each bit as it writes. Source cells are retained, the source
cursor advances exactly one field and the ruler returns to origin. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicField
noncomputable section
abbrev alphabet := 2
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)
open RecoverCarryStep (word)

def bank (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ) :=
  (RulerCopy.cfg ruler source destination rulerHead sourceHead destinationHead).tapes

@[simp] private theorem bank_head (ruler source destination : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead destinationHead : ℤ) (slot : Fin 3) :
    (bank ruler source destination rulerHead sourceHead destinationHead).head slot =
      if slot = 0 then rulerHead else if slot = 1 then sourceHead else destinationHead := rfl

@[simp] private theorem bank_tape (ruler source destination : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead destinationHead : ℤ) (slot : Fin 3) :
    (bank ruler source destination rulerHead sourceHead destinationHead).tape slot =
      if slot = 0 then ruler else if slot = 1 then source else destination := rfl

private theorem set_bank (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ)
    (slot : Fin 3) (newTape : ℤ → Fin (alphabet+4)) (newHead : ℤ) :
    setTape (bank ruler source destination rulerHead sourceHead destinationHead) slot newTape newHead =
      bank (if slot = 0 then newTape else ruler) (if slot = 1 then newTape else source)
        (if slot = 2 then newTape else destination)
        (if slot = 0 then newHead else rulerHead) (if slot = 1 then newHead else sourceHead)
        (if slot = 2 then newHead else destinationHead) := by
  unfold setTape bank RulerCopy.cfg Config.tapes
  congr 1
  · funext index; fin_cases slot <;> fin_cases index <;> simp
  · funext index position; fin_cases slot <;> fin_cases index <;> simp

private theorem advance_bank (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ) :
    (RulerAdvance.cfg ruler source rulerHead sourceHead).tapes.append
      (⟨fun _ => destinationHead, fun _ => destination⟩ : Tapes 1 alphabet) =
        bank ruler source destination rulerHead sourceHead destinationHead := by
  unfold Tapes.append bank RulerAdvance.cfg RulerCopy.cfg Config.tapes
  congr 1 <;> apply List.ofFn_injective <;> rfl

def advance : Program 3 1 alphabet := extend RulerAdvance.program 1
def reset : Program 3 3 alphabet := atProgram ReturnOrigin.program (0 : Fin 3)
def sourceShift (direction : Move) : Program 3 2 alphabet :=
  atProgram (MultiplicationInputSplit.shift direction) (1 : Fin 3)
def separatorWrite : Program 3 2 alphabet := atProgram (WriteSymbol.program separator) (2 : Fin 3)
def destinationShift : Program 3 2 alphabet := atProgram (MultiplicationInputSplit.shift .right) (2 : Fin 3)

def program : Program 3 20 alphabet := seq (seq (seq (seq (seq (seq (seq (seq (seq advance reset) (sourceShift .left))
  (RulerMapCopy.reverseProgram ChirpPublicCodec.encode)) reset) (sourceShift .right)) advance) reset) separatorWrite) destinationShift

private theorem ruler_nonblank (rulerBits : List Bool) :
    ∀ symbol ∈ rulerBits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol, blank, Fin.ext_iff]

private theorem reset_hoare (rulerBits : List Bool) (source destination : ℤ → Fin (alphabet+4))
    (sourceHead destinationHead : ℤ) :
    HoareTime reset (· = bank (word rulerBits) source destination rulerBits.length sourceHead destinationHead)
      (· = bank (word rulerBits) source destination 0 sourceHead destinationHead) (rulerBits.length + 2) := by
  have resetRun := RecoverWorkspace.return_at (0 : Fin 3)
    (bank (word rulerBits) source destination rulerBits.length sourceHead destinationHead)
    (rulerBits.map bitSymbol) (ruler_nonblank _) (by simp) rfl
  simpa only [reset, RecoverWorkspace.restored, bank_tape, set_bank, List.length_map, ite_true, show (0 : Fin 3) ≠ 1 by decide,
    show (0 : Fin 3) ≠ 2 by decide, ite_false] using resetRun

private theorem shift_hoare (direction : Move) (ruler source destination : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead destinationHead : ℤ) :
    HoareTime (sourceShift direction) (· = bank ruler source destination rulerHead sourceHead destinationHead)
      (· = bank ruler source destination rulerHead (sourceHead + direction.offset) destinationHead) 1 := by
  have shiftRun := RecoverWorkspace.shift_at (1 : Fin 3)
    (bank ruler source destination rulerHead sourceHead destinationHead) direction
  simpa only [sourceShift, bank_head, bank_tape, set_bank, ite_true,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, ite_false] using shiftRun

/-- Read a public component from any boundary, converting it to a delimited
native field while retaining every adjacent source cell. -/
theorem runs_field (rulerBits field : List Bool) (rulerLength : rulerBits.length = field.length)
    (background destination : ℤ → Fin (alphabet+4)) (origin destinationHead : ℤ) :
    HoareTime program
      (· = bank (word rulerBits) (putWord background origin (field.map bitSymbol)) destination 0 origin destinationHead)
      (· = bank (word rulerBits) (putWord background origin (field.map bitSymbol))
        (putWord destination destinationHead (((field.reverse.map bitSymbol).map ChirpPublicCodec.encode) ++ [separator]))
        0 (origin + field.length) (destinationHead + field.length + 1)) (7 * field.length + 19) := by
  let source := putWord background origin (field.map (bitSymbol (a := alphabet)))
  let reversedDestination := putWord destination destinationHead ((field.reverse.map (bitSymbol (a := alphabet))).map ChirpPublicCodec.encode)
  have advanceRun := FamilyPlacementAlphabet.extend_hoare
    (RulerAdvance.advance_hoare (fun _ => (blank : Fin (alphabet+4))) source 0 origin
      (rulerBits.map bitSymbol) (ruler_nonblank _) rfl)
    (⟨fun _ => destinationHead, fun _ => destination⟩ : Tapes 1 alphabet)
  simp only [List.length_map, zero_add] at advanceRun
  rw [advance_bank, advance_bank, rulerLength] at advanceRun
  have firstReset := reset_hoare rulerBits source destination (origin + field.length) destinationHead
  rw [rulerLength] at firstReset
  have firstShift := shift_hoare .left (word rulerBits) source destination 0 (origin + field.length) destinationHead
  simp only [Move.offset, Int.add_neg_one] at firstShift
  have copyRun := RulerMapCopy.field_hoare ChirpPublicCodec.encode (fun _ => (blank : Fin (alphabet+4))) background destination
    0 origin destinationHead field (rulerBits.map bitSymbol) (by simpa using rulerLength) (ruler_nonblank _) rfl
  simp only [zero_add] at copyRun
  have secondReset := reset_hoare rulerBits source reversedDestination (origin - 1) (destinationHead + field.length)
  rw [rulerLength] at secondReset
  have secondShift := shift_hoare .right (word rulerBits) source reversedDestination 0 (origin - 1) (destinationHead + field.length)
  simp only [Move.offset, sub_add_cancel] at secondShift
  have skipRun := FamilyPlacementAlphabet.extend_hoare
    (RulerAdvance.advance_hoare (fun _ => (blank : Fin (alphabet+4))) source 0 origin
      (rulerBits.map bitSymbol) (ruler_nonblank _) rfl)
    (⟨fun _ => destinationHead+field.length,fun _ => reversedDestination⟩ : Tapes 1 alphabet)
  simp only [List.length_map,zero_add] at skipRun
  rw [advance_bank,advance_bank,rulerLength] at skipRun
  have lastReset := reset_hoare rulerBits source reversedDestination (origin + field.length) (destinationHead + field.length)
  rw [rulerLength] at lastReset
  have writeRun := RecoverWorkspace.runs_one_at (WriteSymbol.program separator) (2 : Fin 3)
    (bank (word rulerBits) source reversedDestination 0 (origin + field.length) (destinationHead + field.length))
    reversedDestination (Function.update reversedDestination (destinationHead + field.length) separator)
    (destinationHead + field.length) (destinationHead + field.length) rfl rfl
    (by simpa only [WriteSymbol.cfg, Config.tapes, FiniteReturnStack.bank] using
      WriteSymbol.write_hoare separator reversedDestination (destinationHead + field.length))
  simp only [set_bank, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false, ite_true] at writeRun
  have published : Function.update reversedDestination (destinationHead + field.length) separator =
      putWord destination destinationHead (((field.reverse.map bitSymbol).map ChirpPublicCodec.encode) ++ [separator]) := by
    rw [← putWord_append_forward]
    simp only [List.length_map, List.length_reverse, putWord]
    rfl
  rw [published] at writeRun
  have destinationRun := RecoverWorkspace.shift_at (2 : Fin 3)
    (bank (word rulerBits) source (putWord destination destinationHead (((field.reverse.map bitSymbol).map ChirpPublicCodec.encode) ++ [separator]))
      0 (origin + field.length) (destinationHead + field.length)) .right
  simp only [bank_head, bank_tape, set_bank, Move.offset,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false, ite_true] at destinationRun
  unfold program advance reset sourceShift separatorWrite destinationShift
  apply (((((((((advanceRun.seq firstReset).seq firstShift).seq copyRun).seq secondReset).seq secondShift).seq skipRun).seq lastReset).seq writeRun).seq destinationRun).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  omega

/-- The actual destination is exactly the native arithmetic field format. -/
theorem runs_native (rulerBits field : List Bool) (rulerLength : rulerBits.length=field.length)
    (background destination : ℤ → Fin 6) (origin destinationHead : ℤ) :
    HoareTime program
      (· = bank (word rulerBits) (putWord background origin (field.map bitSymbol)) destination 0 origin destinationHead)
      (· = bank (word rulerBits) (putWord background origin (field.map bitSymbol))
        (putWord destination destinationHead (DelimitedRadixRecord.field (ChirpPublicCodec.nativeWord field)))
        0 (origin+field.length) (destinationHead+field.length+1)) (7*field.length+19) := by
  simpa only [ChirpPublicCodec.encoded_word,DelimitedRadixRecord.field] using
    runs_field rulerBits field rulerLength background destination origin destinationHead

end
end IntegerMultBounds.Machine.ChirpPublicField
