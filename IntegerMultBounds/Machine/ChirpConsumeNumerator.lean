module

public import IntegerMultBounds.Machine.ChirpExactProduct
public import IntegerMultBounds.Machine.ChirpTruncate
public import IntegerMultBounds.Machine.GuardedMapCopy

/-! Consume an actual native sum word at cell one and emit its raw LSB bits
at cell zero. Converted writes, complete native-source erasure and both head
returns are physical transitions; signed minima need no extra guard. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpConsumeNumerator
noncomputable section
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)

def source (digits : List (Fin 2)) := MarkedWordCleanup.word (digits.map RadixDigits.digitSymbol)
def destination (digits : List (Fin 2)) : ℤ → Fin 6 := RulerWordMap.word ((ChirpArithmeticCodec.rawBits digits).map bitSymbol)
def bank (source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ) :=
  Copy.tapes source destination sourceHead destinationHead

def live (symbol : Fin 6) : Bool := decide (symbol≠blank)
def startSource := atProgram (MultiplicationInputSplit.shift (a := 2) .right) (0 : Fin 2)
def copy := GuardedMapCopy.program live ChirpPublicDecode.decode
def eraseSource := atProgram (EraseBack.program (a := 2)) (0 : Fin 2)
def returnSource := atProgram (MultiplicationInputSplit.shift (a := 2) .left) (0 : Fin 2)
def returnDestination := atProgram (ReturnOrigin.program (a := 2)) (1 : Fin 2)
def program := seq (seq (seq (seq startSource copy) eraseSource) returnSource) returnDestination

def input (digits : List (Fin 2)) := bank (source digits) (fun _ => blank) 0 0
def output (digits : List (Fin 2)) := bank (fun _ => blank) (destination digits) 0 0

private theorem set_bank (source destination updated : ℤ → Fin 6) (sourceHead destinationHead updatedHead : ℤ) (slot : Fin 2) :
    setTape (bank source destination sourceHead destinationHead) slot updated updatedHead=
      bank (if slot=0 then updated else source) (if slot=1 then updated else destination)
        (if slot=0 then updatedHead else sourceHead) (if slot=1 then updatedHead else destinationHead) := by
  fin_cases slot <;> unfold bank setTape Copy.tapes Copy.cfg Config.tapes
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem nonblank (digits : List (Fin 2)) : ∀ symbol ∈ digits.map RadixDigits.digitSymbol,symbol≠(blank : Fin 6) := by
  intro symbol member
  obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
  fin_cases digit <;> decide

/-- The complete two-tape contract includes genuine source reclamation;
neither a decoded bit word nor a cleanup certificate is supplied. -/
theorem runs (digits : List (Fin 2)) :
    HoareTime program (· = input digits) (· = output digits) (3*digits.length+10) := by
  let native := source digits
  let raw := destination digits
  let symbols := digits.map RadixDigits.digitSymbol
  have advanced := RecoverWorkspace.shift_at (0 : Fin 2) (bank native (fun _ => blank) 0 0) .right
  have copied := GuardedMapCopy.copy_hoare live ChirpPublicDecode.decode (fun _ => (blank : Fin 6))
    (fun _ => blank) 1 0 symbols (by
      intro symbol member
      exact decide_eq_true (nonblank digits symbol member)) (by decide)
  simp only [symbols,List.length_map,zero_add] at copied
  rw [ChirpArithmeticCodec.decoded] at copied
  have erasedLocal : HoareTime (EraseBack.program (a := 2))
      (· = FiniteReturnStack.bank native (1+digits.length)) (· = FiniteReturnStack.bank (fun _ => blank) 1) (digits.length+2) := by
    simpa [native,source,symbols,MarkedWordCleanup.word,EraseBack.cfg,Config.tapes,FiniteReturnStack.bank]
      using EraseBack.erase_hoare (fun _ => (blank : Fin 6)) 1 symbols (nonblank digits) rfl (by intro index bound; rfl)
  have erased := RecoverWorkspace.runs_one_at (EraseBack.program (a := 2)) (0 : Fin 2)
    (bank native raw (1+digits.length) digits.length) native (fun _ => blank) (1+digits.length) 1 rfl rfl erasedLocal
  have sourceReturned := RecoverWorkspace.shift_at (0 : Fin 2) (bank (fun _ => (blank : Fin 6)) raw 1 digits.length) .left
  have rawNonblank : ∀ symbol ∈ (ChirpArithmeticCodec.rawBits digits).map (bitSymbol (a := 2)),symbol≠blank := by
    intro symbol member
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
    cases bit <;> decide
  have destinationReturned := RecoverWorkspace.return_at (1 : Fin 2) (bank (fun _ => (blank : Fin 6)) raw 0 digits.length)
    ((ChirpArithmeticCodec.rawBits digits).map bitSymbol) rawNonblank
    (by simp [bank,Copy.tapes,Copy.cfg,Config.tapes,ChirpArithmeticCodec.rawBits]) rfl
  simp only [RecoverWorkspace.restored,set_bank,Move.offset] at advanced erased sourceReturned destinationReturned
  simp [bank,Copy.tapes,Copy.cfg,Config.tapes] at advanced erased sourceReturned destinationReturned
  simp only [List.length_map,ChirpArithmeticCodec.rawBits] at destinationReturned
  unfold program input output startSource copy eraseSource returnSource returnDestination
  simp only [bank,Copy.tapes,Copy.cfg,Config.tapes,ite_self]
  apply (((advanced.seq copied).seq erased).seq sourceReturned).seq destinationReturned |>.consequence
    (fun _ ready => ready) (fun _ finished => finished) ?_
  omega

theorem raw_signed (digits : List (Fin 2)) (widthPred : ℕ) (wordLength : digits.length=widthPred+1) :
    TwosComplement.signed (ChirpArithmeticCodec.rawBits digits)=ButterflySigned.signedValue widthPred digits :=
  ChirpArithmeticCodec.raw_signed digits widthPred wordLength

end
end IntegerMultBounds.Machine.ChirpConsumeNumerator
