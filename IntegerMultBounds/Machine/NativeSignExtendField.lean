module

public import IntegerMultBounds.Machine.NativeSignExtend
public import IntegerMultBounds.Machine.LayerNativeRecords
public import IntegerMultBounds.Machine.TwoTapeAt

@[expose] public section
namespace IntegerMultBounds.Machine.NativeSignExtendField
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram erased restored)

def wideningMap : Fin 3 → Fin 5 := ![0,3,4]
theorem wideningMap_injective : Function.Injective wideningMap := by decide
def wideningSlots := InjectivePlacement.placement wideningMap wideningMap_injective (by decide : 3+2=5)

def readProgram : Program 5 6 2 := seq (seq (TwoTapeAt.program (Copy.program separator false) (1 : Fin 5) 3 (by decide))
  (atProgram (MultiplicationInputSplit.shift .right) (1 : Fin 5)))
  (atProgram ReturnOrigin.program (3 : Fin 5))
def emitProgram : Program 5 8 2 := seq (seq (seq (TwoTapeAt.program (Copy.program blank false) (4 : Fin 5) 2 (by decide))
  (atProgram EraseBack.program (4 : Fin 5))) (atProgram (WriteSymbol.program separator) (2 : Fin 5)))
  (atProgram (MultiplicationInputSplit.shift .right) (2 : Fin 5))
def program := seq (seq (seq readProgram (Placement.placed NativeSignExtend.program wideningSlots)) emitProgram)
  (atProgram RecoverArrayCleanup.eraseOrigin (3 : Fin 5))

def output (caller : Tapes 5 2) (source : List (Fin 2)) (targetWidth : ℕ) :=
  setTape (setTape caller (1 : Fin 5) (caller.tape 1) (caller.head 1+source.length+1)) (2 : Fin 5)
    (putWord (caller.tape 2) (caller.head 2) (DelimitedRadixRecord.field (NativeSignExtend.extended source targetWidth)))
    (caller.head 2+targetWidth+1)

theorem digits_nonblank (source : List (Fin 2)) :
    ∀ symbol ∈ source.map RadixDigits.digitSymbol, symbol ≠ (blank : Fin 6) := by
  intro symbol member
  obtain ⟨digit, _, rfl⟩ := List.mem_map.mp member
  intro equal
  have values := congrArg Fin.val equal
  change digit.val+4=0 at values
  omega

theorem runs (caller : Tapes 5 2) (source : List (Fin 2)) (targetWidth : ℕ)
    (sourceFits : source.length ≤ targetWidth)
    (background : ℤ → Fin 6)
    (sourceReady : caller.tape 1 = putWord background (caller.head 1) (source.map RadixDigits.digitSymbol))
    (delimiterReady : background (caller.head 1+source.length) = separator)
    (rulerReady : caller.tape 0 = RecoverCarryStep.word (List.replicate targetWidth true))
    (rulerHead : caller.head 0 = 0)
    (sourceWorkBlank : caller.head 3 = 0 ∧ caller.tape 3 = (fun _ => blank))
    (destinationWorkBlank : caller.head 4 = 0 ∧ caller.tape 4 = (fun _ => blank)) :
    HoareTime program (· = caller) (· = output caller source targetWidth) (9*targetWidth+5*source.length+39) := by
  let copied := TwoTapeAt.result caller (1 : Fin 5) 3 (caller.tape 1) (NativeSignExtend.nativeTape source)
    (caller.head 1+source.length) source.length
  let advanced := setTape copied (1 : Fin 5) (caller.tape 1) (caller.head 1+source.length+1)
  let read := restored advanced (3 : Fin 5)
  let widened := setTape read (4 : Fin 5) (NativeSignExtend.nativeTape (NativeSignExtend.extended source targetWidth)) 0
  let resultDigits := NativeSignExtend.extended source targetWidth
  let resultWord := resultDigits.map RadixDigits.digitSymbol
  let copiedResult := TwoTapeAt.result widened (4 : Fin 5) 2 (NativeSignExtend.nativeTape resultDigits)
    (putWord (caller.tape 2) (caller.head 2) resultWord) targetWidth (caller.head 2+targetWidth)
  let clearedResult := erased copiedResult (4 : Fin 5)
  let delimited := setTape clearedResult (2 : Fin 5)
    (Function.update (putWord (caller.tape 2) (caller.head 2) resultWord) (caller.head 2+targetWidth) separator)
    (caller.head 2+targetWidth)
  let emitted := setTape delimited (2 : Fin 5) (delimited.tape 2) (caller.head 2+targetWidth+1)
  have resultLength := NativeSignExtend.extended_length source targetWidth sourceFits
  have copyLocal := Copy.copy_hoare (separator : Fin 6) false background (fun _ => blank)
    (caller.head 1) 0 (source.map RadixDigits.digitSymbol)
    (by intro symbol member; obtain ⟨digit, _, rfl⟩ := List.mem_map.mp member; exact DelimitedRadixRecord.digit_ne_separator digit)
    (by simpa using delimiterReady)
  simp only [Copy.retained, Bool.false_eq_true, ite_false, List.map_map,
    Function.comp_def, List.length_map, zero_add] at copyLocal
  have copyRun := TwoTapeAt.runs (Copy.program separator false) (1 : Fin 5) 3 (by decide) caller
    _ _ _ _ _ _ _ _ ⟨sourceReady, rfl⟩ ⟨sourceWorkBlank.2, sourceWorkBlank.1⟩ copyLocal
  rw [←sourceReady] at copyRun
  have advanceRun := RecoverWorkspace.shift_at (1 : Fin 5) copied .right
  simp only [copied, TwoTapeAt.result, setTape, Function.update_of_ne (by decide : (1 : Fin 5) ≠ 3),
    Function.update_self, Move.offset] at advanceRun
  have returnRun := RecoverWorkspace.return_at (3 : Fin 5) advanced (source.map RadixDigits.digitSymbol)
    (digits_nonblank source) (by simp [advanced, copied, TwoTapeAt.result, setTape])
    (by simp [advanced, copied, TwoTapeAt.result, setTape, NativeSignExtend.nativeTape])
  have readExact : HoareTime readProgram (· = caller) (· = read) (2*source.length+5) := by
    apply ((copyRun.seq advanceRun).seq returnRun).consequence (fun _ ready => ready) (fun _ ready => ready) ?_
    simp only [List.length_map]
    omega
  have wideningReady : Placement.active wideningSlots read = NativeSignExtend.input source targetWidth := by
    rw [wideningSlots, InjectivePlacement.active_bank]
    unfold wideningMap read restored advanced copied TwoTapeAt.result setTape NativeSignExtend.input
      ChirpSignExtend.bank RulerCopy.cfg Config.tapes
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [rulerReady, rulerHead, destinationWorkBlank]
  have wideningEndpoint : Placement.replace wideningSlots read (NativeSignExtend.output source targetWidth) = widened := by
    apply InjectivePlacement.replace_eq wideningMap wideningMap_injective (by decide : 3+2=5) read widened
    · rw [InjectivePlacement.active_bank]
      unfold wideningMap widened read restored advanced copied TwoTapeAt.result setTape NativeSignExtend.output
        ChirpSignExtend.bank RulerCopy.cfg Config.tapes
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp [rulerReady, rulerHead]
    · intro slot outside
      have notDestination : slot ≠ 4 := by intro equal; exact outside 2 (by simpa [wideningMap] using equal.symm)
      simp [widened, setTape, notDestination]
  have wideningRun := Placement.hoare_at (NativeSignExtend.runs source targetWidth sourceFits) wideningSlots read wideningReady
  have wideningExact : HoareTime (Placement.placed NativeSignExtend.program wideningSlots)
      (· = read) (· = widened) (7*targetWidth+source.length+17) := by
    apply wideningRun.consequence (fun _ ready => ready) _ le_rfl
    rintro bank ⟨localBank, rfl, ready⟩
    exact ready.trans wideningEndpoint
  have emitLocal := Copy.copy_hoare (blank : Fin 6) false (fun _ => blank) (caller.tape 2) 0 (caller.head 2)
    resultWord (digits_nonblank resultDigits) rfl
  simp only [zero_add] at emitLocal
  have resultDigitsLength : resultDigits.length = targetWidth := resultLength
  have resultWordLength : resultWord.length = targetWidth := by simp [resultWord, resultDigitsLength]
  rw [resultWordLength] at emitLocal
  have emitCopy := TwoTapeAt.runs (Copy.program blank false) (4 : Fin 5) 2 (by decide) widened
    _ _ _ _ _ _ _ _
    (by simp [widened, setTape, NativeSignExtend.nativeTape, resultDigits, resultWord])
    (by simp [widened, read, restored, advanced, copied, TwoTapeAt.result, setTape]) emitLocal
  have retainedWord : resultWord.map (Copy.retained false) = resultWord := by
    change resultWord.map (fun symbol => symbol) = resultWord
    exact List.map_id resultWord
  rw [retainedWord] at emitCopy
  have eraseResult := RecoverWorkspace.erase_at (4 : Fin 5) copiedResult resultWord (digits_nonblank resultDigits)
    (by simp [copiedResult, TwoTapeAt.result, setTape, resultWordLength])
    (by simp [copiedResult, TwoTapeAt.result, setTape, NativeSignExtend.nativeTape, resultWord])
  have writeDelimiter := RecoverWorkspace.runs_one_at (WriteSymbol.program separator) (2 : Fin 5) clearedResult
    _ _ _ _ rfl rfl (by simpa only [WriteSymbol.cfg, Config.tapes, FiniteReturnStack.bank] using
      WriteSymbol.write_hoare separator (clearedResult.tape 2) (clearedResult.head 2))
  have advanceDestination := RecoverWorkspace.shift_at (2 : Fin 5) delimited .right
  have emitExact : HoareTime emitProgram (· = widened) (· = emitted) (2*targetWidth+7) := by
    apply (((emitCopy.seq eraseResult).seq writeDelimiter).seq advanceDestination).consequence
      (fun _ ready => ready) (fun _ ready => ready) ?_
    simp only [resultWordLength]
    omega
  have eraseSource := RecoverArrayCleanup.erase_origin_at (3 : Fin 5) emitted (source.map RadixDigits.digitSymbol)
    (digits_nonblank source)
    (by simp [emitted, delimited, clearedResult, erased, copiedResult, widened, read, restored, advanced, copied, TwoTapeAt.result, setTape])
    (by simp [emitted, delimited, clearedResult, erased, copiedResult, widened, read, restored, advanced, copied, TwoTapeAt.result, setTape,
      NativeSignExtend.nativeTape])
  have published : Function.update (putWord (caller.tape 2) (caller.head 2) resultWord)
      (caller.head 2+targetWidth) separator =
      putWord (caller.tape 2) (caller.head 2) (DelimitedRadixRecord.field resultDigits) := by
    rw [DelimitedRadixRecord.field, ←putWord_append_forward]
    simp only [resultWord, List.length_map, resultDigitsLength, putWord]
  have endpoint : erased emitted (3 : Fin 5) = output caller source targetWidth := by
    unfold emitted delimited clearedResult erased copiedResult widened read restored advanced copied TwoTapeAt.result output
    apply Placement.Tapes.ext'
    all_goals intro slot; fin_cases slot <;> simp [setTape, sourceWorkBlank, destinationWorkBlank]
    exact published
  unfold program
  apply (((readExact.seq wideningExact).seq emitExact).seq eraseSource).consequence
    (fun _ ready => ready) (fun _ ready => ready.trans endpoint) ?_
  simp only [List.length_map]
  omega

end
end IntegerMultBounds.Machine.NativeSignExtendField
