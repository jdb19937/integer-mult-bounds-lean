module

public import IntegerMultBounds.ExactRecoveryOutput
public import IntegerMultBounds.Machine.WordTapeBridge
public import IntegerMultBounds.Schoenhage.TapeBank
public import IntegerMultBounds.Machine.Copy
public import IntegerMultBounds.Machine.MultiplicationInputSplit
public import IntegerMultBounds.Machine.ExactFrame
public import IntegerMultBounds.Schoenhage.RecoveryCleanupGenerated

/-! The final section 8 installation boundary. The input is an already
recovered MSB word on tape one, in the separator-terminated word format.
Copy only its bits to blank tape zero, move past the source separator, and
run generated cleanup on the source and both arbitrary word-format scratch
tapes. Rounding and carry normalization are separate upstream obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverOutputInstall
open Schoenhage Schoenhage.CertifiedSequence Schoenhage.RecoveryCleanupGenerated

def copySlots : Fin (2+2) ≃ Fin 4 where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by decide
  right_inv := by decide

def shiftSlots : Fin (1+3) ≃ Fin 4 where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by decide
  right_inv := by decide

def cleanupSlots : Fin (3+1) ≃ Fin 4 where
  toFun := ![1,2,3,0]
  invFun := ![3,0,1,2]
  left_inv := by decide
  right_inv := by decide

def bank (source output : ℤ → Fin 4) (sourceHead outputHead : ℤ)
    (scratchA scratchB : WTape) : Tapes 4 0 :=
  ⟨![outputHead,sourceHead,scratchA.pos,scratchB.pos],
    ![output,source,scratchA.tape,scratchB.tape]⟩

def input (word : List Bool) (scratchA scratchB : WTape) : Tapes 4 0 :=
  bank (reg word).tape (fun _ => blank) 0 0 scratchA scratchB

def output (word : List Bool) : Tapes 4 0 :=
  bank (fun _ => blank) (wordTape (word.map bitSymbol)) 0 word.length emp emp

def copyPart := reindex (extend (Copy.program (a := 0) separator false) 2) copySlots
def shiftPart := reindex (extend (MultiplicationInputSplit.shift (a := 0) .right) 3) shiftSlots
noncomputable def cleanupPart := reindex
  (extend (compile (by decide) recoveryCleanupProgram).2 1) cleanupSlots
noncomputable def program := seq (seq copyPart shiftPart) cleanupPart

def cleanupInput (word : List Bool) (scratchA scratchB : WTape) : Fin 3 → WTape :=
  ![⟨[word],[]⟩,scratchA,scratchB]

def cost (word : List Bool) (scratchA scratchB : WTape) : ℕ :=
  3 * word.length + 2 * clen scratchA.words + 2 * clen scratchB.words + 13

theorem cleanup_output (localBank : Fin 3 → WTape) :
    (recoveryCleanupCertificate localBank).output = fun _ => emp := by
  rw [recoveryCleanup_output]
  change ([0,1,2] : List (Fin 3)).foldl
    (fun current slot => Function.update current slot emp) localBank = _
  rw [Schoenhage.TapeBank.clear_fold]
  exact Schoenhage.TapeBank.cleared_all _ (by intro tape; fin_cases tape <;> simp) localBank

theorem cleanup_cost (word : List Bool) (scratchA scratchB : WTape) :
    recoveryCleanupCost (cleanupInput word scratchA scratchB) =
      2 * word.length + 2 * clen scratchA.words + 2 * clen scratchB.words + 10 := by
  simp [recoveryCleanupCost, recoveryCleanupCertificate, Block.then, ofRuns,
    recoveryCleanupStage0, recoveryCleanupStage1, recoveryCleanupStage2,
    cleanupInput, WTape.words, clen]
  omega

theorem source_word (word : List Bool) :
    (reg word).tape (a := 0) = wordTape (word.map bitSymbol ++ [separator]) := by
  simp [WTape.tape, WTape.words, reg, cells, syms, List.map_append, List.map_map, Function.comp_def, sym]

theorem source_put (word : List Bool) :
    putWord (putWord (fun _ => (blank : Fin 4)) word.length [separator]) 0
      (word.map bitSymbol) = (reg word).tape := by
  rw [source_word]
  have joined := putWord_append (fun _ => (blank : Fin 4)) 0 (word.map bitSymbol) [separator]
  simp only [List.length_map, zero_add] at joined
  rw [← joined]
  exact putWord_blank_origin _

theorem copy_bank (source destination : ℤ → Fin 4) (sourceHead destinationHead : ℤ)
    (scratchA scratchB : WTape) :
    ((Copy.tapes source destination sourceHead destinationHead).append
      (enc ![scratchA,scratchB])).reindex copySlots =
      bank source destination sourceHead destinationHead scratchA scratchB := by
  unfold bank Copy.tapes Copy.cfg Config.tapes enc Tapes.append Tapes.reindex copySlots
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem shift_bank (source destination : ℤ → Fin 4) (sourceHead destinationHead : ℤ)
    (scratchA scratchB : WTape) :
    ((⟨fun _ => sourceHead,fun _ => source⟩ : Tapes 1 0).append
      ⟨![destinationHead,scratchA.pos,scratchB.pos],![destination,scratchA.tape,scratchB.tape]⟩).reindex shiftSlots =
      bank source destination sourceHead destinationHead scratchA scratchB := by
  unfold bank Tapes.append Tapes.reindex shiftSlots
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem cleanup_bank (localBank : Fin 3 → WTape) (destination : ℤ → Fin 4) (destinationHead : ℤ) :
    ((enc localBank).append (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 0)).reindex cleanupSlots =
      bank (localBank 0).tape destination (localBank 0).pos destinationHead (localBank 1) (localBank 2) := by
  unfold bank enc Tapes.append Tapes.reindex cleanupSlots
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- A fixed four-tape machine installs the word and clears all three work tapes.
The source separator is never copied to the output. Empty words are included. -/
theorem runs_install (word : List Bool) (scratchA scratchB : WTape) :
    HoareTime program (· = input word scratchA scratchB) (· = output word)
      (cost word scratchA scratchB) := by
  have bitsNotSeparator : ∀ symbol ∈ word.map (bitSymbol (a := 0)), symbol ≠ separator := by
    intro symbol member
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
    cases bit <;> decide
  have copied := Copy.copy_hoare (a := 0) separator false
    (putWord (fun _ => blank) word.length [separator]) (fun _ => blank) 0 0
    (word.map bitSymbol) bitsNotSeparator (by simp [putWord_head])
  have retainedBits : (word.map (bitSymbol (a := 0))).map (Copy.retained false) = word.map bitSymbol := by simp [Copy.retained]
  rw [retainedBits, source_put] at copied
  have rawOutput : putWord (fun _ => (blank : Fin 4)) 0 (word.map bitSymbol) =
      wordTape (word.map bitSymbol) := by
    exact putWord_blank_origin _
  rw [rawOutput] at copied
  simp only [List.length_map, zero_add] at copied
  have placedCopy := hoare_place copied copySlots (enc ![scratchA,scratchB])
  rw [copy_bank, copy_bank] at placedCopy
  have shifted := hoare_place
    (MultiplicationInputSplit.shifts (a := 0) .right (reg word).tape word.length)
    shiftSlots (⟨![word.length,scratchA.pos,scratchB.pos],
      ![wordTape (word.map bitSymbol),scratchA.tape,scratchB.tape]⟩ : Tapes 3 0)
  rw [shift_bank, shift_bank] at shifted
  simp only [Move.offset] at shifted
  have clean := (recoveryCleanupCertificate (cleanupInput word scratchA scratchB)).hoare (by decide)
  rw [cleanup_output] at clean
  have placedClean := hoare_place clean cleanupSlots
    (⟨fun _ => word.length,fun _ => wordTape (word.map bitSymbol)⟩ : Tapes 1 0)
  rw [cleanup_bank, cleanup_bank] at placedClean
  have sourceAfter : (cleanupInput word scratchA scratchB 0).tape (a := 0) = (reg word).tape := by
    simp [cleanupInput, WTape.tape, WTape.words, reg]
  have sourcePosition : (cleanupInput word scratchA scratchB 0).pos = (word.length : ℤ) + 1 := by
    simp [cleanupInput, WTape.pos, clen]
  rw [sourceAfter, sourcePosition] at placedClean
  have combined := (placedCopy.seq shifted).seq placedClean
  have emptyTape : (emp : WTape).tape (a := 0) = fun _ => blank := by
    funext cell
    simp [emp, WTape.tape, WTape.words, cells, syms, wordTape]
  rw [emptyTape] at combined
  apply combined.consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis) ?_
  change word.length + 1 + 1 + 1 + recoveryCleanupCost (cleanupInput word scratchA scratchB) ≤ _
  rw [cleanup_cost]
  unfold cost
  omega

/-- The same executed final bank meets the multiplication output contract
whenever the supplied recovered word has the proved exact value and width. -/
theorem runs_correct (word : List Bool) (scratchA scratchB : WTape)
    {inputLength : ℕ} {leftInput rightInput : List Bool}
    (wordLength : word.length = 2 * inputLength)
    (wordValue : binaryValue word = binaryValue leftInput * binaryValue rightInput) :
    ∃ elapsed finalConfig, elapsed ≤ cost word scratchA scratchB ∧
      run program elapsed ((input word scratchA scratchB).start program) = some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      finalConfig.tapes = output word := by
  obtain ⟨elapsed, finalConfig, bounded, executed, halted, endpoint⟩ :=
    runs_install word scratchA scratchB _ rfl
  refine ⟨elapsed, finalConfig, bounded, executed, halted, ⟨word, wordLength, wordValue, ?_⟩, endpoint⟩
  change finalConfig.tapes.tape ⟨0,program.tapes_pos⟩ = _
  rw [endpoint]
  rfl

/-- Connect the already-proved coefficient recovery semantics to the actual
installation run. Producing this input word on tape remains upstream work. -/
theorem runs_recovered {chunkWidth chunkTotal inputLength : ℕ}
    (chunkPositive : 0 < chunkWidth) (widthCovers : 2 * inputLength ≤ chunkWidth * chunkTotal)
    {leftInput rightInput : List Bool}
    (leftLength : leftInput.length = inputLength) (rightLength : rightInput.length = inputLength)
    (digits : List ℕ)
    (digitsCorrect : NLogN.evalBase (2 ^ chunkWidth) digits = binaryValue leftInput * binaryValue rightInput)
    (scratchA scratchB : WTape) :
    ∃ elapsed finalConfig,
      elapsed ≤ 6 * inputLength + 2 * clen scratchA.words + 2 * clen scratchB.words + 13 ∧
      run program elapsed
        ((input (ExactRecoveryOutput.output chunkWidth chunkTotal inputLength digits) scratchA scratchB).start program) =
        some finalConfig ∧
      step program finalConfig = none ∧ outputCorrect program inputLength leftInput rightInput finalConfig ∧
      finalConfig.tapes = output (ExactRecoveryOutput.output chunkWidth chunkTotal inputLength digits) := by
  obtain ⟨wordLength, wordValue⟩ := ExactRecoveryOutput.output_spec
    chunkPositive widthCovers leftLength rightLength digits digitsCorrect
  have result := runs_correct (ExactRecoveryOutput.output chunkWidth chunkTotal inputLength digits)
    scratchA scratchB wordLength wordValue
  simpa only [cost, wordLength, show 3 * (2 * inputLength) = 6 * inputLength by omega] using result

end IntegerMultBounds.Machine.RecoverOutputInstall
