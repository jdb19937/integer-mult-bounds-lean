module

public import IntegerMultBounds.Machine.RecoverOutputSerialize

/-! Final array workspace reclamation. Erase the retained source array from
its actual end, and scan/erase the final carry and both rulers from origin.
The recovered word and borrowed input-width clock are retained exactly. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverArrayCleanup
noncomputable section
variable {alphabet : ℕ}
open Schoenhage
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)

def eraseOrigin : Program 1 4 alphabet :=
  seq (MultiplicationInputSplit.scan blank) EraseBack.program

/-- The word length is discovered by scanning; neither a counter nor an
execution certificate for its current head is supplied. -/
theorem runs_erase_origin (symbols : List (Fin (alphabet+4)))
    (nonblank : ∀ symbol ∈ symbols, symbol ≠ blank) :
    HoareTime (eraseOrigin (alphabet := alphabet))
      (· = FiniteReturnStack.bank (putWord (fun _ => blank) 0 symbols) 0)
      (· = FiniteReturnStack.bank (fun _ => blank) 0) (2 * symbols.length + 3) := by
  have scanned := MultiplicationInputSplit.scan_hoare (a := alphabet) blank (fun _ => blank) 0 symbols nonblank (by rfl)
  have cleared := EraseBack.erase_hoare (fun _ => (blank : Fin (alphabet+4))) 0 symbols nonblank (by rfl) (by intros; rfl)
  simp only [MultiplicationInputSplit.oneCfg,EraseBack.cfg,Config.tapes,zero_add] at scanned cleared
  apply (scanned.seq cleared).consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

theorem erase_origin_at {t : ℕ} (slot : Fin t) (current : Tapes t alphabet)
    (symbols : List (Fin (alphabet+4))) (nonblank : ∀ symbol ∈ symbols, symbol ≠ blank)
    (headReady : current.head slot = 0)
    (tapeReady : current.tape slot = putWord (fun _ => blank) 0 symbols) :
    HoareTime (RecoverWorkspace.atProgram eraseOrigin slot) (· = current)
      (· = RecoverWorkspace.erased current slot) (2 * symbols.length + 3) :=
  RecoverWorkspace.runs_one_at eraseOrigin slot current _ _ _ _ headReady tapeReady (runs_erase_origin symbols nonblank)

def program : Program 12 15 alphabet :=
  seq (seq (seq (RecoverWorkspace.atProgram EraseBack.program (10 : Fin 12))
    (RecoverWorkspace.atProgram eraseOrigin (1 : Fin 12)))
    (RecoverWorkspace.atProgram eraseOrigin (2 : Fin 12)))
    (RecoverWorkspace.atProgram eraseOrigin (8 : Fin 12))

def input (records : List (List Bool)) (carryBits recovered clock : List Bool) (chunkWidth precision : ℕ) :=
  (RecoverLoad.input (alphabet := alphabet) ⟨records.reverse,[]⟩ carryBits chunkWidth precision (word recovered) recovered.length).append
    (⟨fun _ => 0,fun _ => word clock⟩ : Tapes 1 alphabet)

def output (recovered clock : List Bool) : Tapes 12 alphabet :=
  ⟨![0,0,0,0,0,0,0,0,0,recovered.length,0,0],
    ![fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
      fun _ => blank,fun _ => blank,fun _ => blank,word recovered,fun _ => blank,word clock]⟩

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem cells_nonblank (records : List (List Bool)) :
    ∀ symbol ∈ cells (a := alphabet) records, symbol ≠ blank := by
  intro symbol member
  obtain ⟨sourceSymbol,_,rfl⟩ := List.mem_map.mp member
  exact sym_ne_blank sourceSymbol

theorem runs_cleanup (records : List (List Bool)) (carryBits recovered clock : List Bool) (chunkWidth precision : ℕ) :
    HoareTime (program (alphabet := alphabet)) (· = input records carryBits recovered clock chunkWidth precision)
      (· = output recovered clock)
      (clen records + 2 * carryBits.length + 2 * chunkWidth + 2 * precision + 14) := by
  let initial := input (alphabet := alphabet) records carryBits recovered clock chunkWidth precision
  let stage0 := RecoverWorkspace.erased initial (10 : Fin 12)
  let stage1 := RecoverWorkspace.erased stage0 (1 : Fin 12)
  let stage2 := RecoverWorkspace.erased stage1 (2 : Fin 12)
  let stage3 := RecoverWorkspace.erased stage2 (8 : Fin 12)
  have sourceWord : (⟨records.reverse,[]⟩ : WTape).tape (a := alphabet) =
      putWord (fun _ => blank) 0 (cells records) := by
    rw [putWord_blank_origin]
    simp [WTape.tape,WTape.words]
  have sourceLength : (⟨records.reverse,[]⟩ : WTape).pos = (cells (a := alphabet) records).length := by
    simp [WTape.pos,length_cells,clen_reverse]
  have clearSource := RecoverWorkspace.erase_at (10 : Fin 12) initial (cells records) (cells_nonblank records)
    (by change (⟨records.reverse,[]⟩ : WTape).pos = _; exact sourceLength)
    (by change (⟨records.reverse,[]⟩ : WTape).tape = _; exact sourceWord)
  have clearCarry := erase_origin_at (1 : Fin 12) stage0 (carryBits.map bitSymbol) (bits_nonblank _)
    (by simp [stage0,RecoverWorkspace.erased,setTape]; rfl)
    (by simp [stage0,RecoverWorkspace.erased,setTape]; rfl)
  have clearChunkRuler := erase_origin_at (2 : Fin 12) stage1
    ((List.replicate chunkWidth true).map bitSymbol) (bits_nonblank _)
    (by simp [stage1,stage0,RecoverWorkspace.erased,setTape]; rfl)
    (by simp [stage1,stage0,RecoverWorkspace.erased,setTape]
        change word (List.replicate chunkWidth true) = _
        simp [word])
  have clearPrecisionRuler := erase_origin_at (8 : Fin 12) stage2
    ((List.replicate precision true).map bitSymbol) (bits_nonblank _)
    (by simp [stage2,stage1,stage0,RecoverWorkspace.erased,setTape]; rfl)
    (by simp [stage2,stage1,stage0,RecoverWorkspace.erased,setTape]
        change word (List.replicate precision true) = _
        simp [word])
  have endpoint : stage3 = output (alphabet := alphabet) recovered clock := by
    unfold stage3 stage2 stage1 stage0 initial RecoverWorkspace.erased setTape input RecoverLoad.input RecoverLoad.bank
      RecoverLoad.ready RecoverIterationFinish.bank Tapes.append output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  apply (((clearSource.seq clearCarry).seq clearChunkRuler).seq clearPrecisionRuler).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis.trans endpoint)
  simp only [length_cells,List.length_map,List.length_replicate]
  omega

end
end IntegerMultBounds.Machine.RecoverArrayCleanup
