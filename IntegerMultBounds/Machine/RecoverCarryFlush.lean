module

public import IntegerMultBounds.Machine.RecoverArrayCleanup

/-! Publish the terminal carry after the coefficient stream ends. Its binary
word is appended at the emitted chunk boundary and its head is restored before
final cleanup. No extra zero coefficient record or full chunk capacity is needed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverCarryFlush
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open Schoenhage

def slots : Fin (2+10) ≃ Fin 12 where
  toFun := ![1,9,0,2,3,4,5,6,7,8,10,11]
  invFun := ![2,0,3,4,5,6,7,8,9,1,10,11]
  left_inv := by decide
  right_inv := by decide

def program : Program 12 4 alphabet :=
  seq (reindex (extend (Copy.program blank false) 10) slots)
    (RecoverWorkspace.atProgram ReturnOrigin.program (1 : Fin 12))

private theorem nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem copy_bank (records : List (List Bool)) (carryBits recovered clock : List Bool)
    (chunkWidth precision : ℕ) (carryHead streamHead : ℤ) :
    ((Copy.tapes (word carryBits) (word recovered) carryHead streamHead).append
      (⟨![0,0,0,0,0,0,0,0,(⟨records.reverse,[]⟩ : WTape).pos,0],
        ![fun _ => blank,word (List.replicate chunkWidth true),fun _ => blank,fun _ => blank,fun _ => blank,
          fun _ => blank,fun _ => blank,word (List.replicate precision true),
          (⟨records.reverse,[]⟩ : WTape).tape,word clock]⟩ : Tapes 10 alphabet)).reindex slots =
      setTape (setTape (RecoverArrayCleanup.input records carryBits recovered clock chunkWidth precision)
        (1 : Fin 12) (word carryBits) carryHead) (9 : Fin 12) (word recovered) streamHead := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex slots setTape
    RecoverArrayCleanup.input RecoverLoad.input RecoverLoad.bank RecoverLoad.ready RecoverIterationFinish.bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_flush (records : List (List Bool)) (carryBits recovered clock : List Bool) (chunkWidth precision : ℕ) :
    HoareTime (program (alphabet := alphabet))
      (· = RecoverArrayCleanup.input records carryBits recovered clock chunkWidth precision)
      (· = RecoverArrayCleanup.input records carryBits (recovered ++ carryBits) clock chunkWidth precision)
      (2 * carryBits.length + 3) := by
  have copied := Copy.copy_hoare (a := alphabet) blank false (fun _ => blank) (word recovered)
    0 recovered.length (carryBits.map bitSymbol) (nonblank _) (by rfl)
  have retained : (Copy.retained false : Fin (alphabet+4) → Fin (alphabet+4)) = id := by funext symbol; rfl
  simp only [retained,List.map_id,List.length_map,zero_add] at copied
  have appended : putWord (word (alphabet := alphabet) recovered) recovered.length (carryBits.map bitSymbol) =
      word (recovered ++ carryBits) := by
    have joined := putWord_append_forward (fun _ => (blank : Fin (alphabet+4))) 0
      (recovered.map bitSymbol) (carryBits.map bitSymbol)
    simpa only [word,List.length_map,zero_add,← List.map_append] using joined
  rw [appended] at copied
  have placed := hoare_place copied slots
    (⟨![0,0,0,0,0,0,0,0,(⟨records.reverse,[]⟩ : WTape).pos,0],
      ![fun _ => blank,word (List.replicate chunkWidth true),fun _ => blank,fun _ => blank,fun _ => blank,
        fun _ => blank,fun _ => blank,word (List.replicate precision true),
        (⟨records.reverse,[]⟩ : WTape).tape,word clock]⟩ : Tapes 10 alphabet)
  change HoareTime _
    (· = ((Copy.tapes (word carryBits) (word recovered) 0 recovered.length).append _).reindex slots)
    (· = ((Copy.tapes (word carryBits) (word (recovered ++ carryBits)) carryBits.length
      ((recovered.length : ℤ) + carryBits.length)).append _).reindex slots) _ at placed
  rw [copy_bank] at placed
  have before : setTape (setTape (RecoverArrayCleanup.input (alphabet := alphabet) records carryBits recovered clock chunkWidth precision)
      (1 : Fin 12) (word carryBits) 0) (9 : Fin 12) (word recovered) recovered.length =
      RecoverArrayCleanup.input records carryBits recovered clock chunkWidth precision := by
    unfold setTape RecoverArrayCleanup.input RecoverLoad.input RecoverLoad.bank RecoverLoad.ready RecoverIterationFinish.bank Tapes.append
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [before] at placed
  let copiedBank := setTape (RecoverArrayCleanup.input (alphabet := alphabet) records carryBits (recovered ++ carryBits)
    clock chunkWidth precision) (1 : Fin 12) (word carryBits) carryBits.length
  have copiedEndpoint : ((Copy.tapes (word (alphabet := alphabet) carryBits) (word (recovered ++ carryBits)) carryBits.length
      ((recovered.length : ℤ) + carryBits.length)).append
      (⟨![0,0,0,0,0,0,0,0,(⟨records.reverse,[]⟩ : WTape).pos,0],
        ![fun _ => blank,word (List.replicate chunkWidth true),fun _ => blank,fun _ => blank,fun _ => blank,
          fun _ => blank,fun _ => blank,word (List.replicate precision true),
          (⟨records.reverse,[]⟩ : WTape).tape,word clock]⟩ : Tapes 10 alphabet)).reindex slots = copiedBank := by
    unfold copiedBank setTape RecoverArrayCleanup.input RecoverLoad.input RecoverLoad.bank RecoverLoad.ready
      RecoverIterationFinish.bank Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex slots
    simp only [List.length_append,Nat.cast_add]
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [copiedEndpoint] at placed
  have returned := RecoverWorkspace.return_at (1 : Fin 12) copiedBank (carryBits.map bitSymbol) (nonblank _)
    (by simp [copiedBank,setTape,List.length_map]) (by simp [copiedBank,setTape]; rfl)
  have endpoint : RecoverWorkspace.restored copiedBank (1 : Fin 12) =
      RecoverArrayCleanup.input (alphabet := alphabet) records carryBits (recovered ++ carryBits) clock chunkWidth precision := by
    unfold RecoverWorkspace.restored copiedBank setTape RecoverArrayCleanup.input RecoverLoad.input RecoverLoad.bank
      RecoverLoad.ready RecoverIterationFinish.bank Tapes.append
    congr 1 <;> apply List.ofFn_injective <;> rfl
  apply (placed.seq returned).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis.trans endpoint)
  simp only [List.length_map]
  omega

end
end IntegerMultBounds.Machine.RecoverCarryFlush
