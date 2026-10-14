module

public import IntegerMultBounds.Machine.RecoverWorkspace

/-! Finish a recurring recovery iteration: move the outgoing carry into the
blank incoming slot with both heads restored, append the emitted chunk to an
arbitrary output stream, then erase its temporary word. Both rulers and all
other cleared work remain ready for the next coefficient. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverIterationFinish
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)

def carryProgram : Program 2 4 alphabet :=
  seq (Copy.program blank true) (reindex RulerRetreat.program (Equiv.swap 0 1))
def publishProgram : Program 2 7 alphabet :=
  seq (seq (extend ReturnOrigin.program 1) (Copy.program blank false)) (extend EraseBack.program 1)

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem retreat_bank (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ) :
    ((RulerRetreat.cfg destination source destinationHead sourceHead 0).tapes).reindex (Equiv.swap 0 1) =
      Copy.tapes source destination sourceHead destinationHead := by
  unfold RulerRetreat.cfg Config.tapes Tapes.reindex Copy.tapes Copy.cfg
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_carry (carryBits : List Bool) :
    HoareTime (carryProgram (alphabet := alphabet))
      (· = Copy.tapes (word carryBits) (fun _ => blank) 0 0)
      (· = Copy.tapes (fun _ => blank) (word carryBits) 0 0) (2 * carryBits.length + 3) := by
  have copied := Copy.copy_hoare (a := alphabet) blank true (fun _ => blank) (fun _ => blank)
    0 0 (carryBits.map bitSymbol) (bits_nonblank _) (by rfl)
  have retained : (Copy.retained true : Fin (alphabet+4) → Fin (alphabet+4)) = fun _ => blank := by funext symbol; rfl
  rw [retained] at copied
  simp only [List.length_map,zero_add] at copied
  have erasedSource : putWord (fun _ => (blank : Fin (alphabet+4))) 0
      ((carryBits.map (bitSymbol (a := alphabet))).map (fun _ => blank)) = fun _ => blank := by
    rw [List.map_const',putWord_replicate_blank _ _ _ (by intros; rfl)]
  rw [erasedSource] at copied
  have returned := RulerRetreat.retreat_hoare (a := alphabet) (fun _ => blank) (fun _ => blank)
    0 0 (carryBits.map bitSymbol) (bits_nonblank _) (by rfl)
  have placed := hoare_reindex_eq returned (Equiv.swap 0 1)
  simp only [List.length_map,zero_add] at placed
  rw [retreat_bank,retreat_bank] at placed
  apply (copied.seq placed).consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

private theorem frame_bank (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ) (state : Fin 3) :
    ((ReturnOrigin.cfg source sourceHead state).tapes.append
      (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 alphabet)) =
      Copy.tapes source destination sourceHead destinationHead := by
  unfold ReturnOrigin.cfg Config.tapes Tapes.append Copy.tapes Copy.cfg
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem erase_frame_bank (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ) (state : Fin 3) :
    ((EraseBack.cfg source sourceHead state).tapes.append
      (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 alphabet)) =
      Copy.tapes source destination sourceHead destinationHead := by
  unfold EraseBack.cfg Config.tapes Tapes.append Copy.tapes Copy.cfg
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_publish (chunk : List Bool) (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :
    HoareTime (publishProgram (alphabet := alphabet)) (· = Copy.tapes (word chunk) stream chunk.length streamHead)
      (· = Copy.tapes (fun _ => blank) (putWord stream streamHead (chunk.map bitSymbol)) 0 (streamHead + chunk.length))
      (3 * chunk.length + 6) := by
  have returned := FamilyPlacementAlphabet.extend_hoare
    (ReturnOrigin.return_hoare (chunk.map (bitSymbol (a := alphabet))) (bits_nonblank _))
    (⟨fun _ => streamHead,fun _ => stream⟩ : Tapes 1 alphabet)
  simp only [List.length_map] at returned
  rw [frame_bank,frame_bank] at returned
  have copied := Copy.copy_hoare (a := alphabet) blank false (fun _ => blank) stream
    0 streamHead (chunk.map bitSymbol) (bits_nonblank _) (by rfl)
  have retained : (Copy.retained false : Fin (alphabet+4) → Fin (alphabet+4)) = id := by funext symbol; rfl
  simp only [retained,List.map_id,List.length_map,zero_add] at copied
  have cleared := FamilyPlacementAlphabet.extend_hoare
    (EraseBack.erase_hoare (fun _ => (blank : Fin (alphabet+4))) 0 (chunk.map bitSymbol)
      (bits_nonblank _) (by rfl) (by intros; rfl))
    (⟨fun _ => streamHead + chunk.length,fun _ => putWord stream streamHead (chunk.map bitSymbol)⟩ : Tapes 1 alphabet)
  simp only [List.length_map,zero_add] at cleared
  rw [erase_frame_bank,erase_frame_bank] at cleared
  apply ((returned.seq copied).seq cleared).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis)
  omega

def carrySlots : Fin (2+8) ≃ Fin 10 where
  toFun := ![4,1,0,2,3,5,6,7,8,9]
  invFun := ![2,1,3,4,0,5,6,7,8,9]
  left_inv := by decide
  right_inv := by decide
def publishSlots : Fin (2+8) ≃ Fin 10 where
  toFun := ![3,9,0,1,2,4,5,6,7,8]
  invFun := ![2,3,4,0,5,6,7,8,9,1]
  left_inv := by decide
  right_inv := by decide

def program : Program 10 11 alphabet :=
  seq (reindex (extend carryProgram 8) carrySlots) (reindex (extend publishProgram 8) publishSlots)

def bank (incoming outgoing chunk : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (incomingHead outgoingHead chunkHead streamHead : ℤ) : Tapes 10 alphabet :=
  ⟨![0,incomingHead,0,chunkHead,outgoingHead,0,0,0,0,streamHead],
    ![fun _ => blank,word incoming,word (List.replicate chunkWidth true),word chunk,word outgoing,
      fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true),stream]⟩

def input (carryBits chunk : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :=
  bank [] carryBits chunk chunkWidth precision stream 0 0 chunk.length streamHead
def output (carryBits chunk : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :=
  bank carryBits [] [] chunkWidth precision (putWord stream streamHead (chunk.map bitSymbol))
    0 0 0 (streamHead + chunk.length)

private theorem carry_bank (incoming outgoing chunk : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (incomingHead outgoingHead chunkHead streamHead : ℤ) :
    ((Copy.tapes (word outgoing) (word incoming) outgoingHead incomingHead).append
      (⟨![0,0,chunkHead,0,0,0,0,streamHead],![fun _ => blank,word (List.replicate chunkWidth true),word chunk,
        fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true),stream]⟩ : Tapes 8 alphabet)).reindex carrySlots =
      bank incoming outgoing chunk chunkWidth precision stream incomingHead outgoingHead chunkHead streamHead := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex carrySlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem publish_bank (incoming outgoing chunk : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (incomingHead outgoingHead chunkHead streamHead : ℤ) :
    ((Copy.tapes (word chunk) stream chunkHead streamHead).append
      (⟨![0,incomingHead,0,outgoingHead,0,0,0,0],![fun _ => blank,word incoming,word (List.replicate chunkWidth true),word outgoing,
        fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true)]⟩ : Tapes 8 alphabet)).reindex publishSlots =
      bank incoming outgoing chunk chunkWidth precision stream incomingHead outgoingHead chunkHead streamHead := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex publishSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_finish (carryBits chunk : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :
    HoareTime (program (alphabet := alphabet)) (· = input carryBits chunk chunkWidth precision stream streamHead)
      (· = output carryBits chunk chunkWidth precision stream streamHead)
      (2 * carryBits.length + 3 * chunk.length + 10) := by
  have moved := hoare_place (runs_carry (alphabet := alphabet) carryBits) carrySlots
    (⟨![0,0,chunk.length,0,0,0,0,streamHead],![fun _ => blank,word (List.replicate chunkWidth true),word chunk,
      fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true),stream]⟩ : Tapes 8 alphabet)
  change HoareTime _ (· = ((Copy.tapes (word carryBits) (word []) 0 0).append _).reindex carrySlots)
    (· = ((Copy.tapes (word []) (word carryBits) 0 0).append _).reindex carrySlots) _ at moved
  rw [carry_bank,carry_bank] at moved
  have published := hoare_place (runs_publish (alphabet := alphabet) chunk stream streamHead) publishSlots
    (⟨![0,0,0,0,0,0,0,0],![fun _ => blank,word carryBits,word (List.replicate chunkWidth true),word [],
      fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true)]⟩ : Tapes 8 alphabet)
  change HoareTime _ (· = ((Copy.tapes (word chunk) stream chunk.length streamHead).append _).reindex publishSlots)
    (· = ((Copy.tapes (word []) (putWord stream streamHead (chunk.map bitSymbol)) 0 (streamHead + chunk.length)).append _).reindex publishSlots) _ at published
  rw [publish_bank,publish_bank] at published
  apply (moved.seq published).consequence (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

end
end IntegerMultBounds.Machine.RecoverIterationFinish
