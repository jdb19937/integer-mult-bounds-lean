module

public import IntegerMultBounds.Machine.RecoverIteration
public import IntegerMultBounds.Machine.WordSegments
public import IntegerMultBounds.Machine.WordTapeBridge
public import IntegerMultBounds.Schoenhage.Words

/-! Physical loading of the next separator-terminated coefficient word from
an immutable source array. Only the coefficient scratch and source-array head
change. The source separator is skipped and is not copied to the numerator. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverLoad
noncomputable section
variable {alphabet : ℕ}
open Schoenhage
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)

def ready (carryBits : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :=
  RecoverIterationFinish.bank carryBits [] [] chunkWidth precision stream 0 0 0 streamHead

def bank (source : WTape) (working : Tapes 10 alphabet) :=
  working.append (⟨fun _ => source.pos,fun _ => source.tape⟩ : Tapes 1 alphabet)

def input (source : WTape) (carryBits : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :=
  bank source (ready carryBits chunkWidth precision stream streamHead)

def loaded (source : WTape) (bits carryBits : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :=
  bank source (setTape (ready carryBits chunkWidth precision stream streamHead) (7 : Fin 10) (word bits) bits.length)

def copySlots : Fin (2+9) ≃ Fin 11 where
  toFun := ![10,7,0,1,2,3,4,5,6,8,9]
  invFun := ![2,3,4,5,6,7,8,1,9,10,0]
  left_inv := by decide
  right_inv := by decide

def program : Program 11 3 alphabet :=
  seq (reindex (extend (Copy.program separator false) 9) copySlots)
    (RecoverWorkspace.atProgram (MultiplicationInputSplit.shift .right) (10 : Fin 11))

theorem source_advance (done rest : List (List Bool)) (bits : List Bool) :
    (⟨bits :: done,rest⟩ : WTape).tape (a := alphabet) = (⟨done,bits :: rest⟩ : WTape).tape ∧
    (⟨bits :: done,rest⟩ : WTape).pos = (⟨done,bits :: rest⟩ : WTape).pos + bits.length + 1 := by
  constructor
  · simp [WTape.tape,WTape.words,List.append_assoc]
  · simp [WTape.pos]; omega

theorem source_overwrite (done rest : List (List Bool)) (bits : List Bool) :
    putWord (⟨done,bits :: rest⟩ : WTape).tape (⟨done,bits :: rest⟩ : WTape).pos
      (bits.map (bitSymbol (a := alphabet))) = (⟨done,bits :: rest⟩ : WTape).tape := by
  have sourceWord : (⟨done,bits :: rest⟩ : WTape).tape (a := alphabet) =
      putWord (fun _ => blank) 0 (cells done.reverse ++ bits.map bitSymbol ++ (separator :: cells rest)) := by
    unfold WTape.tape
    rw [← putWord_blank_origin]
    congr 1
    simp [WTape.words,cells,syms_append,syms_cons,sym,Function.comp_def,List.append_assoc]
  have sourcePosition : (⟨done,bits :: rest⟩ : WTape).pos = (cells (a := alphabet) done.reverse).length := by
    rw [length_cells,clen_reverse]
    rfl
  have overwrite := WordSegments.middle (fun _ => (blank : Fin (alphabet+4))) 0
    (cells done.reverse) (bits.map bitSymbol) (separator :: cells rest)
  rw [← sourceWord,zero_add,← sourcePosition] at overwrite
  exact overwrite

private theorem copy_bank (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ)
    (carryBits : List Bool) (chunkWidth precision : ℕ) (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :
    ((Copy.tapes source destination sourceHead destinationHead).append
      (⟨![0,0,0,0,0,0,0,0,streamHead],![fun _ => blank,word carryBits,word (List.replicate chunkWidth true),
        fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true),stream]⟩ : Tapes 9 alphabet)).reindex copySlots =
      (setTape (ready carryBits chunkWidth precision stream streamHead) (7 : Fin 10) destination destinationHead).append
        (⟨fun _ => sourceHead,fun _ => source⟩ : Tapes 1 alphabet) := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex copySlots setTape ready RecoverIterationFinish.bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_load (done rest : List (List Bool)) (bits carryBits : List Bool) (chunkWidth precision : ℕ)
    (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :
    HoareTime (program (alphabet := alphabet))
      (· = input ⟨done,bits :: rest⟩ carryBits chunkWidth precision stream streamHead)
      (· = loaded ⟨bits :: done,rest⟩ bits carryBits chunkWidth precision stream streamHead)
      (bits.length + 2) := by
  have bitsNotSeparator : ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ separator := by
    intro symbol member
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
    cases bit <;> simp [bitSymbol,separator,Fin.ext_iff]
  have copied := Copy.copy_hoare (a := alphabet) separator false (⟨done,bits :: rest⟩ : WTape).tape
    (fun _ => blank) (⟨done,bits :: rest⟩ : WTape).pos 0 (bits.map bitSymbol) bitsNotSeparator
    (by simp only [List.length_map]; exact WTape.tape_sep _ rfl)
  have retained : (Copy.retained false : Fin (alphabet+4) → Fin (alphabet+4)) = id := by funext symbol; rfl
  simp only [retained,List.map_id,List.length_map,zero_add] at copied
  rw [source_overwrite] at copied
  have placed := hoare_place copied copySlots
    (⟨![0,0,0,0,0,0,0,0,streamHead],![fun _ => blank,word carryBits,word (List.replicate chunkWidth true),
      fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,word (List.replicate precision true),stream]⟩ : Tapes 9 alphabet)
  rw [copy_bank,copy_bank] at placed
  have initialReady : setTape (ready (alphabet := alphabet) carryBits chunkWidth precision stream streamHead)
      (7 : Fin 10) (fun _ => blank) 0 = ready carryBits chunkWidth precision stream streamHead := by
    unfold setTape ready RecoverIterationFinish.bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [initialReady] at placed
  let copiedBank := (setTape (ready (alphabet := alphabet) carryBits chunkWidth precision stream streamHead)
    (7 : Fin 10) (word bits) bits.length).append
      (⟨fun _ => (⟨done,bits :: rest⟩ : WTape).pos + bits.length,
        fun _ => (⟨done,bits :: rest⟩ : WTape).tape⟩ : Tapes 1 alphabet)
  have skipped := RecoverWorkspace.shift_at (10 : Fin 11) copiedBank .right
  have endpoint : setTape copiedBank (10 : Fin 11) (copiedBank.tape 10)
      (copiedBank.head 10 + Move.right.offset) =
      loaded (alphabet := alphabet) ⟨bits :: done,rest⟩ bits carryBits chunkWidth precision stream streamHead := by
    obtain ⟨sameTape,nextPosition⟩ := source_advance (alphabet := alphabet) done rest bits
    unfold loaded bank copiedBank setTape Tapes.append
    rw [sameTape,nextPosition]
    congr 1 <;> apply List.ofFn_injective <;> rfl
  apply (placed.seq skipped).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis.trans endpoint)
  omega

theorem loaded_native (done rest : List (List Bool)) (signedLowBits : List Bool) (sign : Bool)
    (carryBits : List Bool) (chunkWidth precision : ℕ) (stream : ℤ → Fin (alphabet+4)) (streamHead : ℤ) :
    loaded (alphabet := alphabet) ⟨(signedLowBits ++ [sign]) :: done,rest⟩ (signedLowBits ++ [sign])
      carryBits chunkWidth precision stream streamHead =
      (RecoverIteration.input signedLowBits sign carryBits chunkWidth precision stream streamHead).append
        (⟨fun _ => (⟨(signedLowBits ++ [sign]) :: done,rest⟩ : WTape).pos,
          fun _ => (⟨(signedLowBits ++ [sign]) :: done,rest⟩ : WTape).tape⟩ : Tapes 1 alphabet) := by
  unfold loaded bank ready RecoverIterationFinish.bank setTape RecoverIteration.input
    RecoverSignedCoefficient.input RecoverSignedCoefficient.work RecoverCarryStep.completeInput RecoverCarryStep.input
    RecoverCarryStep.bank Copy.tapes Copy.cfg Config.tapes Tapes.append
  congr 1 <;> apply List.ofFn_injective <;> rfl

end
end IntegerMultBounds.Machine.RecoverLoad
