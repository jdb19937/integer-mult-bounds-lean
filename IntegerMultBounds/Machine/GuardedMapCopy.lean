module

public import IntegerMultBounds.Machine.DelimitedReverseCopy

/-! Copy a symbol word while a fixed finite-alphabet predicate holds, applying
a fixed symbol conversion during each actual write. Reflection gives backwards
source reads and forward emission at the same exact transition count. -/

@[expose] public section
namespace IntegerMultBounds.Machine.GuardedMapCopy
variable {alphabet : ℕ}
open Copy (cfg tapes)

def program (live : Fin (alphabet+4) → Bool) (convert : Fin (alphabet+4) → Fin (alphabet+4)) : Program 2 1 alphabet where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols => if live (symbols 0) then
    some (0,fun slot => (if slot=0 then symbols 0 else convert (symbols 0),.right)) else none

theorem copy_step (live : Fin (alphabet+4) → Bool) (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ)
    (sourceLive : live (source sourceHead)=true) :
    step (program live convert) (cfg source destination sourceHead destinationHead)=
      some (cfg source (Function.update destination destinationHead (convert (source sourceHead)))
        (sourceHead+1) (destinationHead+1)) := by
  simp only [step,program,cfg,↓reduceIte,sourceLive,Move.offset]
  congr 1
  congr 1
  · funext slot; fin_cases slot <;> simp
  · funext slot position
    fin_cases slot <;> simp [Function.update_apply,eq_comm]
    all_goals try (intro equal; rw [equal])

theorem copy_run (live : Fin (alphabet+4) → Bool) (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (source destination : ℤ → Fin (alphabet+4)) (origin destinationHead : ℤ) (symbols : List (Fin (alphabet+4)))
    (symbolsLive : ∀ symbol ∈ symbols,live symbol=true) :
    run (program live convert) symbols.length (cfg (putWord source origin symbols) destination origin destinationHead)=
      some (cfg (putWord source origin symbols) (putWord destination destinationHead (symbols.map convert))
        (origin+symbols.length) (destinationHead+symbols.length)) := by
  induction symbols generalizing source destination origin destinationHead with
  | nil => simp [putWord,run]
  | cons symbol rest inductionHypothesis =>
    have first := copy_step live convert (putWord source origin (symbol::rest)) destination origin destinationHead
      (by rw [putWord_head]; exact symbolsLive symbol (by simp))
    rw [putWord_head] at first
    simp only [List.length_cons,run,first,Option.bind_some]
    have remaining := inductionHypothesis (Function.update source origin symbol)
      (Function.update destination destinationHead (convert symbol)) (origin+1) (destinationHead+1)
      (fun next member => symbolsLive next (by simp [member]))
    simpa only [List.map_cons,←putWord_cons,List.length_cons,Nat.cast_add,Nat.cast_one,
      add_assoc,add_comm,add_left_comm] using remaining

theorem copy_hoare (live : Fin (alphabet+4) → Bool) (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (source destination : ℤ → Fin (alphabet+4)) (origin destinationHead : ℤ) (symbols : List (Fin (alphabet+4)))
    (symbolsLive : ∀ symbol ∈ symbols,live symbol=true) (endStopped : live (source (origin+symbols.length))=false) :
    HoareTime (program live convert) (· = tapes (putWord source origin symbols) destination origin destinationHead)
      (· = tapes (putWord source origin symbols) (putWord destination destinationHead (symbols.map convert))
        (origin+symbols.length) (destinationHead+symbols.length)) symbols.length := by
  rintro current rfl
  refine ⟨symbols.length,_,le_rfl,copy_run live convert source destination origin destinationHead symbols symbolsLive,?_,rfl⟩
  simp [step,program,cfg,putWord_outside _ _ _ _ (Or.inr (le_refl _)),endStopped]

def mask (slot : Fin 2) : Bool := decide (slot=0)
def reverseProgram (live : Fin (alphabet+4) → Bool) (convert : Fin (alphabet+4) → Fin (alphabet+4)) :=
  Reflection.program (program live convert) mask

private theorem reflected_bank (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ) :
    Reflection.tapes mask (tapes source destination sourceHead destinationHead)=
      tapes (fun position => source (-position)) destination (-sourceHead) destinationHead := by
  unfold Reflection.tapes tapes cfg Config.tapes
  congr 1
  · funext slot; fin_cases slot <;> simp [mask,Reflection.coord]
  · funext slot position; fin_cases slot <;> simp [mask,Reflection.coord]

/-- Read one physical word backwards and convert its copied symbols. Any
non-live delimiter before the word terminates the actual finite program. -/
theorem reverse_hoare (live : Fin (alphabet+4) → Bool) (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (source destination : ℤ → Fin (alphabet+4)) (origin destinationHead : ℤ) (symbols : List (Fin (alphabet+4)))
    (symbolsLive : ∀ symbol ∈ symbols,live symbol=true) (beforeStopped : live (source (origin-1))=false) :
    HoareTime (reverseProgram live convert)
      (· = tapes (putWord source origin symbols) destination (origin+symbols.length-1) destinationHead)
      (· = tapes (putWord source origin symbols) (putWord destination destinationHead (symbols.reverse.map convert))
        (origin-1) (destinationHead+symbols.length)) symbols.length := by
  have copied := copy_hoare live convert (fun position => source (-position)) destination
    (-origin-symbols.length+1) destinationHead symbols.reverse (by simpa using symbolsLive) (by
      have position : -(-origin-(symbols.length : ℤ)+1+symbols.reverse.length)=origin-1 := by simp; omega
      rw [position]
      exact beforeStopped)
  simp only [List.length_reverse] at copied
  have reflected := Reflection.hoare copied mask
  have sourceWord : (fun position => putWord (fun index => source (-index)) (-origin-symbols.length+1) symbols.reverse (-position)) =
      putWord source origin symbols := by
    rw [Reflection.word,List.reverse_reverse,List.length_reverse]
    have position : -(-origin-(symbols.length : ℤ)+1)-symbols.length+1=origin := by omega
    rw [position]
    simp only [neg_neg]
  apply reflected.consequence
  · intro current ready
    refine ⟨_,rfl,?_⟩
    rw [reflected_bank,sourceWord]
    have position : -(-origin-(symbols.length : ℤ)+1)=origin+symbols.length-1 := by omega
    simpa only [position] using ready
  · intro current ⟨original,ready,reflectedReady⟩
    rw [ready,reflected_bank,sourceWord] at reflectedReady
    have position : -(-origin-(symbols.length : ℤ)+1+symbols.length)=origin-1 := by omega
    simpa only [position,List.length_reverse] using reflectedReady
  · rfl

end IntegerMultBounds.Machine.GuardedMapCopy
