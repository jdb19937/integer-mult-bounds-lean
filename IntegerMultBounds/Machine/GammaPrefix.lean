module

public import IntegerMultBounds.Machine.RecoverBinaryOutput

/-! Discover a gamma code's binary width on the tape. One true ruler cell is
written per leading zero and one for the first true bit. The source head stays
on that first true bit; all source cells and destination exterior are retained. -/

@[expose] public section
namespace IntegerMultBounds.Machine.GammaPrefix
variable {alphabet : ℕ}

def program : Program 2 2 alphabet where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    if symbols 1 = bitSymbol false then some (0,fun slot =>
      (if slot = 0 then bitSymbol true else symbols slot,Move.right))
    else if symbols 1 = bitSymbol true then some (1,fun slot =>
      (if slot = 0 then bitSymbol true else symbols slot,if slot = 0 then Move.right else Move.stay))
    else none
    else none

def cfg (ruler source : ℤ → Fin (alphabet+4)) (rulerHead sourceHead : ℤ) (state : Fin 2) : Config 2 2 alphabet :=
  ⟨state, ![rulerHead,sourceHead], ![ruler,source]⟩

private theorem zero_step (ruler source : ℤ → Fin (alphabet+4)) (rulerHead sourceHead : ℤ)
    (sourceZero : source sourceHead = bitSymbol false) :
    step program (cfg ruler source rulerHead sourceHead 0) =
      some (cfg (Function.update ruler rulerHead (bitSymbol true)) source (rulerHead+1) (sourceHead+1) 0) := by
  simp [step,program,cfg,sourceZero,Move.offset]
  constructor
  · funext slot; fin_cases slot <;> simp
  · funext slot position; fin_cases slot <;> simp [Function.update_apply]
    intro equal; rw [equal]

private theorem one_step (ruler source : ℤ → Fin (alphabet+4)) (rulerHead sourceHead : ℤ)
    (sourceOne : source sourceHead = bitSymbol true) :
    step program (cfg ruler source rulerHead sourceHead 0) =
      some (cfg (Function.update ruler rulerHead (bitSymbol true)) source (rulerHead+1) sourceHead 1) := by
  have different : bitSymbol (a := alphabet) true ≠ bitSymbol false := by simp [bitSymbol,Fin.ext_iff]
  simp [step,program,cfg,sourceOne,different,Move.offset]
  constructor
  · funext slot; fin_cases slot <;> simp
  · funext slot position; fin_cases slot <;> simp [Function.update_apply]
    intro equal; rw [equal]

/-- The first true cell actually stops the prefix scan. The code length is
neither supplied to the finite control nor read from a prepared counter. -/
theorem prefix_run (ruler source : ℤ → Fin (alphabet+4)) (rulerHead sourceHead : ℤ) (zeroCount : ℕ)
    (leadingZeros : ∀ index < zeroCount, source (sourceHead+index) = bitSymbol false)
    (firstOne : source (sourceHead+zeroCount) = bitSymbol true) :
    run program (zeroCount+1) (cfg ruler source rulerHead sourceHead 0) =
      some (cfg (putWord ruler rulerHead (List.replicate (zeroCount+1) (bitSymbol true))) source
        (rulerHead+zeroCount+1) (sourceHead+zeroCount) 1) := by
  induction zeroCount generalizing ruler rulerHead sourceHead with
  | zero =>
    simpa only [Nat.zero_add, Nat.cast_zero, add_zero, List.replicate_one, putWord, run_one] using
      one_step ruler source rulerHead sourceHead (by simpa using firstOne)
  | succ zeroCount inductionHypothesis =>
    rw [show zeroCount+1+1 = (zeroCount+1)+1 by rfl, run, zero_step ruler source rulerHead sourceHead
      (by simpa using leadingZeros 0 (by omega))]
    simp only [Option.bind_some]
    have tail := inductionHypothesis (Function.update ruler rulerHead (bitSymbol true)) (rulerHead+1) (sourceHead+1)
      (by intro index bound; simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using leadingZeros (index+1) (by omega))
      (by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using firstOne)
    rw [List.replicate_succ,putWord_cons]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using tail

theorem prefix_hoare (ruler source : ℤ → Fin (alphabet+4)) (rulerHead sourceHead : ℤ) (zeroCount : ℕ)
    (leadingZeros : ∀ index < zeroCount, source (sourceHead+index) = bitSymbol false)
    (firstOne : source (sourceHead+zeroCount) = bitSymbol true) :
    HoareTime program (· = (cfg ruler source rulerHead sourceHead 0).tapes)
      (· = (cfg (putWord ruler rulerHead (List.replicate (zeroCount+1) (bitSymbol true))) source
        (rulerHead+zeroCount+1) (sourceHead+zeroCount) 1).tapes) (zeroCount+1) := by
  rintro current rfl
  exact ⟨zeroCount+1,_,le_rfl,prefix_run ruler source rulerHead sourceHead zeroCount leadingZeros firstOne,
    by simp [step,program,cfg],rfl⟩

end IntegerMultBounds.Machine.GammaPrefix
