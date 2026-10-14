module

public import IntegerMultBounds.Machine.RecoverExponentRuler

/-! Two actual ruler cells are erased per retained clock cell. The two-state
controller runs directly from the supplied ruler clock without a binary count;
source and clock heads, all erased cells and the exact shortened tape are
accounted for. This implements twice-chunk and twice-exponent precision shifts. -/

@[expose] public section
namespace IntegerMultBounds.Machine.DoubleRulerErase
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)

def program : Program 2 2 alphabet where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    if symbols 1 = blank then none else some (1,fun slot =>
      (if slot = 0 then blank else symbols slot,if slot = 0 then Move.left else Move.stay))
    else some (0,fun slot => (if slot = 0 then blank else symbols slot,
      if slot = 0 then Move.left else Move.right))

def cfg (source clock : ℤ → Fin (alphabet+4)) (sourceHead clockHead : ℤ) (state : Fin 2) : Config 2 2 alphabet :=
  ⟨state,![sourceHead,clockHead],![source,clock]⟩

private theorem first_step (source clock : ℤ → Fin (alphabet+4)) (sourceHead clockHead : ℤ)
    (clockLive : clock clockHead ≠ blank) :
    step program (cfg source clock sourceHead clockHead 0) =
      some (cfg (Function.update source sourceHead blank) clock (sourceHead-1) clockHead 1) := by
  simp [step,program,cfg,clockLive,Move.offset]
  constructor
  · funext slot; fin_cases slot <;> simp [sub_eq_add_neg]
  · funext slot position; fin_cases slot <;> simp [Function.update_apply]
    intro equal; rw [equal]

private theorem second_step (source clock : ℤ → Fin (alphabet+4)) (sourceHead clockHead : ℤ) :
    step program (cfg source clock sourceHead clockHead 1) =
      some (cfg (Function.update source sourceHead blank) clock (sourceHead-1) (clockHead+1) 0) := by
  simp [step,program,cfg,Move.offset]
  constructor
  · funext slot; fin_cases slot <;> simp [sub_eq_add_neg]
  · funext slot position; fin_cases slot <;> simp [Function.update_apply]
    intro equal; rw [equal]

private theorem erase_pair (remaining : ℕ) (clock : ℤ → Fin (alphabet+4)) (clockHead : ℤ)
    (clockLive : clock clockHead ≠ blank) :
    run program 2 (cfg (word (List.replicate (remaining+2) true)) clock (remaining+1) clockHead 0) =
      some (cfg (word (List.replicate remaining true)) clock ((remaining : ℤ)-1) (clockHead+1) 0) := by
  rw [run,first_step _ _ _ _ clockLive]
  have firstErase := RecoverRulerTrim.erase_last (alphabet := alphabet) (remaining+1)
  simp only [Nat.cast_add,Nat.cast_one] at firstErase
  rw [firstErase]
  have firstHead : (remaining : ℤ)+1-1 = remaining := by omega
  rw [firstHead]
  simp only [Option.bind_some,run_one]
  rw [second_step,RecoverRulerTrim.erase_last]

/-- The clock's actual nonblank cells control exactly two erasures each.
Neither an erasure count nor a destination position is encoded in finite control. -/
theorem erase_run (width count : ℕ) (clock : ℤ → Fin (alphabet+4)) (clockHead : ℤ)
    (erasuresFit : 2 * count ≤ width)
    (clockLive : ∀ index < count, clock (clockHead+index) ≠ blank) :
    run program (2 * count) (cfg (word (List.replicate width true)) clock ((width : ℤ)-1) clockHead 0) =
      some (cfg (word (List.replicate (width-2*count) true)) clock
        (((width-2*count : ℕ) : ℤ)-1) (clockHead+count) 0) := by
  induction count generalizing width clockHead with
  | zero => simp [run]
  | succ count inductionHypothesis =>
    have widthSplit : width = (width-2)+2 := by omega
    have sourceHead : (width : ℤ)-1 = ((width-2 : ℕ) : ℤ)+1 := by omega
    rw [show 2*(count+1) = 2+2*count by omega,run_add]
    have firstPair := erase_pair (alphabet := alphabet) (width-2) clock clockHead
      (by simpa using clockLive 0 (by omega))
    rw [← widthSplit,← sourceHead] at firstPair
    rw [firstPair]
    simp only [Option.bind_some]
    have rest := inductionHypothesis (width-2) (clockHead+1) (by omega) (by
      intro index bound
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using clockLive (index+1) (by omega))
    have remainingEquation : width-2-2*count = width-2*(count+1) := by omega
    rw [remainingEquation] at rest
    simpa only [Nat.mul_add,Nat.mul_one,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using rest

/-- The shortened precision ruler is exact and the entire length clock is
retained, with its cursor at the blank end. Both zero and full erasure work. -/
theorem erase_hoare (width : ℕ) (clockBits : List Bool) (erasuresFit : 2 * clockBits.length ≤ width) :
    HoareTime (program (alphabet := alphabet))
      (· = (cfg (word (List.replicate width true)) (word clockBits) ((width : ℤ)-1) 0 0).tapes)
      (· = (cfg (word (List.replicate (width-2*clockBits.length) true)) (word clockBits)
        (((width-2*clockBits.length : ℕ) : ℤ)-1) clockBits.length 0).tapes) (2 * clockBits.length) := by
  rintro current rfl
  refine ⟨2 * clockBits.length,_,le_rfl,?_,?_,rfl⟩
  · simpa only [zero_add,Tapes.start,Config.tapes,program,cfg] using erase_run (alphabet := alphabet) width clockBits.length (word clockBits) 0 erasuresFit (by
      intro index bound
      have cell := WordSegments.get (fun _ => (blank : Fin (alphabet+4))) 0 (clockBits.map bitSymbol) index (by simpa using bound)
      simp only [zero_add,List.getElem_map] at cell
      rw [word,zero_add,cell]
      cases clockBits[index] <;> simp [bitSymbol,blank,Fin.ext_iff])
  · have clockEnd : word (alphabet := alphabet) clockBits clockBits.length = blank := by
      rw [word,putWord_outside _ _ _ _ (Or.inr (by simp))]
    simp [step,program,cfg,clockEnd]

end
end IntegerMultBounds.Machine.DoubleRulerErase
