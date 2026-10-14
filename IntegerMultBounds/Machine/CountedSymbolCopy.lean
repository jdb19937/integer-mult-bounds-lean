module

public import IntegerMultBounds.Machine.CountedLoopHeaderClean
public import IntegerMultBounds.Machine.WordSegments

@[expose] public section
namespace IntegerMultBounds.Machine.CountedSymbolCopy
noncomputable section
variable {alphabet : ℕ}

def payload (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ)
    (descriptor : List Bool) : Tapes 3 alphabet :=
  ⟨![sourceHead,destinationHead,1], ![source,destination,RadixZeroFill.encodedBinary descriptor]⟩

def cell : Program 3 2 alphabet where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state=0 then some (1, fun slot =>
    (if slot=1 then symbols 0 else symbols slot, if slot=2 then .stay else .right)) else none

theorem cell_runs (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ)
    (descriptor : List Bool) :
    HoareTime cell (· = payload source destination sourceHead destinationHead descriptor)
      (· = payload source (Function.update destination destinationHead (source sourceHead))
        (sourceHead+1) (destinationHead+1) descriptor) 1 := by
  rintro bank rfl
  refine ⟨1, ⟨1, (payload source (Function.update destination destinationHead (source sourceHead))
    (sourceHead+1) (destinationHead+1) descriptor).head,
    (payload source (Function.update destination destinationHead (source sourceHead))
      (sourceHead+1) (destinationHead+1) descriptor).tape⟩, le_rfl, ?_, ?_, rfl⟩
  · simp only [run_one, step, cell, Tapes.start, ite_true, payload, Move.offset]
    congr 1
    congr 1
    · funext slot; fin_cases slot <;> rfl
    · funext slot position; fin_cases slot <;> simp [Function.update_apply]
      all_goals intro equal; subst position; rfl
  · simp [step, cell]

def program := CountedLoopHeaderClean.program (cell (alphabet := alphabet)) (2 : Fin 3)
def bank (source destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ)
    (descriptor : List Bool) := CountedLoopHeaderClean.bank (payload source destination sourceHead destinationHead descriptor)

theorem runs (background destination : ℤ → Fin (alphabet+4)) (sourceHead destinationHead : ℤ)
    (symbols : List (Fin (alphabet+4))) (descriptor : List Bool)
    (descriptorValue : Counter.value descriptor = symbols.length) :
    HoareTime program
      (· = bank (putWord background sourceHead symbols) destination sourceHead destinationHead descriptor)
      (· = bank (putWord background sourceHead symbols) (putWord destination destinationHead symbols)
        (sourceHead+symbols.length) (destinationHead+symbols.length) descriptor)
      (7*symbols.length+11*descriptor.length+35) := by
  let source := putWord background sourceHead symbols
  let states := fun copied => payload source (putWord destination destinationHead (symbols.take copied))
    (sourceHead+copied) (destinationHead+copied) descriptor
  have execution := CountedLoopHeaderClean.runs (cell (alphabet := alphabet)) (2 : Fin 3)
    descriptor symbols.length states (fun _ => 1) ⟨rfl,rfl⟩ descriptorValue (by
      intro copied beforeEnd
      have cellRun := cell_runs source (putWord destination destinationHead (symbols.take copied))
        (sourceHead+copied) (destinationHead+copied) descriptor
      have readCell := WordSegments.get background sourceHead symbols copied beforeEnd
      change source (sourceHead+copied) = symbols[copied] at readCell
      have prefixLength : (symbols.take copied).length = copied := List.length_take_of_le (by omega)
      have nextWord := putWord_append_forward destination destinationHead (symbols.take copied) [symbols[copied]]
      simp only [prefixLength, putWord] at nextWord
      rw [readCell, nextWord, ←List.take_succ_eq_append_getElem beforeEnd] at cellRun
      simpa only [states, Nat.cast_add, Nat.cast_one, add_assoc] using cellRun)
  apply execution.consequence
  · intro current ready
    simpa [states, bank, putWord] using ready
  · intro current ready
    simpa [states, bank] using ready
  · simp [CountedLoopHeaderClean.cost]
    omega

end
end IntegerMultBounds.Machine.CountedSymbolCopy
