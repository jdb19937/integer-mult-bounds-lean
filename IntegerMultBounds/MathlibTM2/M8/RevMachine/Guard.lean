module

public import IntegerMultBounds.Machine.SharedBankFamilyExact
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Graph

/-!
# The test of the leaf loop

The test reads two counters under their heads and halts at once: in state `1` (one more leaf)
when the remaining-leaf counter is nonzero, else in state `2` (the node) when the atom count
per coordinate is nonzero, else in state `3` (done). A canonical counter at head one is zero
exactly when its first cell is blank. Every tape and head is kept (`run_exact`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Guard

open IntegerMultBounds.Machine
open SharedBankFamilyExact (atState)
variable {t a : ℕ}

def program (rem fc : Fin t) : Program t 4 a where
  tapes_pos := Nat.zero_lt_of_lt rem.isLt
  start := 0
  transition := fun st sy =>
    if st = 0 then
      some (if sy rem ≠ blank then 1 else if sy fc ≠ blank then 2 else 3, fun i => (sy i, Move.stay))
    else none

/-- The exit of each terminal state. -/
def exit : Fin 4 → Graph.Exit := ![.done, .leaf, .node, .done]

/-- The terminal state the test reaches on the bank `v`. -/
def result (rem fc : Fin t) (v : Tapes t a) : Fin 4 :=
  if v.tape rem (v.head rem) ≠ blank then 1 else if v.tape fc (v.head fc) ≠ blank then 2 else 3

theorem result_ne_zero (rem fc : Fin t) (v : Tapes t a) : result rem fc v ≠ 0 := by
  unfold result; split_ifs <;> decide

/-- **The test** halts after one step in its result state with the bank kept. -/
theorem run_exact (rem fc : Fin t) (v : Tapes t a) :
    run (program rem fc) 1 (v.start (program rem fc)) = some (atState v (result rem fc v)) ∧
      step (program rem fc) (atState v (result rem fc v)) = none := by
  constructor
  · rw [run_one]
    simp only [step, program, Tapes.start, ite_true, result]
    congr 1
    apply congrArg₂ (Config.mk _)
    · funext i; simp [Move.offset]
    · funext i z; by_cases hz : z = v.head i <;> simp [hz]
  · simp [step, program, atState, result_ne_zero]

end IntegerMultBounds.MathlibTM2.M8.RevMachine.Guard
