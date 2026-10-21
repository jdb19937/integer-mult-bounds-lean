module

public import IntegerMultBounds.Machine.CounterDimensions
public import IntegerMultBounds.Machine.CounterSteps

/-!
# The six counters of a dimension bank

The input of `CounterDimensions` holds six counters `w 0, …, w 5` (`b, W, T, R, K, M`) at slots
`3..8` (`counters_eq`). Writing a new counter value at its slot is updating `w`
(`counters_set`), so the counter steps of `CounterSteps` act on the counters as functions.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.CounterBank
open FlatCoordinateSchedule (bits)
open SharedPlacementAlphabet (setTape)
noncomputable section
variable {q : ℕ}

/-- The slots of the counters. -/
def slot (j : Fin 6) : Fin 17 := ⟨3 + j.val, by omega⟩

/-- The six counters as optional descriptors. -/
def entries (w : Fin 6 → ℕ) : Fin 17 → Option (List Bool) :=
  fun i => if h : 3 ≤ i.val ∧ i.val < 9 then some (bits (w ⟨i.val - 3, by omega⟩)) else none

/-- The bank of six counters. -/
def counters (w : Fin 6 → ℕ) : Tapes 17 q := CounterDimensions.bank (entries w)

theorem counters_eq (b W T R K M : ℕ) :
    CounterDimensions.input (q := q) (bits b) (bits W) (bits T) (bits R) (bits K) (bits M) =
      counters ![b, W, T, R, K, M] := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem counters_tape (w : Fin 6 → ℕ) (j : Fin 6) :
    (counters (q := q) w).tape (slot j) = RadixZeroFill.encodedBinary (bits (w j)) := by
  have h : 3 ≤ (slot j).val ∧ (slot j).val < 9 := by simp [slot]; omega
  unfold counters CounterDimensions.bank entries
  dsimp only
  rw [dite_eq_left h]
  have hj : (⟨(slot j).val - 3, by omega⟩ : Fin 6) = j := by ext; simp [slot]
  rw [hj]
  rfl

theorem counters_head (w : Fin 6 → ℕ) (j : Fin 6) : (counters (q := q) w).head (slot j) = 1 := by
  have h : 3 ≤ (slot j).val ∧ (slot j).val < 9 := by simp [slot]; omega
  unfold counters CounterDimensions.bank entries
  dsimp only
  rw [dite_eq_left h]
  rfl

theorem counters_set (w : Fin 6 → ℕ) (j : Fin 6) (x : ℕ) :
    setTape (counters (q := q) w) (slot j) (RadixZeroFill.encodedBinary (bits x)) 1 =
      counters (Function.update w j x) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [counters, CounterDimensions.bank] <;>
    by_cases hi : i = slot j
  all_goals first
    | (subst hi
       have h : 3 ≤ (slot j).val ∧ (slot j).val < 9 := by simp [slot]; omega
       have hj : (⟨(slot j).val - 3, by omega⟩ : Fin 6) = j := by ext; simp [slot]
       unfold entries
       rw [Function.update_self, dite_eq_left h, hj, Function.update_self]
       rfl)
    | (rw [Function.update_of_ne hi]
       unfold entries
       split_ifs with h
       · have hne : (⟨i.val - 3, by omega⟩ : Fin 6) ≠ j := by
           intro e; apply hi; ext; rw [← e]; simp [slot]; omega
         rw [Function.update_of_ne hne]
       · rfl)

end
end IntegerMultBounds.Machine.CounterBank
