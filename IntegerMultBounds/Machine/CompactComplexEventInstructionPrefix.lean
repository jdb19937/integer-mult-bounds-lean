module

public import IntegerMultBounds.Machine.CompactComplexActualInterleavedNetwork

/-! Chronological original-event prefixes expand one literal scalar or child
instruction block at a time. Prefix execution runs the new block after the
previous prefix, matching the actual framed execution order. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexEventInstructionPrefix
noncomputable section
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexActualInterleavedNetwork (expand instructions)
open CompactComplexActualEventNetwork (Stored)
open Networks
attribute [local irreducible] ComplexRank25.program schedule

private theorem flatMap_prefix_step {Element Output : Type*}
    (items : List Element) (render : Element → List Output) (index : ℕ)
    (indexBound : index < items.length) :
    (items.take (index+1)).flatMap render=
      (items.take index).flatMap render++render items[index] := by
  rw [List.take_succ_eq_append_getElem indexBound,List.flatMap_append]
  simp only [List.flatMap_singleton]

/-- Expanding one further original event appends exactly its actual scalar
or child instruction block, for every symbolic event list. -/
theorem prefix_step (columns : ℕ) (events : List Event) (eventIndex : ℕ)
    (eventBound : eventIndex < events.length) :
    expand columns (events.take (eventIndex+1))=
      expand columns (events.take eventIndex)++instructions columns events[eventIndex] :=
  flatMap_prefix_step events (instructions columns) eventIndex eventBound

/-- The new event executes after the earlier prefix, with the literal order
proved by the original framed execution's append theorem. -/
theorem prefix_run_step (columns : ℕ) (events : List Event) (eventIndex : ℕ)
    (eventBound : eventIndex < events.length) (initialArrays : Stored columns) :
    FramedFactorExecution.run (expand columns (events.take (eventIndex+1))) initialArrays=
      FramedFactorExecution.run (instructions columns events[eventIndex])
        (FramedFactorExecution.run (expand columns (events.take eventIndex)) initialArrays) := by
  rw [prefix_step columns events eventIndex eventBound,FramedFactorExecution.run_append]

/-- An actual scheduled event has exactly the symbolic prefix expansion. -/
theorem schedule_prefix_step (columns eventIndex : ℕ) (eventBound : eventIndex < schedule.length) :
    expand columns (schedule.take (eventIndex+1))=
      expand columns (schedule.take eventIndex)++instructions columns schedule[eventIndex] :=
  prefix_step columns schedule eventIndex eventBound

/-- Literal schedule-prefix execution is ready for array-trace induction. -/
theorem schedule_prefix_run_step (columns eventIndex : ℕ) (eventBound : eventIndex < schedule.length)
    (initialArrays : Stored columns) :
    FramedFactorExecution.run (expand columns (schedule.take (eventIndex+1))) initialArrays=
      FramedFactorExecution.run (instructions columns schedule[eventIndex])
        (FramedFactorExecution.run (expand columns (schedule.take eventIndex)) initialArrays) :=
  prefix_run_step columns schedule eventIndex eventBound initialArrays

/-- The empty event prefix leaves the original stored arrays unchanged. -/
theorem prefix_run_zero (columns : ℕ) (events : List Event) (initialArrays : Stored columns) :
    FramedFactorExecution.run (expand columns (events.take 0)) initialArrays=initialArrays := by
  simp only [List.take_zero,expand,List.flatMap_nil,FramedFactorExecution.run]

/-- At the terminal prefix the actual schedule has the original complete
compiler-network action, including its proved terminal sink incidences. -/
theorem schedule_prefix_terminal (columns : ℕ) (initialArrays : Stored columns) :
    FramedFactorExecution.run (expand columns (schedule.take schedule.length)) initialArrays=
      FramedCircuit.run (ComplexFramedExecution.network columns) initialArrays := by
  rw [List.take_length]
  exact CompactComplexActualInterleavedNetwork.schedule_run columns initialArrays

end
end IntegerMultBounds.Machine.CompactComplexEventInstructionPrefix
