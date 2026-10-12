module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards

/-! A real scalar event preserves the actual returned-child cursor. Prefix
filtering is proved for abstract event lists before the sealed original
schedule is specialized, so no concrete compiler calls are evaluated. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualReturnedOrdinal
noncomputable section
open CompactComplexScalarIntegerRows (GroupIndex)
open CompactComplexCompletedLiveLower (Event schedule childNames)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites Networks.ComplexRecursiveCallSchema.calls schedule
  CompactComplexRolePhaseSite.roleCount

/-- Consuming an actual scalar event leaves the counted child prefix intact,
for any symbolic event list and its genuine bounded event position. -/
theorem scalar_child_count_preserved (events : List Event) (eventIndex : ℕ)
    (eventBound : eventIndex<events.length) (group : GroupIndex)
    (eventEquation : events[eventIndex]=Event.scalar group) :
    (childNames (events.take (eventIndex+1))).length=(childNames (events.take eventIndex)).length := by
  rw [List.take_succ_eq_append_getElem eventBound,eventEquation,
    CompactComplexSourceReadyEventScheduleSemantics.childNames_append]
  simp only [childNames,List.length_append,List.length_nil,Nat.add_zero]

/-- The original scalar event changes neither the entry returned volume nor
its counted sibling contribution to the actual reached cursor. -/
theorem scalar_returned_cursor (entryReturned eventIndex childVolume : ℕ)
    (eventBound : eventIndex<schedule.length) (group : GroupIndex)
    (eventEquation : schedule[eventIndex]=Event.scalar group) :
    returnedCursor entryReturned (eventIndex+1) childVolume=returnedCursor entryReturned eventIndex childVolume := by
  unfold returnedCursor
  rw [scalar_child_count_preserved schedule eventIndex eventBound group eventEquation]

end
end IntegerMultBounds.Machine.CompactComplexActualReturnedOrdinal
