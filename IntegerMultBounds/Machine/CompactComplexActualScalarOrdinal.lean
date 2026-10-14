module

public import IntegerMultBounds.Machine.CompactComplexScheduledPCLayout
public import Mathlib.Data.List.FinRange

/-! Actual scalar events have their original group ordinal. Generic symbolic
assembly and prefix proofs avoid expanding the closed compiler schedule, and
the resulting equality initializes each real scalar-prefix readiness step. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal
noncomputable section
open CompactComplexScalarIntegerRows (GroupIndex)
open CompactComplexCompletedLiveLower (Event groups schedule assembleWith assemble groupCalls)
attribute [local irreducible] Networks.ComplexRank25.program groups schedule

/-- Reuse the original scalar-group filter from the actual PC layout. -/
abbrev scalarGroups := CompactComplexScheduledPCLayout.scalarGroups

theorem scalarGroups_append (eventPrefix eventSuffix : List Event) :
    scalarGroups (eventPrefix++eventSuffix)=scalarGroups eventPrefix++scalarGroups eventSuffix := by
  induction eventPrefix with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
    cases event <;> simp only [List.cons_append,scalarGroups,
      CompactComplexScheduledPCLayout.scalarGroups,inductionHypothesis,List.cons_append]

theorem scalarGroups_children (calls : List Networks.ComplexRecursiveCallSchema.Call) :
    scalarGroups (calls.map Event.child)=[] := by
  induction calls with
  | nil => rfl
  | cons call remaining inductionHypothesis => exact inductionHypothesis

/-- Generic symbolic assembly retains each original scalar group once and
in order, regardless of the sizes of interleaved child-call intervals. -/
theorem assemble_scalarGroups (childCount : GroupIndex → ℕ) (groupList : List GroupIndex)
    (calls : List Networks.ComplexRecursiveCallSchema.Call) :
    scalarGroups (assembleWith childCount groupList calls)=groupList := by
  induction groupList generalizing calls with
  | nil => exact scalarGroups_children calls
  | cons group remaining inductionHypothesis =>
    rw [assembleWith,scalarGroups_append,scalarGroups_children]
    exact congrArg (List.cons group) (inductionHypothesis (calls.drop (childCount group)))

theorem schedule_scalarGroups : scalarGroups schedule=groups := by
  unfold schedule assemble
  exact assemble_scalarGroups groupCalls groups Networks.ComplexRecursiveCallSchema.calls

theorem schedule_scalarGroups_nodup : (scalarGroups schedule).Nodup := by
  rw [schedule_scalarGroups]
  unfold groups
  exact List.nodup_ofFn_ofInjective Function.injective_id

private theorem ofFn_idxOf (size : ℕ) (index : Fin size) :
    (List.ofFn (id : Fin size → Fin size)).idxOf index=index.val := by
  have indexBound : index.val<(List.ofFn (id : Fin size → Fin size)).length := by
    simpa only [List.length_ofFn] using index.isLt
  have indicesNodup : (List.ofFn (id : Fin size → Fin size)).Nodup :=
    List.nodup_ofFn_ofInjective Function.injective_id
  have indexEquation := indicesNodup.idxOf_getElem index.val indexBound
  simpa only [List.getElem_ofFn,id_eq,Fin.eta] using indexEquation

theorem groups_idxOf (group : GroupIndex) : groups.idxOf group=group.val := by
  unfold groups
  exact ofFn_idxOf _ group

/-- Prefix indexing is proved for symbolic event lists before specializing
to the actual schedule. Only local uniqueness of named scalar groups is used. -/
private theorem scalar_prefix_idxOf (events : List Event) (groupsNodup : (scalarGroups events).Nodup)
    (eventIndex : ℕ) (eventBound : eventIndex<events.length)
    (group : GroupIndex) (eventEquation : events[eventIndex]=Event.scalar group) :
    (scalarGroups (events.take eventIndex)).length=(scalarGroups events).idxOf group := by
  have eventDrop := List.drop_eq_getElem_cons eventBound
  rw [eventEquation] at eventDrop
  have eventSplit := List.take_append_drop eventIndex events
  rw [eventDrop] at eventSplit
  have groupSplit := congrArg scalarGroups eventSplit
  rw [scalarGroups_append] at groupSplit
  simp only [scalarGroups,CompactComplexScheduledPCLayout.scalarGroups] at groupSplit
  change scalarGroups (events.take eventIndex)++
    group::scalarGroups (events.drop (eventIndex+1))=scalarGroups events at groupSplit
  have prefixDisjoint : List.Disjoint (scalarGroups (events.take eventIndex))
      (group::scalarGroups (events.drop (eventIndex+1))) := by
    apply List.Nodup.disjoint
    rw [groupSplit]
    exact groupsNodup
  have groupNotPrefix : group∉scalarGroups (events.take eventIndex) := by
    intro prefixMember
    exact List.disjoint_left.mp prefixDisjoint prefixMember List.mem_cons_self
  rw [←groupSplit,List.idxOf_append_of_notMem groupNotPrefix,List.idxOf_cons_self,Nat.add_zero]

/-- At the actual scalar event, the prefix's processed scalar-group count
is exactly the original group's value, with no supplied cursor equation. -/
theorem schedule_prefix_ordinal (eventIndex : ℕ) (eventBound : eventIndex<schedule.length)
    (group : GroupIndex) (eventEquation : schedule[eventIndex]=Event.scalar group) :
    (scalarGroups (schedule.take eventIndex)).length=group.val := by
  have prefixIndex := scalar_prefix_idxOf schedule schedule_scalarGroups_nodup
    eventIndex eventBound group eventEquation
  rw [schedule_scalarGroups] at prefixIndex
  exact prefixIndex.trans (groups_idxOf group)

/-- A real scalar event advances the counted scalar cursor by one. -/
theorem scalar_count_successor (events : List Event) (eventIndex : ℕ)
    (eventBound : eventIndex<events.length) (group : GroupIndex)
    (eventEquation : events[eventIndex]=Event.scalar group) :
    (scalarGroups (events.take (eventIndex+1))).length=(scalarGroups (events.take eventIndex)).length+1 := by
  rw [List.take_succ_eq_append_getElem eventBound,eventEquation,scalarGroups_append]
  simp only [scalarGroups,CompactComplexScheduledPCLayout.scalarGroups,List.length_append,
    List.length_cons,List.length_nil]

/-- A real child event preserves the counted scalar cursor. -/
theorem child_count_successor (events : List Event) (eventIndex : ℕ)
    (eventBound : eventIndex<events.length) (call : Networks.ComplexRecursiveCallSchema.Call)
    (eventEquation : events[eventIndex]=Event.child call) :
    (scalarGroups (events.take (eventIndex+1))).length=(scalarGroups (events.take eventIndex)).length := by
  rw [List.take_succ_eq_append_getElem eventBound,eventEquation,scalarGroups_append]
  simp only [scalarGroups,CompactComplexScheduledPCLayout.scalarGroups,List.length_append,
    List.length_nil,Nat.add_zero]

end
end IntegerMultBounds.Machine.CompactComplexActualScalarOrdinal
