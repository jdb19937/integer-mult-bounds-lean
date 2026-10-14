module

public import IntegerMultBounds.Machine.CompactComplexActualEventTrace
public import IntegerMultBounds.Machine.CompactComplexScheduledPCLayout
public import IntegerMultBounds.Machine.CompactComplexSourceReadyEventScheduleSemantics
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.FinRange

/-! Every literal child event has its original site-major residual-coordinate
ordinal. This connects actual processed schedule calls to the dependency
counter used by sibling child entry, rather than assuming their equality. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualCallOrdinal
noncomputable section
open Networks.ComplexRecursiveCallSchema (Call Occurrence callsAt calls callsAtFor callsFor)
open CompactComplexActualEventTrace (siteCalls)
open CompactComplexCompletedLiveLower (Event schedule childNames)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites schedule

section Generic
open Networks.ComplexRecursiveCallSchema (CallFor)
open Networks.ComplexPhaseRowSchedule (Edge dimension)
variable (siteList : List Edge)
local instance : DecidableEq (CallFor siteList) := Classical.typeDecidableEq _

private theorem callsAtFor_nodup (site : Fin siteList.length) : (callsAtFor siteList site).Nodup := by
  unfold callsAtFor
  apply List.nodup_ofFn_ofInjective
  intro firstCoordinate secondCoordinate callEquation
  have valueEquation := congrArg (fun call => call.coordinate.val) callEquation
  exact Fin.ext valueEquation

/-- Abstract site lists keep dependent row indices symbolic during kernel
verification; specialization never enumerates the original finite program. -/
theorem callsFor_idxOf (call : CallFor siteList) :
    (callsFor siteList).idxOf call=
      ((List.ofFn (fun site : Fin siteList.length => dimension siteList[site.val])).take call.site.val).sum+
        call.coordinate.val := by
  classical
  let siteBlocks := List.ofFn (callsAtFor siteList)
  have siteBound : call.site.val<siteBlocks.length := by
    simpa only [siteBlocks,List.length_ofFn] using call.site.isLt
  have siteDrop := List.drop_eq_getElem_cons siteBound
  simp only [siteBlocks,List.getElem_ofFn] at siteDrop
  have wholeSplit := congrArg List.flatten (List.take_append_drop call.site.val siteBlocks)
  rw [List.flatten_append,siteDrop,List.flatten_cons] at wholeSplit
  change (siteBlocks.take call.site.val).flatten++
    (callsAtFor siteList call.site++(siteBlocks.drop (call.site.val+1)).flatten)=callsFor siteList at wholeSplit
  have callMember : call∈callsAtFor siteList call.site := List.mem_ofFn.mpr ⟨call.coordinate,rfl⟩
  have prefixDisjoint : List.Disjoint (siteBlocks.take call.site.val).flatten
      (callsAtFor siteList call.site++(siteBlocks.drop (call.site.val+1)).flatten) := by
    apply List.Nodup.disjoint
    rw [wholeSplit]
    exact CompactComplexScheduledPCLayout.callsFor_nodup siteList
  have callNotPrefix : call∉(siteBlocks.take call.site.val).flatten := by
    intro prefixMember
    exact List.disjoint_left.mp prefixDisjoint prefixMember (List.mem_append_left _ callMember)
  let coordinateIndex : Fin (callsAtFor siteList call.site).length :=
    ⟨call.coordinate.val,by simpa only [callsAtFor,List.length_ofFn] using call.coordinate.isLt⟩
  have coordinateEntry : (callsAtFor siteList call.site)[coordinateIndex.val]=call := by
    simp only [callsAtFor,List.getElem_ofFn,coordinateIndex]
  have localOrdinal := (callsAtFor_nodup siteList call.site).idxOf_getElem coordinateIndex coordinateIndex.isLt
  rw [coordinateEntry] at localOrdinal
  have blockLengths : siteBlocks.map List.length=
      List.ofFn (fun site : Fin siteList.length => dimension siteList[site.val]) := by
    simp only [siteBlocks,List.map_ofFn]
    congr 1
    funext site
    simp only [Function.comp_apply,callsAtFor,List.length_ofFn]
  have prefixLength : (siteBlocks.take call.site.val).flatten.length=
      ((List.ofFn (fun site : Fin siteList.length => dimension siteList[site.val])).take call.site.val).sum := by
    rw [List.length_flatten,List.map_take,blockLengths]
  rw [←wholeSplit,List.idxOf_append_of_notMem callNotPrefix,
    List.idxOf_append_of_mem callMember,localOrdinal,prefixLength]

end Generic

local instance : DecidableEq Call := Classical.typeDecidableEq _

theorem callsAt_nodup (site : Occurrence) : (callsAt site).Nodup :=
  callsAtFor_nodup Networks.ComplexRecursiveCallSchema.sites site

theorem calls_nodup : calls.Nodup :=
  CompactComplexScheduledPCLayout.actual_calls_nodup

/-- The original call ordinal is a specialization of the symbolic site-list
proof, retaining the actual precedingCalls definition. -/
theorem calls_idxOf (call : Call) : calls.idxOf call=CompactRecursiveDependencyBudget.precedingCalls call := by
  exact callsFor_idxOf Networks.ComplexRecursiveCallSchema.sites call

/-- Generic event lists keep the prefix-index calculation independent of
any concrete compiler schedule or its enormous closed call enumeration. -/
private theorem child_prefix_idxOf (events : List Event) (childrenNodup : (childNames events).Nodup)
    (eventIndex : ℕ) (eventBound : eventIndex<events.length)
    (call : Call) (eventEquation : events[eventIndex]=Event.child call) :
    (childNames (events.take eventIndex)).length=(childNames events).idxOf call := by
  classical
  have eventDrop := List.drop_eq_getElem_cons eventBound
  rw [eventEquation] at eventDrop
  have eventSplit := List.take_append_drop eventIndex events
  rw [eventDrop] at eventSplit
  have callSplit := congrArg childNames eventSplit
  rw [CompactComplexSourceReadyEventScheduleSemantics.childNames_append] at callSplit
  simp only [childNames] at callSplit
  have prefixDisjoint : List.Disjoint (childNames (events.take eventIndex))
      (call::childNames (events.drop (eventIndex+1))) := by
    apply List.Nodup.disjoint
    rw [callSplit]
    exact childrenNodup
  have callNotPrefix : call∉childNames (events.take eventIndex) := by
    intro prefixMember
    exact List.disjoint_left.mp prefixDisjoint prefixMember List.mem_cons_self
  rw [←callSplit,List.idxOf_append_of_notMem callNotPrefix,List.idxOf_cons_self,Nat.add_zero]

/-- Filtering an actual event prefix counts precisely the original call's
ordinal at its physical child event. No indexing premise remains. -/
theorem schedule_prefix_ordinal (eventIndex : ℕ) (eventBound : eventIndex<schedule.length)
    (call : Call) (eventEquation : schedule[eventIndex]=Event.child call) :
    (childNames (schedule.take eventIndex)).length=CompactRecursiveDependencyBudget.precedingCalls call := by
  have prefixIndex := child_prefix_idxOf schedule CompactComplexScheduledPCLayout.schedule_children_nodup
    eventIndex eventBound call eventEquation
  rw [CompactComplexCompletedLiveLower.schedule_calls] at prefixIndex
  exact prefixIndex.trans (calls_idxOf call)

end
end IntegerMultBounds.Machine.CompactComplexActualCallOrdinal
