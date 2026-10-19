module

public import IntegerMultBounds.Networks.DAGReplay
public import IntegerMultBounds.Networks.DAGAllocatorBudget

/-! Count actual interned additions by their distinct supports. These bounds
connect replayed node lists to finite support-sharing certificates. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DAGReplayBudget

open DisjointCircuit DAGReplay

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def isAddition (node : Node α) : Bool :=
  match node.kind with | .input _ => false | .add _ _ => true

omit [DecidableEq α] in
theorem isAddition_iff (node : Node α) :
    isAddition node = true ↔ ∃ l r, node.kind = .add l r := by
  cases hk : node.kind <;> simp [isAddition, hk]

/-- Only actual addition nodes contribute to this support budget. -/
def additionSupports (nodes : List (Node α)) : Finset (Finset α) :=
  ((nodes.filter isAddition).map Node.support).toFinset

theorem mem_additionSupports (nodes : List (Node α)) (support : Finset α) :
    support ∈ additionSupports nodes ↔ AdditionSupport nodes support := by
  simp only [additionSupports, List.mem_toFinset, List.mem_map, List.mem_filter,
    isAddition_iff, AdditionSupport]
  aesop

/-- Interning makes every counted addition occupy exactly one support. -/
theorem additionSupports_card (nodes : List (Node α)) (hn : (nodes.map Node.support).Nodup) :
    (additionSupports nodes).card = DAGAllocator.additionCount nodes := by
  have hf := hn.sublist (List.filter_sublist.map Node.support :
    ((nodes.filter isAddition).map Node.support).Sublist _)
  rw [additionSupports, List.toFinset_card_of_nodup hf, List.length_map,
    ← List.countP_eq_length_filter]
  rfl

theorem additions_le_card (nodes : List (Node α)) (budget : Finset (Finset α))
    (hn : (nodes.map Node.support).Nodup) (hs : additionSupports nodes ⊆ budget) :
    DAGAllocator.additionCount nodes ≤ budget.card := by
  rw [← additionSupports_card nodes hn]
  exact Finset.card_le_card hs

end IntegerMultBounds.Networks.DAGReplayBudget
