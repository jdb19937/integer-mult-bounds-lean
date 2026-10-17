module

public import IntegerMultBounds.Networks.DAGAllocatorBudget

/-! Generic finite sets of allocated addition identifiers. Counting and index
bounds depend only on the node list, independently of any concrete certificate. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DAGAdditionIds

open DisjointCircuit

/-- Input nodes are excluded from the sharing-allocation count. -/
def isAddition {ι : Type*} (node : Node ι) : Bool :=
  match node.kind with | .input _ => false | .add _ _ => true

theorem isAddition_iff {ι : Type*} (node : Node ι) :
    isAddition node = true ↔ ∃ l r, node.kind = .add l r := by
  cases hk : node.kind <;> simp [isAddition, hk]

/-- The identifiers of actual addition nodes in their literal topological list. -/
def additionIds {ι : Type*} (nodes : List (Node ι)) : Finset ℕ :=
  ((nodes.zipIdx.filter (fun row => isAddition row.1)).map Prod.snd).toFinset

theorem mem_additionIds {ι : Type*} (nodes : List (Node ι)) (i : ℕ) :
    i ∈ additionIds nodes ↔ ∃ node, nodes[i]? = some node ∧ ∃ l r, node.kind = .add l r := by
  simp only [additionIds, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨node,j⟩, ⟨hm, ha⟩, he⟩
    change j = i at he
    subst j
    exact ⟨node, List.mk_mem_zipIdx_iff_getElem?.mp hm, (isAddition_iff node).mp ha⟩
  · rintro ⟨node, hm, ha⟩
    exact ⟨(node,i), ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hm, (isAddition_iff node).mpr ha⟩, rfl⟩

theorem additionIds_bound {ι : Type*} (nodes : List (Node ι)) (i : ℕ) (hi : i ∈ additionIds nodes) :
    i < nodes.length := by
  obtain ⟨node, hn, _⟩ := (mem_additionIds nodes i).mp hi
  exact (List.getElem?_eq_some_iff.mp hn).1

/-- Counting filtered unique indices is exactly counting addition records. -/
theorem additionIds_card {ι : Type*} (nodes : List (Node ι)) :
    (additionIds nodes).card = DAGAllocator.additionCount nodes := by
  have hn : ((nodes.zipIdx).map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hf := hn.sublist (List.filter_sublist.map Prod.snd :
    ((nodes.zipIdx.filter (fun row => isAddition row.1)).map Prod.snd).Sublist _)
  rw [additionIds, List.toFinset_card_of_nodup hf, List.length_map, ← List.countP_eq_length_filter]
  change (nodes.zipIdx.countP (isAddition ∘ Prod.fst)) = nodes.countP isAddition
  rw [← List.countP_map, List.zipIdx_map_fst]

private theorem countP_active_zipIdx {ι : Type*} (nodes : List (Node ι))
    (active : Finset ℕ) (offset : ℕ) :
    (nodes.zipIdx offset).countP (fun row => isAddition row.1 && decide (row.2 ∈ active)) =
      DisjointPruning.additionCountFrom offset active nodes := by
  induction nodes generalizing offset with
  | nil => simp [DisjointPruning.additionCountFrom]
  | cons node nodes ih =>
    simp only [List.zipIdx_cons, List.countP_cons, ih, DisjointPruning.additionCountFrom]
    cases hk : node.kind <;> by_cases hm : offset ∈ active <;> simp [isAddition, hk, hm, Nat.add_comm]

/-- Live addition counting is ordinary finite-set intersection cardinality.
This exposes mathlib's disjoint-union tools for composing pruning credits. -/
theorem additionCountFrom_eq_inter_card {ι : Type*} (nodes : List (Node ι)) (active : Finset ℕ) :
    DisjointPruning.additionCountFrom 0 active nodes = (additionIds nodes ∩ active).card := by
  let p := fun row : Node ι × ℕ => isAddition row.1 && decide (row.2 ∈ active)
  have hn : ((nodes.zipIdx).map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hf := hn.sublist (List.filter_sublist.map Prod.snd :
    ((nodes.zipIdx.filter p).map Prod.snd).Sublist _)
  have he : (((nodes.zipIdx.filter p).map Prod.snd).toFinset) = additionIds nodes ∩ active := by
    ext i
    simp only [additionIds, List.mem_toFinset, List.mem_map, List.mem_filter, Finset.mem_inter,
      p, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨row, ⟨hrow, hadd, hactive⟩, rfl⟩
      exact ⟨⟨row, ⟨hrow, hadd⟩, rfl⟩, hactive⟩
    · rintro ⟨⟨row, ⟨hrow, hadd⟩, rfl⟩, hactive⟩
      exact ⟨row, ⟨hrow, hadd, hactive⟩, rfl⟩
  rw [← he, List.toFinset_card_of_nodup hf, List.length_map, ← List.countP_eq_length_filter]
  exact (countP_active_zipIdx nodes active 0).symm

/-- A family of distinct, actual addition identifiers earns exactly its
cardinality as a pruning credit; aliases are collapsed by the finite set. -/
theorem additionCountFrom_eq_card {ι : Type*} (nodes : List (Node ι)) (active : Finset ℕ)
    (hs : active ⊆ additionIds nodes) :
    DisjointPruning.additionCountFrom 0 active nodes = active.card := by
  rw [additionCountFrom_eq_inter_card, Finset.inter_eq_right.mpr hs]

end IntegerMultBounds.Networks.DAGAdditionIds
