module

public import IntegerMultBounds.Networks.DAGAllocatorBudget
public import IntegerMultBounds.Networks.DAGSupportTrace
import IntegerMultBounds.Networks.DAGValueTransfer
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient

/-! Compositional pruning budgets. A stored sum that cannot fit inside any
requested output support is dead, regardless of the shape of the DAG or the
amount of support interning. Certified dead additions can be subtracted from
any constructor budget without evaluating the backward marking pass. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DisjointPruning

open DisjointCircuit DAGSupportTrace

variable {ι : Type*}

/-- Any property inherited by parents propagates through backwards marking. -/
theorem markFrom_property (offset : ℕ) (nodes : List (Node ι)) (roots : Finset ℕ)
    (P : ℕ → Prop) (hr : ∀ i ∈ roots, P i)
    (hp : ∀ j (hj : j < nodes.length), ∀ p ∈ parents nodes[j], P (offset + j) → P p) :
    ∀ i ∈ markFrom offset nodes roots, P i := by
  induction nodes generalizing offset with
  | nil => exact hr
  | cons node nodes ih =>
    have ht := ih (offset + 1) (fun j hj p hmem h => by
      have h' := hp (j + 1) (by simp; omega) p (by simpa using hmem)
      exact h' (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h))
    simp only [markFrom]
    split_ifs with hm
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ht i hi
      · exact hp 0 (by simp) i hi (by simpa using ht offset hm)
    · exact ht

variable [DecidableEq ι]

/-- Each parent's support is contained in its child's support. -/
theorem parent_support_subset (nodes : List (Node ι)) (hv : Valid nodes)
    (j : ℕ) (hj : j < nodes.length) (p : ℕ) (hp : p ∈ parents nodes[j]) :
    nodeSupport nodes p ⊆ nodeSupport nodes j := by
  rw [nodeSupport_get nodes j hj]
  cases hk : nodes[j].kind with
  | input a => simp [parents, hk] at hp
  | add l r =>
    simp only [parents, hk, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact nodeSupport_parent nodes hv j hj (p, .gate j false) (by
        simp [DAGAllocator.parentPorts, hk])
    · exact nodeSupport_parent nodes hv j hj (p, .gate j true) (by
        simp [DAGAllocator.parentPorts, hk])

/-- Every live sum fits inside at least one requested output support. -/
theorem marked_support_subset (nodes : List (Node ι)) (hv : Valid nodes)
    (roots : Finset ℕ) (i : ℕ) (hi : i ∈ mark nodes roots) :
    ∃ r ∈ roots, nodeSupport nodes i ⊆ nodeSupport nodes r := by
  apply markFrom_property 0 nodes roots
    (fun i => ∃ r ∈ roots, nodeSupport nodes i ⊆ nodeSupport nodes r) ?_ ?_ i hi
  · intro r hr
    exact ⟨r, hr, Finset.Subset.refl _⟩
  · intro j hj p hp h
    obtain ⟨r, hr, hs⟩ := h
    exact ⟨r, hr, (parent_support_subset nodes hv j hj p hp).trans (by simpa using hs)⟩

/-- A support obstruction proves deadness without replaying the marking pass. -/
theorem not_marked_of_support (nodes : List (Node ι)) (hv : Valid nodes)
    (roots : Finset ℕ) (i : ℕ)
    (h : ∀ r ∈ roots, ¬ nodeSupport nodes i ⊆ nodeSupport nodes r) :
    i ∉ mark nodes roots := by
  intro hi
  obtain ⟨r, hr, hs⟩ := marked_support_subset nodes hv roots i hi
  exact h r hr hs

/-- An unrequested node with no actual users is dead. Unlike support
obstructions, this also handles unused intermediate totals that fit inside an
output's support but are never referenced by its construction. -/
theorem not_marked_of_unused (nodes : List (Node ι)) (hv : Valid nodes)
    (roots : Finset ℕ) (i : ℕ) (hr : i ∉ roots)
    (hu : ∀ j (hj : j < nodes.length), i < j → i ∉ parents nodes[j]) :
    i ∉ mark nodes roots := by
  intro hm
  have h := markFrom_property 0 nodes roots (fun j => j ≠ i)
    (fun j hj he => hr (he ▸ hj)) (by
      intro j hj p hp _ he
      subst p
      have hn := DAGValueTransfer.validFrom_get [] nodes hv j hj
      have hlt := parents_lt ([] ++ (nodes.take j).map Node.support) nodes[j] hn i hp
      have hij : i < j := by
        simpa only [List.length_append, List.length_nil, List.length_map,
          List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), Nat.zero_add] using hlt
      exact hu j hj hij hp) i hm
  exact h rfl

omit [DecidableEq ι] in
/-- Live and certified-dead additions consume disjoint parts of the same budget. -/
theorem additionCountFrom_add_le (offset : ℕ) (nodes : List (Node ι))
    (active dead : Finset ℕ) (hd : Disjoint active dead) :
    additionCountFrom offset active nodes + additionCountFrom offset dead nodes ≤
      DAGAllocator.additionCount nodes := by
  induction nodes generalizing offset with
  | nil => simp [additionCountFrom, DAGAllocator.additionCount]
  | cons node nodes ih =>
    have ht := ih (offset + 1)
    have hx : ¬ (offset ∈ active ∧ offset ∈ dead) := by
      intro h
      exact Finset.disjoint_left.mp hd h.1 h.2
    cases node with
    | mk kind support =>
      cases kind <;>
        simp only [additionCountFrom, DAGAllocator.additionCount, List.countP_cons] at ht ⊢
      all_goals split_ifs <;> simp_all <;> omega

/-- Subtract any proved family of support-obstructed additions from an existing
allocation bound. Sharing is already accounted for by counting actual nodes. -/
theorem marked_additions_le_sub (nodes : List (Node ι)) (hv : Valid nodes)
    (roots dead : Finset ℕ)
    (hd : ∀ i ∈ dead, ∀ r ∈ roots, ¬ nodeSupport nodes i ⊆ nodeSupport nodes r)
    (capacity saved : ℕ) (hc : DAGAllocator.additionCount nodes ≤ capacity)
    (hs : saved ≤ additionCountFrom 0 dead nodes) :
    additionCountFrom 0 (mark nodes roots) nodes ≤ capacity - saved := by
  have hdis : Disjoint (mark nodes roots) dead := by
    apply Finset.disjoint_left.mpr
    intro i hi hd'
    exact not_marked_of_support nodes hv roots i (hd i hd') hi
  have h := additionCountFrom_add_le 0 nodes (mark nodes roots) dead hdis
  omega

omit [DecidableEq ι] in
theorem additionCountFrom_mono (offset : ℕ) (nodes : List (Node ι))
    (active larger : Finset ℕ) (hs : active ⊆ larger) :
    additionCountFrom offset active nodes ≤ additionCountFrom offset larger nodes := by
  induction nodes generalizing offset with
  | nil => simp [additionCountFrom]
  | cons node nodes ih =>
    simp only [additionCountFrom]
    apply Nat.add_le_add _ (ih (offset + 1))
    by_cases ha : offset ∈ active
    · simp [ha, hs ha]
    · simp [ha]

omit [DecidableEq ι] in
/-- A parent-closed envelope may be proved structurally at a recursive boundary;
there is no need to enumerate the exact transitive closure. -/
theorem marked_additions_le_of_closed (nodes : List (Node ι)) (roots active : Finset ℕ)
    (hr : roots ⊆ active) (hc : ClosedFrom 0 active nodes)
    (budget : ℕ) (hb : additionCountFrom 0 active nodes ≤ budget) :
    additionCountFrom 0 (mark nodes roots) nodes ≤ budget := by
  exact (additionCountFrom_mono 0 nodes _ active
    (markFrom_subset 0 nodes roots active hr hc)).trans hb

omit [DecidableEq ι] in
/-- Backwards marking composes across construction stages. The later stage
supplies exactly the roots needed by the earlier stage. -/
theorem markFrom_append (offset : ℕ) (before after : List (Node ι)) (roots : Finset ℕ) :
    markFrom offset (before ++ after) roots =
      markFrom offset before (markFrom (offset + before.length) after roots) := by
  induction before generalizing offset with
  | nil => simp [markFrom]
  | cons node before ih =>
    simp [markFrom, ih, Nat.add_assoc, Nat.add_comm]

omit [DecidableEq ι] in
theorem additionCountFrom_append (offset : ℕ) (before after : List (Node ι))
    (active : Finset ℕ) :
    additionCountFrom offset active (before ++ after) =
      additionCountFrom offset active before +
        additionCountFrom (offset + before.length) active after := by
  induction before generalizing offset with
  | nil => simp [additionCountFrom]
  | cons node before ih =>
    simp [additionCountFrom, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq ι] in
/-- Split the live budget at any recursive construction boundary. The tail
contains only genuinely allocated nodes; reused references remain in the prefix. -/
theorem additionCountFrom_split (nodes : List (Node ι)) (active : Finset ℕ)
    (cut : ℕ) (hc : cut ≤ nodes.length) :
    additionCountFrom 0 active nodes =
      additionCountFrom 0 active (nodes.take cut) +
        additionCountFrom cut active (nodes.drop cut) := by
  have h := additionCountFrom_append 0 (nodes.take cut) (nodes.drop cut) active
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hc, Nat.zero_add] using h

end IntegerMultBounds.Networks.DisjointPruning
