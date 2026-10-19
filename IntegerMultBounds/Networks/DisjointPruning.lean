module

public import IntegerMultBounds.Networks.DisjointCircuit

/-! Execution with inactive DAG nodes omitted. A backwards pass computes the
actual ancestors of the requested outputs. The execution keeps node indices
stable using zero placeholders; only marked addition nodes perform additions.
This is an array execution theorem, not a tape-space allocation theorem. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DisjointPruning

open DisjointCircuit

variable {ι A : Type*}

/-- Direct dependencies of a node. -/
def parents (node : Node ι) : Finset ℕ :=
  match node.kind with
  | .input _ => ∅
  | .add l r => {l, r}

/-- Mark ancestors by a single backwards pass through the topological list. -/
def markFrom (offset : ℕ) : List (Node ι) → Finset ℕ → Finset ℕ
  | [], roots => roots
  | node :: nodes, roots =>
    let marked := markFrom (offset + 1) nodes roots
    if offset ∈ marked then marked ∪ parents node else marked

def mark (nodes : List (Node ι)) (roots : Finset ℕ) : Finset ℕ :=
  markFrom 0 nodes roots

/-- Every marked node has all its parents marked. -/
def ClosedFrom (offset : ℕ) (active : Finset ℕ) : List (Node ι) → Prop
  | [] => True
  | node :: nodes =>
    (offset ∈ active → parents node ⊆ active) ∧ ClosedFrom (offset + 1) active nodes

theorem roots_subset_markFrom (offset : ℕ) (nodes : List (Node ι)) (roots : Finset ℕ) :
    roots ⊆ markFrom offset nodes roots := by
  induction nodes generalizing offset with
  | nil => exact Finset.Subset.refl _
  | cons node nodes ih =>
    simp only [markFrom]
    split_ifs
    · exact (ih _).trans Finset.subset_union_left
    · exact ih _

variable [DecidableEq ι]

theorem parents_lt (prior : List (Finset ι)) (node : Node ι) (hv : node.Valid prior)
    (p : ℕ) (hp : p ∈ parents node) : p < prior.length := by
  cases node with
  | mk kind support =>
    cases kind with
    | input i => simp [parents] at hp
    | add l r =>
      simp only [Node.Valid] at hv
      split at hv
      next hl =>
        split at hv
        next hr =>
          simp only [parents, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> assumption
        next => contradiction
      next => contradiction

omit [DecidableEq ι] in
/-- Adding indices strictly before a suffix does not activate any new nodes
in that suffix. -/
theorem closedFrom_union_earlier (offset : ℕ) (nodes : List (Node ι))
    (active extra : Finset ℕ) (hc : ClosedFrom offset active nodes)
    (he : ∀ i ∈ extra, i < offset) : ClosedFrom offset (active ∪ extra) nodes := by
  induction nodes generalizing offset with
  | nil => trivial
  | cons node nodes ih =>
    obtain ⟨hn, ht⟩ := hc
    constructor
    · intro ha
      have ha' : offset ∈ active := by
        rcases Finset.mem_union.mp ha with h | h
        · exact h
        · have := he offset h; omega
      exact (hn ha').trans Finset.subset_union_left
    · exact ih (offset + 1) ht (fun i hi => by have := he i hi; omega)

/-- For a valid DAG, the computed backwards marking is parent closed. -/
theorem markFrom_closed (prior : List (Finset ι)) (nodes : List (Node ι))
    (roots : Finset ℕ) (hv : ValidFrom prior nodes) :
    ClosedFrom prior.length (markFrom prior.length nodes roots) nodes := by
  induction nodes generalizing prior with
  | nil => trivial
  | cons node nodes ih =>
    obtain ⟨hn, ht⟩ := hv
    have hi := ih (prior ++ [node.support]) ht
    simp only [List.length_append, List.length_singleton] at hi
    change (prior.length ∈ markFrom prior.length (node :: nodes) roots →
      parents node ⊆ markFrom prior.length (node :: nodes) roots) ∧ _
    simp only [markFrom]
    split_ifs with ha
    · constructor
      · intro _; exact Finset.subset_union_right
      · exact closedFrom_union_earlier _ _ _ _ hi
          (fun i hi => by have := parents_lt prior node hn i hi; omega)
    · exact ⟨fun h => False.elim (ha h), hi⟩

section Execution
variable [AddCommMonoid A]

/-- Equality of the stored values at the active indices, including absent
indices. The latter makes the evaluator total even for malformed DAGs. -/
def Agree (active : Finset ℕ) (xs ys : List A) : Prop :=
  ∀ i ∈ active, xs[i]? = ys[i]?

/-- Execute only marked nodes, retaining zero placeholders for the others. -/
def evalFrom (active : Finset ℕ) (input : ι → A) : List A → List (Node ι) → List A
  | prior, [] => prior
  | prior, node :: nodes =>
    let value := if prior.length ∈ active then node.eval input prior else 0
    evalFrom active input (prior ++ [value]) nodes

def eval (active : Finset ℕ) (input : ι → A) (nodes : List (Node ι)) : List A :=
  evalFrom active input [] nodes

end Execution

/-- The exact number of additions performed by marked execution. Input
copies and skipped nodes do not contribute to this arithmetic count. -/
def additionCountFrom (offset : ℕ) (active : Finset ℕ) : List (Node ι) → ℕ
  | [] => 0
  | node :: nodes =>
    (if offset ∈ active then match node.kind with | .input _ => 0 | .add _ _ => 1 else 0) +
      additionCountFrom (offset + 1) active nodes

/-- Instrumented execution counts precisely the additions it performs. -/
def runFrom [AddCommMonoid A] (active : Finset ℕ) (input : ι → A) :
    List A → List (Node ι) → List A × ℕ
  | prior, [] => (prior, 0)
  | prior, node :: nodes =>
    let value := if prior.length ∈ active then node.eval input prior else 0
    let cost := if prior.length ∈ active then
      match node.kind with | .input _ => 0 | .add _ _ => 1 else 0
    let rest := runFrom active input (prior ++ [value]) nodes
    (rest.1, cost + rest.2)

end IntegerMultBounds.Networks.DisjointPruning
