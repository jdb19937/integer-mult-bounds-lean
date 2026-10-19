module

public import IntegerMultBounds.Networks.DAGCompileCorrect
public import IntegerMultBounds.Networks.DAGAllocatorBudget

/-! Exact elementary XOR-instruction counts for the literal pruned DAG
compiler. These are lengths of actual scalar programs, not tape runtimes. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

variable {ι : Type*}

/-- A source gate has one fewer instruction than consumers, while an addition
has one instruction per consumer. Count the actual gather/scatter lists. -/
theorem allocate_program_count (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hc : consumers ≠ []) :
    (allocate state index node consumers).gate.program.length +
      (allocate state index node consumers).source.toList.length = consumers.length := by
  have hp := List.length_pos_iff.mpr hc
  cases node with
  | mk kind support =>
    cases kind <;>
      simp [allocate, Gate.program, ReversibleFanout.gather, ReversibleFanout.scatter] <;> omega

/-- Sum the literal emitted instruction and source lists: together they account
for every actual consumer exactly once. -/
theorem compileFrom_program_count (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hlive : ∀ i ∈ active, users all active outputs i ≠ []) :
    (compileFrom all active outputs state offset nodes).program.length +
      (compileFrom all active outputs state offset nodes).sources.length =
      usesFrom all active outputs offset nodes := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom, Code.program, usesFrom]
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · have hh := ih (allocate state offset node (users all active outputs offset)).state (offset+1)
      have hc := allocate_program_count state offset node _ (hlive offset ha)
      simp only [compileFrom, ha, ↓reduceIte, Code.program, List.flatMap_cons,
        List.length_append, List.length_map, usesFrom] at hh ⊢
      omega
    · simpa only [compileFrom, ha, ↓reduceIte, usesFrom, zero_add] using ih state (offset+1)

variable [DecidableEq ι]

/-- Exact scalar cost of the actual compiled DAG, including repeated requested
outputs: instructions plus actual source entries equal twice the number of
active additions plus the number of requested outputs. -/
theorem compile_program_count (nodes : List (Node ι)) (outputs : List ℕ)
    (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length) :
    (compile nodes outputs).program.length + (compile nodes outputs).sources.length =
      2 * DisjointPruning.additionCountFrom 0 (DisjointPruning.mark nodes outputs.toFinset) nodes +
        outputs.length := by
  have hh := compileFrom_program_count nodes (DisjointPruning.mark nodes outputs.toFinset)
    outputs ⟨0,[]⟩ 0 nodes (fun i hi => users_mark_nonempty nodes outputs i hi)
  rw [marked_uses_count nodes outputs hv ho] at hh
  exact hh

/-- A certificate's total addition count bounds the actual scalar program even
when backward pruning discards dead certificate nodes. -/
theorem compile_program_le_additions (nodes : List (Node ι)) (outputs : List ℕ)
    (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length) :
    (compile nodes outputs).program.length ≤ 2 * additionCount nodes + outputs.length := by
  have hh := compile_program_count nodes outputs hv ho
  have hm := marked_additions_le nodes (DisjointPruning.mark nodes outputs.toFinset) 0
  omega

end IntegerMultBounds.Networks.DAGAllocator
