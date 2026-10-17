module

public import IntegerMultBounds.Networks.PairedCircuitBudget
public import IntegerMultBounds.Networks.PairedInitialGraph
import IntegerMultBounds.Networks.DAGInstructionCount
import IntegerMultBounds.Networks.DisjointPruningBudget
public import IntegerMultBounds.Networks.DAGSupportTrace
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient

/-! Certificate-free resource bounds for the literal paired construction.
Absent references denote zero and are omitted from the physical output list.
The structural budget is conservative; sharper addition bounds can be supplied
to the same compiler transfer theorems. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedInitialGraph

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator

def additionBudget (points : List ℕ) : ℕ :=
  PairedCircuitBudget.blockBudget points (pairs points).length points.length

theorem nodes_additionCount (points : List ℕ) : additionCount (nodes points) = 0 := by
  simp [nodes, additionCount, List.countP_map]

theorem circuit_additions_le (points : List ℕ) :
    additionCount (circuit points).nodes ≤ additionBudget points := by
  have h := PairedCircuitBudget.block_additions_le (nodes points) points
    (edges points) (weights points)
  simpa only [circuit, additionBudget, nodes_additionCount, Nat.zero_add, edges, weights, List.length_map,
    List.length_zipIdx] using h

/-- Enumerate the nonzero physical outputs in canonical pair order. -/
def outputRefs (points : List ℕ) : List ℕ :=
  (pairs points).filterMap (lookup (circuit points).two)

theorem outputRefs_length_le (points : List ℕ) :
    (outputRefs points).length ≤ (pairs points).length := List.length_filterMap_le _ _

theorem outputRefs_valid (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    ∀ i ∈ outputRefs points, i < (circuit points).nodes.length := by
  intro i hi
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hi
  have h := ((circuit_correct points hs).two p hp).1
  rw [he] at h
  exact h

/-- Pruning-aware entry point: a sharp bound only needs to count live additions,
including any savings established by a future structural pruning argument. -/
theorem compile_bounds_of_active (points : List ℕ) (hs : points.Pairwise (· < ·))
    (budget : ℕ)
    (hb : DisjointPruning.additionCountFrom 0
      (DisjointPruning.mark (circuit points).nodes (outputRefs points).toFinset)
      (circuit points).nodes ≤ budget) :
    (compile (circuit points).nodes (outputRefs points)).state.next ≤
        budget + (pairs points).length ∧
      (compile (circuit points).nodes (outputRefs points)).program.length ≤
        2 * budget + (pairs points).length := by
  have hr := DAGAllocator.compile_roles _ _ (circuit_correct points hs).valid
    (outputRefs_valid points hs)
  have hi := DAGAllocator.compile_program_count _ _ (circuit_correct points hs).valid
    (outputRefs_valid points hs)
  have ho := outputRefs_length_le points
  constructor <;> omega

/-- Structural dead-support families improve the actual paired compiler's
budget without unfolding the recursive circuit or its backwards traversal. -/
theorem compile_bounds_of_dead (points : List ℕ) (hs : points.Pairwise (· < ·))
    (dead : Finset ℕ) (capacity saved : ℕ)
    (hc : additionCount (circuit points).nodes ≤ capacity)
    (hd : ∀ i ∈ dead, ∀ r ∈ outputRefs points,
      ¬ DAGSupportTrace.nodeSupport (circuit points).nodes i ⊆
        DAGSupportTrace.nodeSupport (circuit points).nodes r)
    (hsaved : saved ≤ DisjointPruning.additionCountFrom 0 dead (circuit points).nodes) :
    (compile (circuit points).nodes (outputRefs points)).state.next ≤
        (capacity - saved) + (pairs points).length ∧
      (compile (circuit points).nodes (outputRefs points)).program.length ≤
        2 * (capacity - saved) + (pairs points).length := by
  apply compile_bounds_of_active points hs (capacity - saved)
  exact DisjointPruning.marked_additions_le_sub _ (circuit_correct points hs).valid _ dead
    (fun i hi r hr => hd i hi r (List.mem_toFinset.mp hr)) capacity saved hc hsaved

/-- Any improved addition bound transfers directly to allocated registers. -/
theorem compile_roles_le_of (points : List ℕ) (hs : points.Pairwise (· < ·))
    (budget : ℕ) (hb : additionCount (circuit points).nodes ≤ budget) :
    (compile (circuit points).nodes (outputRefs points)).state.next ≤
      budget + (pairs points).length := by
  have h := DAGAllocator.compile_roles_le _ _ (circuit_correct points hs).valid
    (outputRefs_valid points hs)
  have ho := outputRefs_length_le points
  omega

/-- Any improved addition bound transfers directly to emitted instructions. -/
theorem compile_instructions_le_of (points : List ℕ) (hs : points.Pairwise (· < ·))
    (budget : ℕ) (hb : additionCount (circuit points).nodes ≤ budget) :
    (compile (circuit points).nodes (outputRefs points)).program.length ≤
      2 * budget + (pairs points).length := by
  have h := DAGAllocator.compile_program_le_additions _ _ (circuit_correct points hs).valid
    (outputRefs_valid points hs)
  have ho := outputRefs_length_le points
  omega

theorem compile_roles_le (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    (compile (circuit points).nodes (outputRefs points)).state.next ≤
      additionBudget points + (pairs points).length :=
  compile_roles_le_of points hs _ (circuit_additions_le points)

theorem compile_instructions_le (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    (compile (circuit points).nodes (outputRefs points)).program.length ≤
      2 * additionBudget points + (pairs points).length :=
  compile_instructions_le_of points hs _ (circuit_additions_le points)

end IntegerMultBounds.Networks.PairedInitialGraph
