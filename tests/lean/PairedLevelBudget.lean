module

import IntegerMultBounds.Networks.PairedInitialBudget
import IntegerMultBounds.Networks.DisjointPruningBudget

/-! Regression for one complete paired recursion (seven vertices to four).
Run with scripts/check-lean-safe.py. No generated DAG or witness rows are used.
The kernel checks the small boundary counts, and the generic stage-composition
and compiler theorems assemble the sharp result. Kept outside the default build
so this concrete computation does not add to normal incremental checking. -/

namespace IntegerMultBounds.Networks.PairedLevelBudgetTest

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator DisjointPruning

def points := List.range 7
def graph := PairedInitialGraph.circuit points
def roots := (PairedInitialGraph.outputRefs points).toFinset

def coarse : BlockResult PairedInitialGraph.Input :=
  let groups := PairGrouping.groups points
  let ce := coarseEdges (PairedInitialGraph.nodes points) groups (PairedInitialGraph.edges points)
  let cw := coarseWeights ce.1 groups (PairedInitialGraph.edges points) (PairedInitialGraph.weights points)
  block cw.1 (List.range groups.length) ce.2 cw.2

def cut := coarse.nodes.length

theorem allocated : additionCount graph.nodes = 108 := by decide +kernel

theorem recursive_boundary : cut = 57 := by decide +kernel

theorem cut_le : cut ≤ graph.nodes.length := by
  rw [recursive_boundary]
  decide +kernel

/-- The recursively constructed prefix contributes thirty live additions. -/
theorem recursive_live : additionCountFrom 0 (mark graph.nodes roots) (graph.nodes.take cut) = 30 := by
  rw [recursive_boundary]
  decide +kernel

/-- Reconstruction contributes sixty more, including reuse and discarded singles. -/
theorem reconstruction_live : additionCountFrom cut (mark graph.nodes roots) (graph.nodes.drop cut) = 60 := by
  rw [recursive_boundary]
  decide +kernel

theorem live_additions : additionCountFrom 0 (mark graph.nodes roots) graph.nodes = 90 := by
  rw [additionCountFrom_split graph.nodes (mark graph.nodes roots) cut cut_le,
    recursive_live, reconstruction_live]

theorem pruned_additions : additionCount graph.nodes -
    additionCountFrom 0 (mark graph.nodes roots) graph.nodes = 18 := by
  rw [allocated, live_additions]

/-- The small exact boundary counts suffice for the actual pruned compiler. -/
theorem compiled_bounds :
    (compile graph.nodes (PairedInitialGraph.outputRefs points)).state.next ≤ 111 ∧
    (compile graph.nodes (PairedInitialGraph.outputRefs points)).program.length ≤ 201 := by
  have h := PairedInitialGraph.compile_bounds_of_active points List.pairwise_lt_range 90
    live_additions.le
  have hlength : (pairs points).length = 21 := by decide +kernel
  simpa only [graph, hlength, Nat.reduceAdd, Nat.reduceMul] using h

end IntegerMultBounds.Networks.PairedLevelBudgetTest
