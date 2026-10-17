module

public import IntegerMultBounds.Networks.PairedIndexedGraph
public import IntegerMultBounds.Networks.PairedRename
public import IntegerMultBounds.Networks.PairedLocalPruning
public import IntegerMultBounds.Networks.PairedSingleBudget

/-! The finite-coordinate constructor is the pair-keyed constructor with its
input atoms relabeled. Live counts and pruning credits proved for the
pair-keyed graph therefore bound the pruned local circuit consumed by replay.
No concrete node list is evaluated. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedIndexedPruning

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect DisjointPruning

attribute [local irreducible] PairedIndexedGraph.circuit PairedInitialGraph.circuit

/-- Canonical pair labels of the finite source coordinates. -/
def pairEmbedding (n : ℕ) : Fin (n.choose 2) ↪ ℕ × ℕ :=
  ⟨PairMask.pairAt n, PairMask.pairAt_injective n⟩

theorem finRange_pairAt (n : ℕ) :
    (List.finRange (n.choose 2)).map (PairMask.pairAt n) = pairs (List.range n) := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp [PairMask.pairAt]

theorem nodes_map (n : ℕ) :
    (PairedIndexedGraph.nodes n).map (PairedRename.node (pairEmbedding n)) =
      PairedInitialGraph.nodes (List.range n) := by
  rw [PairedInitialGraph.nodes, ← finRange_pairAt]
  simp [PairedIndexedGraph.nodes, PairedRename.node, PairedRename.kind, pairEmbedding,
    Function.comp_def]

/-- Relabeling the finite-coordinate construction gives the pair-keyed one. -/
theorem circuit_map (n : ℕ) :
    PairedRename.block (pairEmbedding n) (PairedIndexedGraph.circuit n) =
      PairedInitialGraph.circuit (List.range n) := by
  rw [PairedIndexedGraph.circuit, PairedInitialGraph.circuit, ← nodes_map, PairedRename.block_map]

theorem circuit_nodes_map (n : ℕ) :
    (PairedIndexedGraph.circuit n).nodes.map (PairedRename.node (pairEmbedding n)) =
      (PairedInitialGraph.circuit (List.range n)).nodes :=
  congrArg BlockResult.nodes (circuit_map n)

theorem circuit_two (n : ℕ) :
    (PairedIndexedGraph.circuit n).two = (PairedInitialGraph.circuit (List.range n)).two :=
  congrArg BlockResult.two (circuit_map n)

theorem additionCount_eq (n : ℕ) :
    DAGAllocator.additionCount (PairedIndexedGraph.circuit n).nodes =
      DAGAllocator.additionCount (PairedInitialGraph.circuit (List.range n)).nodes := by
  rw [← circuit_nodes_map, PairedRename.additionCount_map]

/-- Every requested pair output of the finite-coordinate construction is present. -/
theorem lookup_some (n : ℕ) (hn : 4 ≤ n) (p : ℕ × ℕ) (hp : p ∈ pairs (List.range n)) :
    ∃ i, lookup (PairedIndexedGraph.circuit n).two p = some i := by
  have hs := (PairedIndexedGraph.circuit_pair_support n p hp).2
  cases he : lookup (PairedIndexedGraph.circuit n).two p with
  | none =>
    rw [he] at hs
    have hne := PairedIndexedGraph.exclusion_nonempty n hn p.1 p.2
    rw [← hs] at hne
    exact False.elim (Finset.not_nonempty_empty hne)
  | some i => exact ⟨i, rfl⟩

private theorem filterMap_eq_map {X Y : Type*} (f : X → Option Y) (g : X → Y) (xs : List X)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.filterMap f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, h x (by simp)]
    simp only [List.map_cons]
    exact congrArg _ (ih (fun y hy => h y (by simp [hy])))

theorem implementationOf_nodes (graph : BlockResult (Fin 1176)) (hvalid : Valid graph.nodes)
    (hnodup : (graph.nodes.map Node.support).Nodup)
    (hsupport : ∀ p ∈ pairs (List.range 49),
      RefSpec (MaskDAG.decode (PairMask.exclusion49 p.1 p.2)) graph.nodes (lookup graph.two p)) :
    (PairedIndexedGraph.implementationOf graph hvalid hnodup hsupport).nodes = graph.nodes := rfl

theorem implementationOf_outputs (graph : BlockResult (Fin 1176)) (hvalid : Valid graph.nodes)
    (hnodup : (graph.nodes.map Node.support).Nodup)
    (hsupport : ∀ p ∈ pairs (List.range 49),
      RefSpec (MaskDAG.decode (PairMask.exclusion49 p.1 p.2)) graph.nodes (lookup graph.two p)) :
    (PairedIndexedGraph.implementationOf graph hvalid hnodup hsupport).outputs =
      (pairs (List.range 49)).map (fun p => (p, (lookup graph.two p).getD 0)) := rfl

/-- Symbolic projections; the concrete constructor is never reduced. -/
theorem implementation49_nodes :
    PairedIndexedGraph.implementation49.nodes = (PairedIndexedGraph.circuit 49).nodes :=
  implementationOf_nodes _ _ _ _

theorem implementation49_outputs : PairedIndexedGraph.implementation49.outputs =
    (pairs (List.range 49)).map (fun p => (p, (lookup (PairedIndexedGraph.circuit 49).two p).getD 0)) :=
  implementationOf_outputs _ _ _ _

/-- The replayed roots are exactly the pair-keyed physical outputs. -/
theorem roots_eq : PairedIndexedGraph.implementation49.roots =
    (PairedInitialGraph.outputRefs (List.range 49)).toFinset := by
  rw [PairedLocalCircuit.roots, implementation49_outputs, PairedInitialGraph.outputRefs,
    ← circuit_two, filterMap_eq_map _ (fun p => (lookup (PairedIndexedGraph.circuit 49).two p).getD 0),
    List.map_map]
  · simp only [Function.comp_def]
  · intro p hp
    obtain ⟨i, hi⟩ := lookup_some 49 (by decide) p hp
    rw [hi]
    rfl

/-- The live count of the replayed local circuit is the pair-keyed live count. -/
theorem live_eq :
    additionCountFrom 0 PairedIndexedGraph.implementation49.live
        PairedIndexedGraph.implementation49.nodes =
      additionCountFrom 0 (mark (PairedInitialGraph.circuit (List.range 49)).nodes
          (PairedInitialGraph.outputRefs (List.range 49)).toFinset)
        (PairedInitialGraph.circuit (List.range 49)).nodes := by
  rw [PairedLocalCircuit.live, roots_eq, implementation49_nodes, ← circuit_nodes_map,
    PairedRename.mark_map, PairedRename.additionCountFrom_map]
  rfl

/-- The pruned structural local circuit consumed by shared-point replay. -/
def implementation : PairedLocalCircuit := PairedIndexedGraph.implementation49.pruned

/-- Any live-addition bound for the pair-keyed construction bounds the
pruned structural implementation. -/
theorem additions_le_live : DAGAllocator.additionCount implementation.nodes ≤
    additionCountFrom 0 (mark (PairedInitialGraph.circuit (List.range 49)).nodes
        (PairedInitialGraph.outputRefs (List.range 49)).toFinset)
      (PairedInitialGraph.circuit (List.range 49)).nodes :=
  (PairedLocalCircuit.pruned_additions_le _).trans live_eq.le

/-- The unused single-exclusion sums are removed before replay. -/
theorem additions_le : DAGAllocator.additionCount implementation.nodes ≤
    PairedInitialGraph.additionBudget (List.range 49) - 49 := by
  have hs := PairedInitialGraph.single_additions_saved (List.range 49) List.pairwise_lt_range (by
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
    decide)
  rw [PairedInitialGraph.singleSavings_49] at hs
  have hc := PairedInitialGraph.circuit_additions_le (List.range 49)
  have hl := additions_le_live
  omega

end IntegerMultBounds.Networks.PairedIndexedPruning
