module

public import IntegerMultBounds.Networks.PairedCircuitUnique
public import IntegerMultBounds.Networks.PairedInitialBudget
public import IntegerMultBounds.Networks.PairedLocalCircuit

/-! The literal recursive paired constructor in canonical finite source
coordinates. This construction can implement the same local-circuit interface
as the finite witness; input renaming does not rely on a generated mask bank. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedIndexedGraph

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open PairedCoarseCorrect PairedPartition SupportInterpretation

/-- One actual input for each canonical pair position. -/
def nodes (n : ℕ) : List (Node (Fin (n.choose 2))) :=
  (List.finRange (n.choose 2)).map (fun i => ⟨.input i, {i}⟩)

abbrev edges (n : ℕ) := PairedInitialGraph.edges (List.range n)
abbrev weights (n : ℕ) := PairedInitialGraph.weights (List.range n)

/-- The actual local recursion, using finite source IDs from its first step. -/
def circuit (n : ℕ) : BlockResult (Fin (n.choose 2)) :=
  block (nodes n) (List.range n) (edges n) (weights n)

/-- Invalid pair keys have empty support; valid keys use the canonical inverse. -/
def inputSupport (n : ℕ) : Source ℕ → Finset (Fin (n.choose 2))
  | .vertex _ => ∅
  | .edge a b => if h : (a,b) ∈ pairs (List.range n) then
      {(PairMask.pairEquiv n).symm ⟨(a,b),h⟩} else ∅

@[simp] theorem inputSupport_pairAt (n : ℕ) (i : Fin (n.choose 2)) :
    inputSupport n (.edge (PairMask.pairAt n i).1 (PairMask.pairAt n i).2) = {i} := by
  have h := PairMask.pairAt_mem n i
  simp only [inputSupport, dite_eq_left h]
  congr 1
  apply (PairMask.pairEquiv n).injective
  simp only [Equiv.apply_symm_apply]
  exact Subtype.ext rfl

private theorem inputNodes_valid {ι : Type*} [DecidableEq ι]
    (xs : List ι) (prior : List (Finset ι)) :
    ValidFrom prior (xs.map (fun i => (⟨.input i, {i}⟩ : Node ι))) := by
  induction xs generalizing prior with
  | nil => trivial
  | cons i xs ih => exact ⟨rfl, ih _⟩

theorem nodes_valid (n : ℕ) : Valid (nodes n) := inputNodes_valid _ []

@[simp] theorem nodes_length (n : ℕ) : (nodes n).length = n.choose 2 := by simp [nodes]

theorem input_refSpec (n i : ℕ) (hi : i < n.choose 2) :
    RefSpec {⟨i,hi⟩} (nodes n) (some i) := by
  have hbound : i < (nodes n).length := by simpa using hi
  refine ⟨hbound, ?_⟩
  rw [refSupport_some _ i hbound]
  simp [nodes]

theorem edges_spec (n : ℕ) :
    TableSpec (fun p => inputSupport n (.edge p.1 p.2)) (pairs (List.range n))
      (nodes n) (edges n) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [edges, PairedInitialGraph.edges], ?_⟩
  intro i hi hj
  have hbound : i < n.choose 2 := by simpa only [PairMask.pairs_range_length] using hi
  simp only [List.get_eq_getElem, edges, PairedInitialGraph.edges, List.getElem_map,
    List.getElem_zipIdx, Nat.zero_add]
  refine ⟨trivial, ?_⟩
  have he : (pairs (List.range n))[i] = PairMask.pairAt n ⟨i,hbound⟩ := rfl
  rw [he, inputSupport_pairAt]
  exact input_refSpec n i hbound

theorem weights_spec (n : ℕ) :
    TableSpec (fun _ => (∅ : Finset (Fin (n.choose 2)))) (List.range n) (nodes n) (weights n) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [weights, PairedInitialGraph.weights], ?_⟩
  intro i hi hj
  simp only [List.get_eq_getElem, weights, PairedInitialGraph.weights, List.getElem_map]
  exact ⟨trivial, trivial, rfl⟩

theorem inputSupport_disjoint (n : ℕ) (x y : Source ℕ) (hne : x ≠ y) :
    Disjoint (inputSupport n x) (inputSupport n y) := by
  cases x with
  | vertex a => simp [inputSupport]
  | edge a b =>
    cases y with
    | vertex c => simp [inputSupport]
    | edge c d =>
      simp only [inputSupport]
      split_ifs with hab hcd
      · apply Finset.disjoint_singleton.mpr
        intro he
        have hp := congrArg (fun i => ((PairMask.pairEquiv n) i).val) he
        simp only [Equiv.apply_symm_apply] at hp
        exact hne (by cases hp; rfl)
      all_goals simp

/-- The input graph satisfies the same structural recursion invariant as the
original pair-keyed construction. -/
theorem graphReady (n : ℕ) : GraphReady (nodes n) (List.range n) (edges n) (weights n) := by
  apply graphReady_of_atomTable _ _ _ _ (inputSupport n) (nodes_valid n) List.pairwise_lt_range
    (edges_spec n) (weights_spec n)
  intro a _ b _ hne
  exact inputSupport_disjoint n a b hne

/-- The same structural uniqueness proof now certifies the finite-coordinate
constructor consumed by the local-circuit interface. -/
theorem circuit_unique (n : ℕ) : DisjointUnique.Unique (circuit n).nodes := by
  apply DisjointUnique.unique_of_valid_nodup
  · exact (PairedBlockCorrect.block_correct _ _ _ _ (graphReady n)).valid
  · apply PairedCircuitUnique.block_nodup
    simp only [nodes, List.map_map, Function.comp_def]
    exact (List.nodup_finRange _).map (fun _ _ h => Finset.singleton_injective h)

theorem atomRef_spec (n : ℕ) (a : Source ℕ) (ha : a ∈ atomKeys (List.range n)) :
    RefSpec (inputSupport n a) (nodes n) (atomRef (edges n) (weights n) a) := by
  have ht := tableSpec_atomTable (inputSupport n) (List.range n) (nodes n) (edges n) (weights n)
    (edges_spec n) (weights_spec n)
  exact tableSpec_lookup _ _ _ _ ht a ha

/-- Output semantics are proved in the finite input coordinates actually used
by shared-point replay, rather than transported through a supplied mask bank. -/
theorem query_support (n : ℕ) (excluded : List ℕ) :
    supports (nodes n) (query (edges n) (weights n) excluded) =
      Finset.univ.filter (fun i : Fin (n.choose 2) =>
        (PairMask.pairAt n i).1 ∉ excluded ∧ (PairMask.pairAt n i).2 ∉ excluded) := by
  rw [PairedQuerySupport.query_support (graphReady n)]
  have he : interpret (atomSupport (nodes n) (edges n) (weights n))
      (avoiding (atomKeys (List.range n)).toFinset excluded.toFinset) =
      interpret (inputSupport n) (avoiding (atomKeys (List.range n)).toFinset excluded.toFinset) := by
    apply congr_weights
    intro a ha
    exact (atomRef_spec n a (List.mem_toFinset.mp ((mem_avoiding _ _ _).mp ha).1)).2
  rw [he]
  ext i
  simp only [mem_interpret, mem_avoiding, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset]
  constructor
  · rintro ⟨a, ⟨ha, hd⟩, hi⟩
    cases a with
    | vertex a => simp [inputSupport] at hi
    | edge a b =>
      simp only [inputSupport] at hi
      split_ifs at hi with hab
      · have hii := Finset.mem_singleton.mp hi
        have hp : PairMask.pairAt n i = (a,b) := by
          rw [hii, ← PairMask.pairEquiv_val, Equiv.apply_symm_apply]
        rw [hp]
        simpa [endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left] using hd
      · simp at hi
  · intro hi
    refine ⟨.edge (PairMask.pairAt n i).1 (PairMask.pairAt n i).2, ⟨?_, ?_⟩, ?_⟩
    · exact (edge_mem_atomKeys _ _ _).mpr (PairMask.pairAt_mem n i)
    · simpa [endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left] using hi
    · simp [inputSupport_pairAt]

theorem circuit_correct (n : ℕ) :
    BlockCorrect (nodes n) (List.range n) (edges n) (weights n) (circuit n) :=
  PairedBlockCorrect.block_correct _ _ _ _ (graphReady n)

theorem circuit_pair_support (n : ℕ) (p : ℕ × ℕ) (hp : p ∈ pairs (List.range n)) :
    RefSpec (MaskDAG.decode (PairMask.exclusion n p.1 p.2))
      (circuit n).nodes (lookup (circuit n).two p) := by
  have hh := (circuit_correct n).two p hp
  rw [query_support] at hh
  convert hh using 1
  ext i
  simp only [PairMask.mem_exclusion, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A constructor bound for the actual finite-coordinate graph. Sharper
live-addition bounds can replace this conservative shape bound later. -/
theorem circuit_additions_le (n : ℕ) :
    DAGAllocator.additionCount (circuit n).nodes ≤ PairedInitialGraph.additionBudget (List.range n) := by
  have hn : DAGAllocator.additionCount (nodes n) = 0 := by
    simp [nodes, DAGAllocator.additionCount, List.countP_map]
  have h := PairedCircuitBudget.block_additions_le (nodes n) (List.range n) (edges n) (weights n)
  simpa only [circuit, hn, Nat.zero_add, PairedInitialGraph.additionBudget,
    edges, weights, PairedInitialGraph.edges, PairedInitialGraph.weights,
    List.length_map, List.length_zipIdx] using h

/-- Every pair-exclusion output is present once four vertices exist. -/
theorem exclusion_nonempty (n : ℕ) (hn : 4 ≤ n) (a b : ℕ) :
    (MaskDAG.decode (PairMask.exclusion n a b)).Nonempty := by
  have hsmall : ({a,b} : Finset ℕ).card < (Finset.range n).card := by
    have h := Finset.card_insert_le a ({b} : Finset ℕ)
    simp only [Finset.card_singleton, Finset.card_range] at h ⊢
    omega
  obtain ⟨v, hv, hnotv⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hsmall' : ({a,b,v} : Finset ℕ).card < (Finset.range n).card := by
    have h1 := Finset.card_insert_le a ({b,v} : Finset ℕ)
    have h2 := Finset.card_insert_le b ({v} : Finset ℕ)
    simp only [Finset.card_singleton, Finset.card_range] at h2 ⊢
    omega
  obtain ⟨w, hw, hnotw⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall'
  have hv' : v < n := Finset.mem_range.mp hv
  have hw' : w < n := Finset.mem_range.mp hw
  have hnv : v ≠ a ∧ v ≠ b := by simpa using hnotv
  have hnw : w ≠ a ∧ w ≠ b ∧ w ≠ v := by simpa using hnotw
  obtain ⟨p, hp, havoid⟩ : ∃ p ∈ pairs (List.range n), p.1 ∉ [a,b] ∧ p.2 ∉ [a,b] := by
    by_cases hlt : v < w
    · exact ⟨(v,w), (pairs_mem _ List.pairwise_lt_range _ _).mpr
        ⟨List.mem_range.mpr hv', List.mem_range.mpr hw', hlt⟩, by simp [hnv, hnw]⟩
    · exact ⟨(w,v), (pairs_mem _ List.pairwise_lt_range _ _).mpr
        ⟨List.mem_range.mpr hw', List.mem_range.mpr hv', by omega⟩, by simp [hnv, hnw]⟩
  obtain ⟨i, hi⟩ := (PairMask.pairEquiv n).surjective ⟨p,hp⟩
  have he : PairMask.pairAt n i = p := congrArg Subtype.val hi
  exact ⟨i, (PairMask.mem_exclusion n a b i).mpr (by simpa [he] using havoid)⟩

/-- Package a structurally verified graph without evaluating its nodes. -/
def implementationOf (graph : BlockResult (Fin 1176))
    (hvalid : Valid graph.nodes) (hnodup : (graph.nodes.map Node.support).Nodup)
    (hsupport : ∀ p ∈ pairs (List.range 49),
      RefSpec (MaskDAG.decode (PairMask.exclusion49 p.1 p.2))
        graph.nodes (lookup graph.two p)) : PairedLocalCircuit where
  nodes := graph.nodes
  outputs := (pairs (List.range 49)).map (fun p => (p, (lookup graph.two p).getD 0))
  valid := hvalid
  supports_nodup := hnodup
  output_keys := by simp [Function.comp_def]
  output_support := by
    intro out ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
    have hs := hsupport p hp
    have hn : (MaskDAG.decode (PairMask.exclusion49 p.1 p.2)).Nonempty :=
      exclusion_nonempty 49 (by decide) p.1 p.2
    cases he : lookup graph.two p with
    | none =>
      rw [he] at hs
      rw [← hs.2] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
    | some i =>
      simp only [Option.getD_some]
      have hi : i < graph.nodes.length := by
        have hvalid := hs.1
        rw [he] at hvalid
        exact hvalid
      refine ⟨hi, ?_⟩
      have hsupport := hs.2
      rw [he, refSupport_some _ i hi] at hsupport
      exact hsupport

private theorem implementationOf_additions_le (graph : BlockResult (Fin 1176))
    (hvalid : Valid graph.nodes) (hnodup : (graph.nodes.map Node.support).Nodup)
    (hsupport : ∀ p ∈ pairs (List.range 49),
      RefSpec (MaskDAG.decode (PairMask.exclusion49 p.1 p.2))
        graph.nodes (lookup graph.two p))
    (budget : ℕ) (hbudget : DAGAllocator.additionCount graph.nodes ≤ budget) :
    DAGAllocator.additionCount (implementationOf graph hvalid hnodup hsupport).nodes ≤ budget :=
  hbudget

/-- The literal recursive construction implements the shared-point interface.
This packages correctness and uniqueness only; no sharp count is assumed. -/
def implementation49 : PairedLocalCircuit :=
  implementationOf (circuit 49) (circuit_correct 49).valid (circuit_unique 49).nodup
    (circuit_pair_support 49)

/-- Transfer the constructor budget through the interface symbolically. -/
theorem implementation49_additions_le :
    DAGAllocator.additionCount implementation49.nodes ≤
      PairedInitialGraph.additionBudget (List.range 49) :=
  implementationOf_additions_le (circuit 49) (circuit_correct 49).valid (circuit_unique 49).nodup
    (circuit_pair_support 49) _ (circuit_additions_le 49)

end IntegerMultBounds.Networks.PairedIndexedGraph
