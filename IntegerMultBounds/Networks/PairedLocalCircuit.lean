module

public import IntegerMultBounds.Networks.SharedPointLift
public import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DAGAdditionIds
public import IntegerMultBounds.Networks.DAGValueTransfer

/-! The local-circuit interface used by shared-point replay. Correctness and
support uniqueness concern the same executable node list. Concrete mask banks
and generated row formats are not part of this interface. -/

@[expose] public section

namespace IntegerMultBounds.Networks

open DisjointCircuit

/-- A local pair-exclusion circuit in the canonical 49-vertex coordinates. -/
structure PairedLocalCircuit where
  nodes : List (Node (Fin 1176))
  outputs : List ((ℕ × ℕ) × ℕ)
  valid : Valid nodes
  supports_nodup : (nodes.map Node.support).Nodup
  output_keys : outputs.map Prod.fst = PairedCircuit.pairs (List.range 49)
  output_support : ∀ out ∈ outputs, ∃ hi : out.2 < nodes.length,
    nodes[out.2].support = MaskDAG.decode (PairMask.exclusion49 out.1.1 out.1.2)

namespace PairedLocalCircuit

/-- The actual local support at a node identifier. -/
def support (circuit : PairedLocalCircuit) (i : ℕ) : Finset (Fin 1176) :=
  (circuit.nodes[i]?.map Node.support).getD ∅

theorem support_get (circuit : PairedLocalCircuit) (i : ℕ) (hi : i < circuit.nodes.length) :
    circuit.support i = circuit.nodes[i].support := by
  simp [support, List.getElem?_eq_getElem hi]

theorem output_count (circuit : PairedLocalCircuit) : circuit.outputs.length = 1176 := by
  have h : circuit.outputs.length = Nat.choose 49 2 := by
    simpa only [List.length_map, PairMask.pairs_range_length] using
      congrArg List.length circuit.output_keys
  norm_num [Nat.choose_two_right] at h
  exact h

theorem output_bounds (circuit : PairedLocalCircuit) :
    ∀ i ∈ circuit.outputs.map Prod.snd, i < circuit.nodes.length := by
  intro i hi
  obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hi
  exact (circuit.output_support out hout).choose

/-- Semantic endpoint summaries are defined for every local constructor,
without requiring a generated signature bank. -/
def endpointCore (circuit : PairedLocalCircuit) (i : ℕ) : Finset (Fin 49) :=
  MaskSignature.core (SharedPointLift.pairPayload 49) (circuit.support i)

def endpointUnion (circuit : PairedLocalCircuit) (i : ℕ) : Finset (Fin 49) :=
  MaskSignature.union (SharedPointLift.pairPayload 49) (circuit.support i)

/-- Actual addition supports satisfy the union law at every valid node. -/
theorem support_add (circuit : PairedLocalCircuit) (i : ℕ) (hi : i < circuit.nodes.length)
    (l r : ℕ) (hk : circuit.nodes[i].kind = .add l r) :
    circuit.support i = circuit.support l ∪ circuit.support r := by
  have hn : circuit.nodes[i].Valid ((circuit.nodes.take i).map Node.support) := by
    simpa using DAGValueTransfer.validFrom_get [] circuit.nodes circuit.valid i hi
  simp only [Node.Valid, hk, List.length_map, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hi)] at hn
  split at hn
  next hl =>
    split at hn
    next hr =>
      simp only [List.getElem_map, List.getElem_take] at hn
      rw [support_get circuit i hi, support_get circuit l (hl.trans hi),
        support_get circuit r (hr.trans hi), hn.2]
    next hr => contradiction
  next hl => contradiction

/-- Endpoint summaries are computed structurally by intersection and union
at actual additions, rather than accepted from a generated signature table. -/
theorem endpoints_add (circuit : PairedLocalCircuit) (i : ℕ) (hi : i < circuit.nodes.length)
    (l r : ℕ) (hk : circuit.nodes[i].kind = .add l r) :
    circuit.endpointCore i = circuit.endpointCore l ∩ circuit.endpointCore r ∧
      circuit.endpointUnion i = circuit.endpointUnion l ∪ circuit.endpointUnion r := by
  change MaskSignature.core _ (circuit.support i) = _ ∧
    MaskSignature.union _ (circuit.support i) = _
  rw [circuit.support_add i hi l r hk]
  exact ⟨MaskSignature.core_union _ _ _, MaskSignature.union_union _ _ _⟩

/-- Lifted core semantics apply to the actual circuit's endpoint summaries. -/
theorem lifted_core (circuit : PairedLocalCircuit) (c : Fin 50) (i : ℕ) :
    SharedPointKey.core (SharedPointLift.lift49 c (circuit.support i)) =
      insert c ((circuit.endpointCore i).image c.succAbove) :=
  SharedPointLift.core_lift _ _ c _

theorem lifted_union (circuit : PairedLocalCircuit) (c : Fin 50) (i : ℕ)
    (hn : (circuit.support i).Nonempty) :
    SharedPointKey.vertices (SharedPointLift.lift49 c (circuit.support i)) =
      insert c ((circuit.endpointUnion i).image c.succAbove) :=
  SharedPointLift.vertices_lift _ _ c _ hn

/-- All supports in an actual addition are nontrivial, irrespective of the
local circuit implementation. -/
theorem support_card_two (circuit : PairedLocalCircuit) (i : ℕ)
    (hi : i ∈ DAGAdditionIds.additionIds circuit.nodes) : 2 ≤ (circuit.support i).card := by
  obtain ⟨node, hget, l, r, hk⟩ := (DAGAdditionIds.mem_additionIds _ _).mp hi
  rw [support, hget]
  exact DisjointUnique.valid_add_card_two circuit.nodes circuit.valid node
    (List.mem_of_getElem? hget) l r hk

end PairedLocalCircuit
end IntegerMultBounds.Networks
