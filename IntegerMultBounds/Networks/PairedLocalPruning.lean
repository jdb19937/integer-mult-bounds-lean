module

public import IntegerMultBounds.Networks.PairedLocalCircuit
public import IntegerMultBounds.Networks.DAGCompact
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient

/-! Prune any local pair-exclusion circuit to the ancestors of its requested
outputs before replay. The pruned circuit satisfies the same contract, and
its addition count is the live count of the original, so dead-node credits
proved for a constructor reduce the shared-point family directly. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedLocalCircuit

open DisjointCircuit DisjointPruning DAGCompact

/-- The requested local output identifiers. -/
def roots (circuit : PairedLocalCircuit) : Finset ℕ := (circuit.outputs.map Prod.snd).toFinset

/-- The backward-marked ancestors of the requested outputs. -/
def live (circuit : PairedLocalCircuit) : Finset ℕ := mark circuit.nodes circuit.roots

theorem compact_live (circuit : PairedLocalCircuit) :
    Valid (compact circuit.live circuit.nodes).1 ∧
      ((compact circuit.live circuit.nodes).1.map Node.support).Nodup ∧
      ∀ j (hj : j < circuit.nodes.length), j ∈ circuit.live →
        ((compact circuit.live circuit.nodes).1.map Node.support)[
          (compact circuit.live circuit.nodes).2[j]?.getD 0]? = some circuit.nodes[j].support :=
  compact_correct circuit.live circuit.nodes circuit.valid
    (mark_closed circuit.nodes circuit.roots circuit.valid)

theorem output_live (circuit : PairedLocalCircuit) (out : (ℕ × ℕ) × ℕ)
    (ho : out ∈ circuit.outputs) : out.2 ∈ circuit.live :=
  roots_subset_markFrom 0 _ _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨out, ho, rfl⟩))

/-- The same circuit with every dead node removed and references renumbered. -/
def pruned (circuit : PairedLocalCircuit) : PairedLocalCircuit where
  nodes := (compact circuit.live circuit.nodes).1
  outputs := circuit.outputs.map (fun out => (out.1, (compact circuit.live circuit.nodes).2[out.2]?.getD 0))
  valid := circuit.compact_live.1
  supports_nodup := circuit.compact_live.2.1
  output_keys := by simpa [Function.comp_def] using circuit.output_keys
  output_support := by
    intro out ho
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ho
    obtain ⟨hi, hs⟩ := circuit.output_support old hold
    have h := circuit.compact_live.2.2 old.2 hi (circuit.output_live old hold)
    refine ⟨by simpa using DAGReplay.lookup_bound h, ?_⟩
    have he := (List.getElem?_eq_some_iff.mp h).2
    simpa only [List.getElem_map, hs] using he

/-- Pruning allocates only the live additions of the original circuit. -/
theorem pruned_additions_le (circuit : PairedLocalCircuit) :
    DAGAllocator.additionCount circuit.pruned.nodes ≤ additionCountFrom 0 circuit.live circuit.nodes :=
  compact_additions_le circuit.live circuit.nodes

end IntegerMultBounds.Networks.PairedLocalCircuit
