module

public import IntegerMultBounds.Networks.PairedIndexedPruning
public import IntegerMultBounds.Networks.SharedPointLocalReplay

/-! End-to-end shared-point execution from the literal recursive local
constructor, pruned to the ancestors of its outputs before replay. No
generated local DAG, mask bank, endpoint signature, or cross-copy witness is
imported. The budget does not yet credit shared duplicates; the sharp published bound remains on
the certified implementation until its live-node and duplicate counts are
established. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStructuralSharedPoint

open DisjointCircuit NeighborCounts SharedPointReplay

attribute [local irreducible] PairedIndexedGraph.circuit PairedIndexedGraph.implementation49
  PairedIndexedPruning.implementation SharedPointReplay.circuitUsing

/-- The same executable replay used by the main proof, with the pruned structural local constructor. -/
def circuit : State := circuitUsing PairedIndexedPruning.implementation

theorem ready : Ready circuit := circuitUsing_ready PairedIndexedPruning.implementation

theorem output_count : circuit.outputs.length = 58800 :=
  circuitUsing_output_count PairedIndexedPruning.implementation

theorem output_value {A : Type*} [AddCommMonoid A] (input : Triple 50 → A)
    (out : Output) (ho : out ∈ circuit.outputs) :
    (eval input circuit.nodes)[out.ref]? = some (supportSum input (expected out)) :=
  circuitUsing_output_value PairedIndexedPruning.implementation input out ho

/-- Every requested common-point/pair combination has an actual output. -/
theorem output_exists (c : Fin 50) (p : ℕ × ℕ) (hp : p ∈ PairedCircuit.pairs (List.range 49)) :
    ∃ out ∈ circuit.outputs, out.common = c ∧ out.pair = p := by
  have hm : (c,p) ∈ circuit.outputs.map key := by
    rw [show circuit.outputs.map key = _ from circuitUsing_keys PairedIndexedPruning.implementation]
    exact List.mem_flatMap.mpr ⟨c, List.mem_finRange c, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  obtain ⟨out, hout, he⟩ := List.mem_map.mp hm
  exact ⟨out, hout, congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- The actual scalar program for the structural construction. -/
def code : DAGAllocator.Code := codeUsing PairedIndexedPruning.implementation

def initial (input : Triple 50 → ZMod 2) : ℕ → ZMod 2 :=
  initialUsing PairedIndexedPruning.implementation input

/-- End-to-end correctness of every requested triple partial sum for the
structural program, including its actual allocated output slot. -/
theorem run_partial (input : Triple 50 → ZMod 2) (c : Fin 50) (j : Fin 1176) :
    ∃ i, ∃ hi : i < circuit.outputs.length,
      circuit.outputs[i].common = c ∧ circuit.outputs[i].pair = PairMask.pairAt 49 j ∧
      Circuit.run code.program (initial input) (code.outputSlot i) =
        supportSum input (Finset.univ.filter
          (fun T : Triple 50 => T.val ∩ (embedding c j).val = {c})) :=
  run_partial_for PairedIndexedPruning.implementation input c j

/-- Certificate-free budget for all fifty replayed copies: the sharp local
allocation count less the proved dead additions. Duplicate sharing across
copies is not yet credited. -/
def additionBudget : ℕ := 50 * 9818

theorem support_bound :
    ((SharedPointLocalFamily.domain PairedIndexedPruning.implementation).image
      (SharedPointLocalFamily.support PairedIndexedPruning.implementation)).card ≤ additionBudget := by
  calc
    _ ≤ (SharedPointLocalFamily.domain PairedIndexedPruning.implementation).card := Finset.card_image_le
    _ ≤ additionBudget := by
      rw [SharedPointLocalFamily.domain_card]
      exact Nat.mul_le_mul_left 50 PairedIndexedPruning.additions_le

/-- Both compiler bounds concern the actual structural shared-point circuit.
No finite-count premise or unchecked agreement with a generated DAG is assumed. -/
theorem compile_bounds :
    (DAGAllocator.compile circuit.nodes (circuit.outputs.map Output.ref)).state.next ≤
        additionBudget + 58800 ∧
    (DAGAllocator.compile circuit.nodes (circuit.outputs.map Output.ref)).program.length ≤
        2 * additionBudget + 58800 :=
  compile_bounds_for PairedIndexedPruning.implementation additionBudget support_bound

end IntegerMultBounds.Networks.PairedStructuralSharedPoint
