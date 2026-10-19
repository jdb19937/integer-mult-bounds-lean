module

public import IntegerMultBounds.Networks.SharedPointLocalFamily
public import IntegerMultBounds.Networks.DAGReplayBudget
public import IntegerMultBounds.Networks.DAGInstructionCount
public import IntegerMultBounds.Networks.SharedPointOutputMap

/-! Executable shared-point replay and physical compiler bounds for any local
pair-exclusion constructor satisfying its semantic contract. This module has
no dependency on generated local circuits, masks, or duplicate witnesses. -/

@[expose] public section

namespace IntegerMultBounds.Networks.SharedPointReplay

open DisjointCircuit DisjointBuilder NeighborCounts DAGReplay

/-- The actual input renaming for one common-point copy. -/
def embedding (c : Fin 50) : Fin 1176 ↪ Triple 50 :=
  ⟨SharedPointLift.source (SharedPointLift.pairPayload 49) (SharedPointLift.pairPayload_card 49) c,
    SharedPointLift.source_injective _ _ (SharedPointLift.pairPayload_injective 49) c⟩

@[simp] theorem map_embedding (c : Fin 50) (s : Finset (Fin 1176)) :
    s.map (embedding c) = SharedPointLift.lift49 c s := by
  rw [Finset.map_eq_image]
  rfl

structure Output where
  common : Fin 50
  pair : ℕ × ℕ
  ref : ℕ

structure State where
  nodes : List (Node (Triple 50))
  outputs : List Output

def expected (out : Output) : Finset (Triple 50) :=
  SharedPointLift.lift49 out.common (MaskDAG.decode (PairMask.exclusion49 out.pair.1 out.pair.2))

def CorrectOutput (nodes : List (Node (Triple 50))) (out : Output) : Prop :=
  (nodes.map Node.support)[out.ref]? = some (expected out)

def Ready (state : State) : Prop :=
  Valid state.nodes ∧ (state.nodes.map Node.support).Nodup ∧
    ∀ out ∈ state.outputs, CorrectOutput state.nodes out

/-- Import a source DAG with its designated output keys. -/
def importStep (source : List (Node (Fin 1176))) (localOutputs : List ((ℕ × ℕ) × ℕ))
    (state : State) (c : Fin 50) : State :=
  ⟨(replay (embedding c) state.nodes source).1,
    state.outputs ++ localOutputs.map (fun out =>
      ⟨c, out.1, (replay (embedding c) state.nodes source).2[out.2]?.getD 0⟩)⟩

theorem importStep_nodes (source : List (Node (Fin 1176)))
    (localOutputs : List ((ℕ × ℕ) × ℕ)) (state : State) (c : Fin 50) :
    (importStep source localOutputs state c).nodes = (replay (embedding c) state.nodes source).1 := rfl

theorem importStep_outputs (source : List (Node (Fin 1176)))
    (localOutputs : List ((ℕ × ℕ) × ℕ)) (state : State) (c : Fin 50) :
    (importStep source localOutputs state c).outputs = state.outputs ++ localOutputs.map (fun out =>
      (⟨c, out.1, (replay (embedding c) state.nodes source).2[out.2]?.getD 0⟩ : Output)) := rfl

def initial : State := ⟨[], []⟩

/-- Replay correctness consumes only the local-circuit contract. A structural
constructor and the current witness therefore use the same execution proof. -/
theorem importStep_ready (source : PairedLocalCircuit) (state : State) (c : Fin 50)
    (hs : Ready state) : Ready (importStep source.nodes source.outputs state c) := by
  obtain ⟨hv, hn, ho⟩ := hs
  rw [Ready, importStep_nodes, importStep_outputs]
  have hr := replay_correct (embedding c) state.nodes source.nodes hv source.valid
  refine ⟨hr.1, replay_nodup (embedding c) _ _ hn, ?_⟩
  intro out hout
  rcases List.mem_append.mp hout with hold | hnew
  · exact lookup_extends hr.2.1 (ho out hold)
  · obtain ⟨localOut, hlocal, rfl⟩ := List.mem_map.mp hnew
    obtain ⟨hi, hsupport⟩ := source.output_support localOut hlocal
    have hh := replay_support (embedding c) state.nodes source.nodes hv source.valid localOut.2 hi
    simpa only [CorrectOutput, expected, hsupport, map_embedding] using hh

/-- Execute the same shared-point replay with any proved local constructor. -/
def runUsing (source : PairedLocalCircuit) (state : State) : List (Fin 50) → State
  | [] => state
  | c :: common => runUsing source (importStep source.nodes source.outputs state c) common

theorem runUsing_ready (source : PairedLocalCircuit) (state : State) (common : List (Fin 50))
    (hs : Ready state) : Ready (runUsing source state common) := by
  induction common generalizing state with
  | nil => exact hs
  | cons c common ih => exact ih _ (importStep_ready source state c hs)

/-- The complete executable shared-point circuit for a supplied local constructor. -/
def circuitUsing (source : PairedLocalCircuit) : State := runUsing source initial (List.finRange 50)

theorem circuitUsing_ready (source : PairedLocalCircuit) : Ready (circuitUsing source) :=
  runUsing_ready source initial _ ⟨trivial, by simp [initial], by simp [initial]⟩

theorem runUsing_output_count (source : PairedLocalCircuit) (state : State) (common : List (Fin 50)) :
    (runUsing source state common).outputs.length = state.outputs.length + common.length * 1176 := by
  induction common generalizing state with
  | nil => simp [runUsing]
  | cons c common ih =>
    simp only [runUsing, ih, importStep_outputs, List.length_append, List.length_map,
      source.output_count, List.length_cons]
    omega

theorem circuitUsing_output_count (source : PairedLocalCircuit) :
    (circuitUsing source).outputs.length = 58800 := by
  rw [circuitUsing, runUsing_output_count]
  simp [initial]

def ContainedFor (source : PairedLocalCircuit) (state : State) : Prop :=
  ∀ s, AdditionSupport state.nodes s →
    s ∈ (SharedPointLocalFamily.domain source).image (SharedPointLocalFamily.support source)

theorem importStep_contained_for (source : PairedLocalCircuit) (state : State) (c : Fin 50)
    (hs : ContainedFor source state) :
    ContainedFor source (importStep source.nodes source.outputs state c) := by
  intro s hnew
  rw [importStep_nodes] at hnew
  rcases replay_additionSupport (embedding c) state.nodes source.nodes s hnew with
    hold | ⟨support, ⟨node, hn, hk, he⟩, hmap⟩
  · exact hs s hold
  · obtain ⟨i, hi, hnode⟩ := List.mem_iff_getElem.mp hn
    have hd : (c,i) ∈ SharedPointLocalFamily.domain source := by
      apply (SharedPointLocalFamily.mem_domain source (c,i)).mpr
      exact (DAGAdditionIds.mem_additionIds _ i).mpr
        ⟨node, (List.getElem?_eq_getElem hi).trans (congrArg some hnode), hk⟩
    apply Finset.mem_image.mpr
    refine ⟨(c,i), hd, ?_⟩
    rw [SharedPointLocalFamily.support, source.support_get i hi, hnode, he, ← map_embedding, hmap]

theorem runUsing_contained (source : PairedLocalCircuit) (state : State) (common : List (Fin 50))
    (hs : ContainedFor source state) : ContainedFor source (runUsing source state common) := by
  induction common generalizing state with
  | nil => exact hs
  | cons c common ih => exact ih _ (importStep_contained_for source state c hs)

/-- The actual replayed additions are bounded by the supplied implementation's
shared support family. This is the bound consumed by the main compiler proof. -/
theorem additions_le_for (source : PairedLocalCircuit) :
    DAGAllocator.additionCount (circuitUsing source).nodes ≤
      ((SharedPointLocalFamily.domain source).image (SharedPointLocalFamily.support source)).card := by
  apply DAGReplayBudget.additions_le_card _ _ (circuitUsing_ready source).2.1
  intro support hs
  have hcontained := runUsing_contained source initial (List.finRange 50) (by
    rintro s ⟨node, hn, _⟩
    simp [initial] at hn)
  exact hcontained support ((DAGReplayBudget.mem_additionSupports _ _).mp hs)

/-- Both physical budgets are proved for the same executable replayed circuit,
with no dependency on the concrete local constructor or generated mask rows. -/
theorem compile_bounds_for (source : PairedLocalCircuit) (budget : ℕ)
    (hcard : ((SharedPointLocalFamily.domain source).image
      (SharedPointLocalFamily.support source)).card ≤ budget) :
    (DAGAllocator.compile (circuitUsing source).nodes
      ((circuitUsing source).outputs.map Output.ref)).state.next ≤ budget + 58800 ∧
    (DAGAllocator.compile (circuitUsing source).nodes
      ((circuitUsing source).outputs.map Output.ref)).program.length ≤ 2 * budget + 58800 := by
  have hr := circuitUsing_ready source
  have hb : ∀ i ∈ (circuitUsing source).outputs.map Output.ref,
      i < (circuitUsing source).nodes.length := by
    intro i hi
    obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hi
    exact lookup_bound (hr.2.2 out hout)
  have ha := (additions_le_for source).trans hcard
  have hroles := DAGAllocator.compile_roles_le _ _ hr.1 hb
  have hcode := DAGAllocator.compile_program_le_additions _ _ hr.1 hb
  have hlen : ((circuitUsing source).outputs.map Output.ref).length = 58800 := by
    rw [List.length_map, circuitUsing_output_count]
  rw [hlen] at hroles hcode
  constructor <;> omega

def key (out : Output) : Fin 50 × (ℕ × ℕ) := (out.common, out.pair)

theorem importStep_keys (source : PairedLocalCircuit) (state : State) (c : Fin 50) :
    (importStep source.nodes source.outputs state c).outputs.map key = state.outputs.map key ++
      (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair)) := by
  simp only [importStep_outputs, List.map_append, List.map_map]
  rw [← source.output_keys]
  simp only [List.map_map, Function.comp_def, key]

attribute [local irreducible] circuitUsing

/-- The physical program compiled from a supplied local constructor. -/
def codeUsing (source : PairedLocalCircuit) : DAGAllocator.Code :=
  DAGAllocator.compile (circuitUsing source).nodes ((circuitUsing source).outputs.map Output.ref)

end IntegerMultBounds.Networks.SharedPointReplay
