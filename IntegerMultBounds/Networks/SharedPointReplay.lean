module

public import IntegerMultBounds.Networks.SharedPointFamily
public import IntegerMultBounds.Networks.SharedPointLocalReplay

/-! The actual globally shared fifty-copy circuit: replay the structural local
DAG into one persistent interned DAG and retain every remapped output reference.
The proof does not assume any global circuit list or allocation count. -/

@[expose] public section

namespace IntegerMultBounds.Networks.SharedPointReplay

open DisjointCircuit DisjointBuilder NeighborCounts DAGReplay

attribute [local irreducible] PairedIndexedPruning.implementation DAGReplay.replay

/-- Selected implementation of the local-circuit contract. -/
abbrev implementation : PairedLocalCircuit := SharedPointFamily.localCircuit

/-- Import one local circuit and append its remapped designated outputs. -/
def step (state : State) (c : Fin 50) : State :=
  importStep implementation.nodes implementation.outputs state c

@[simp] theorem step_nodes (state : State) (c : Fin 50) :
    (step state c).nodes = (replay (embedding c) state.nodes implementation.nodes).1 :=
  importStep_nodes _ _ _ _

@[simp] theorem step_outputs (state : State) (c : Fin 50) :
    (step state c).outputs = state.outputs ++ implementation.outputs.map (fun out =>
      (⟨c, out.1, (replay (embedding c) state.nodes implementation.nodes).2[out.2]?.getD 0⟩ : Output)) :=
  importStep_outputs _ _ _ _

/-- Process common points in their literal enumeration order. -/
def runFrom (state : State) : List (Fin 50) → State
  | [] => state
  | c :: common => runFrom (step state c) common

def circuit : State := runFrom initial (List.finRange 50)

theorem step_ready (state : State) (c : Fin 50) (hs : Ready state) : Ready (step state c) :=
  importStep_ready implementation state c hs

theorem runFrom_eq_using (state : State) (common : List (Fin 50)) :
    runFrom state common = runUsing implementation state common := by
  induction common generalizing state with
  | nil => rfl
  | cons c common ih => exact ih _

theorem circuit_eq_using : circuit = circuitUsing implementation :=
  runFrom_eq_using initial (List.finRange 50)

theorem runFrom_ready (state : State) (common : List (Fin 50)) (hs : Ready state) :
    Ready (runFrom state common) := by
  rw [runFrom_eq_using]
  exact runUsing_ready implementation state common hs

theorem ready : Ready circuit := runFrom_ready initial _ ⟨trivial, by simp [initial], by simp [initial]⟩

theorem valid : Valid circuit.nodes := ready.1

theorem supports_nodup : (circuit.nodes.map Node.support).Nodup := ready.2.1

theorem output_support (out : Output) (ho : out ∈ circuit.outputs) : CorrectOutput circuit.nodes out :=
  ready.2.2 out ho

theorem output_bound (out : Output) (ho : out ∈ circuit.outputs) : out.ref < circuit.nodes.length :=
  lookup_bound (output_support out ho)

/-- Actual imported execution computes every requested lifted support sum. -/
theorem output_value {A : Type*} [AddCommMonoid A] (input : Triple 50 → A)
    (out : Output) (ho : out ∈ circuit.outputs) :
    (eval input circuit.nodes)[out.ref]? = some (supportSum input (expected out)) := by
  rw [eval_eq input _ valid]
  have hh := congrArg (Option.map (supportSum input)) (output_support out ho)
  simpa only [CorrectOutput, ← List.getElem?_map, List.map_map, Function.comp_def, Option.map_some] using hh

theorem step_keys (state : State) (c : Fin 50) :
    (step state c).outputs.map key = state.outputs.map key ++
      (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair)) :=
  importStep_keys implementation state c

theorem runFrom_keys (state : State) (common : List (Fin 50)) :
    (runFrom state common).outputs.map key = state.outputs.map key ++
      common.flatMap (fun c => (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair))) := by
  induction common generalizing state with
  | nil => simp [runFrom]
  | cons c common ih => simp only [runFrom, ih, step_keys, List.flatMap_cons, List.append_assoc]

/-- Every canonical pair output appears once per actual common-point copy. -/
theorem output_keys : circuit.outputs.map key =
    (List.finRange 50).flatMap (fun c =>
      (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair))) := by
  simpa only [circuit, initial, List.map_nil, List.nil_append] using runFrom_keys initial (List.finRange 50)

theorem step_output_count (state : State) (c : Fin 50) :
    (step state c).outputs.length = state.outputs.length + 1176 := by
  have h := implementation.output_count
  simpa only [step_outputs, List.length_append, List.length_map] using
    congrArg (state.outputs.length + ·) h

theorem runFrom_output_count (state : State) (common : List (Fin 50)) :
    (runFrom state common).outputs.length = state.outputs.length + common.length * 1176 := by
  induction common generalizing state with
  | nil => simp [runFrom]
  | cons c common ih =>
    rw [runFrom, ih, step_output_count, List.length_cons]
    omega

theorem output_count : circuit.outputs.length = 58800 := by
  rw [circuit, runFrom_output_count]
  simp [initial]

/-- The local support family bounds every newly imported addition. -/
theorem local_addition_mem (c : Fin 50) (s : Finset (Fin 1176))
    (hs : AdditionSupport implementation.nodes s) :
    s.map (embedding c) ∈ SharedPointFamily.domain.image SharedPointFamily.support := by
  obtain ⟨node, hn, hk, he⟩ := hs
  obtain ⟨i, hi, hnode⟩ := List.mem_iff_getElem.mp hn
  have hd : (c,i) ∈ SharedPointFamily.domain := by
    apply (SharedPointFamily.mem_domain_iff (c,i)).mpr
    exact ⟨node, (List.getElem?_eq_getElem hi).trans (congrArg some hnode), hk⟩
  refine Finset.mem_image.mpr ⟨(c,i), hd, ?_⟩
  rw [SharedPointFamily.support_eq, SharedPointFamily.localSupport_get i hi, hnode, he, map_embedding]

/-- All actual additions, including those from earlier copies, stay in the
finite source-support budget. -/
def Contained (state : State) : Prop :=
  ∀ s, AdditionSupport state.nodes s → s ∈ SharedPointFamily.domain.image SharedPointFamily.support

theorem step_contained (state : State) (c : Fin 50) (hs : Contained state) : Contained (step state c) := by
  rw [Contained, step_nodes]
  intro s hnew
  rcases replay_additionSupport (embedding c) state.nodes implementation.nodes s hnew with
    hold | ⟨localSupport, hlocal, he⟩
  · exact hs s hold
  · exact he ▸ local_addition_mem c localSupport hlocal

theorem runFrom_contained (state : State) (common : List (Fin 50)) (hs : Contained state) :
    Contained (runFrom state common) := by
  induction common generalizing state with
  | nil => exact hs
  | cons c common ih => exact ih _ (step_contained state c hs)

theorem contained : Contained circuit := runFrom_contained initial _ (by
  rintro s ⟨node, hn, _⟩
  simp [initial] at hn)

/-- Actual requested output references in their common-point/pair order. -/
def outputRefs : List ℕ := circuit.outputs.map Output.ref

attribute [local irreducible] circuit

theorem outputRefs_count : outputRefs.length = 58800 := by
  rw [outputRefs, List.length_map, output_count]

theorem outputRefs_bounds : ∀ i ∈ outputRefs, i < circuit.nodes.length := by
  intro i hi
  obtain ⟨out, ho, rfl⟩ := List.mem_map.mp hi
  exact output_bound out ho

theorem additionSupports_subset : DAGReplayBudget.additionSupports circuit.nodes ⊆
    SharedPointFamily.domain.image SharedPointFamily.support := by
  intro s hs
  exact contained s ((DAGReplayBudget.mem_additionSupports _ _).mp hs)

/-- Support sharing bounds the actual addition nodes of the constructed DAG. -/
theorem additions_le_supports : DAGAllocator.additionCount circuit.nodes ≤
    (SharedPointFamily.domain.image SharedPointFamily.support).card := by
  rw [circuit_eq_using]
  exact additions_le_for implementation

/-- Any support budget transfers to actual compiled storage without evaluating
the circuit or fixing the numerical support bound. -/
theorem allocated_roles_le_of (budget : ℕ)
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ budget) :
    (DAGAllocator.compile circuit.nodes outputRefs).state.next ≤ budget + 58800 := by
  change (DAGAllocator.compile circuit.nodes (circuit.outputs.map Output.ref)).state.next ≤ _
  rw [circuit_eq_using]
  exact (compile_bounds_for implementation budget hcard).1

/-- The same parameterized support budget bounds actual emitted instructions. -/
theorem compiled_instructions_le_of (budget : ℕ)
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ budget) :
    (DAGAllocator.compile circuit.nodes outputRefs).program.length ≤ 2 * budget + 58800 := by
  change (DAGAllocator.compile circuit.nodes (circuit.outputs.map Output.ref)).program.length ≤ _
  rw [circuit_eq_using]
  exact (compile_bounds_for implementation budget hcard).2

theorem allocated_roles_le
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394) :
    (DAGAllocator.compile circuit.nodes outputRefs).state.next ≤ 509194 :=
  allocated_roles_le_of 450394 hcard

theorem compiled_instructions_le
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394) :
    (DAGAllocator.compile circuit.nodes outputRefs).program.length ≤ 959588 :=
  compiled_instructions_le_of 450394 hcard

end IntegerMultBounds.Networks.SharedPointReplay
