module

public import IntegerMultBounds.Networks.Certificates.PR589.Frames.Model
public import IntegerMultBounds.Networks.FramedEdgeTrace

/-! Interpret the exact common-frame phase traces through the existing compiler.
This does not compile scatter: its distinct-frame COPY contract is separate. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Frames

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

def framedGate (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (g : RawGate) :
    FramedCircuit.FramedGate ℕ (ZMod 2) E := ⟨g.toCircuit, frameOf g.frame⟩

theorem touched_toCircuit (g : RawGate) : FramedCircuit.touched g.toCircuit = touched g := by
  simp [FramedCircuit.touched, RawGate.toCircuit, touched, List.map_map, Function.comp_def]

theorem afterGate_eq (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (current : ℕ → ℕ) (g : RawGate) :
    FramedCircuit.afterGate (fun i => frameOf (current i)) (framedGate frameOf g) =
      fun i => frameOf (step g current i) := by
  funext i
  simp only [FramedCircuit.afterGate, framedGate, touched_toCircuit,
    FramedCircuit.afterEdges_apply, step]
  split <;> rfl

theorem finalFrames_eq (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (gs : List RawGate) (current : ℕ → ℕ) :
    FramedCircuit.finalFrames (fun i => frameOf (current i)) (gs.map (framedGate frameOf)) =
      fun i => frameOf (run gs current i) := by
  induction gs generalizing current with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, FramedCircuit.finalFrames, afterGate_eq, run]
    exact ih _

/-- Ordered old/new pairs are those of the actual compiled edge operators. -/
theorem compile_pairs (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (gs : List RawGate) (current : ℕ → ℕ) :
    FramedEdgeTrace.pairs (FramedCircuit.compile (fun i => frameOf (current i))
      (gs.map (framedGate frameOf))) =
    (edges gs current).map (fun p => (frameOf p.1, frameOf p.2)) := by
  induction gs generalizing current with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, FramedCircuit.compile, FramedEdgeTrace.pairs_append,
      afterGate_eq]
    have hgate : FramedEdgeTrace.pairs (FramedCircuit.compileGate
        (fun i => frameOf (current i)) (framedGate frameOf g)) =
        (RankTrace.edges current ((touched g).map fun i => (i, g.frame))).map
          (fun p => (frameOf p.1, frameOf p.2)) := by
      simp only [FramedCircuit.compileGate, framedGate, touched_toCircuit,
        FramedEdgeTrace.pairs_append]
      rw [FramedEdgeTrace.pairs_edges]
      simp [FramedEdgeTrace.pairs]
    rw [hgate, ih]
    simp only [edges, updates, List.flatMap_cons, RankTrace.edges_append,
      ← step_eq_finish, List.map_append]

/-- Phase compilation uses exactly the literal scalar gates and checked final profile. -/
theorem compile_semantics (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (gs : List RawGate) (current : ℕ → ℕ) (x : ℕ → E) :
    FramedCircuit.run (FramedCircuit.compile (fun i => frameOf (current i))
      (gs.map (framedGate frameOf))) (FramedCircuit.encode (fun i => frameOf (current i)) x) =
    FramedCircuit.encode (fun i => frameOf (run gs current i))
      (FramedCircuit.moduleRun (gs.map RawGate.toCircuit) x) := by
  rw [FramedCircuit.compile_invariant, finalFrames_eq]
  simp only [List.map_map, framedGate, Function.comp_def]

end IntegerMultBounds.Networks.Certificates.PR589.Frames
