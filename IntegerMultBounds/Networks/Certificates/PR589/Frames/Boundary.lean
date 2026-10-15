module

public import IntegerMultBounds.Networks.Certificates.PR589.Frames.Replay
public import IntegerMultBounds.Networks.Certificates.PR589.Frames.Compilation

/-! The checked frame profiles are the actual compiler's phase boundaries.
The intervening distinct-frame COPY execution remains a separate obligation. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Frames

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The literal D/A compiler ends at the certified pre-COPY profile. -/
theorem before_scatter_compiled (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (x : ℕ → E) :
    FramedCircuit.run (FramedCircuit.compile (fun i => frameOf (snapshot initialRefs i))
      ((sectionD ++ sectionA).map (framedGate frameOf)))
      (FramedCircuit.encode (fun i => frameOf (snapshot initialRefs i)) x) =
    FramedCircuit.encode (fun i => frameOf (beforeScatter i))
      (FramedCircuit.moduleRun ((sectionD ++ sectionA).map RawGate.toCircuit) x) := by
  rw [compile_semantics, before_scatter]

/-- B/C begins with that same profile; scatter does not silently align its inputs. -/
theorem after_scatter_compiled (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (x : ℕ → E) :
    FramedCircuit.run (FramedCircuit.compile (fun i => frameOf (scatterFinish beforeScatter i))
      ((sectionB ++ sectionC).map (framedGate frameOf)))
      (FramedCircuit.encode (fun i => frameOf (scatterFinish beforeScatter i)) x) =
    FramedCircuit.encode (fun i => frameOf (snapshot after234 i))
      (FramedCircuit.moduleRun ((sectionB ++ sectionC).map RawGate.toCircuit) x) := by
  rw [compile_semantics, after_scatter]

/-- Final alignment changes frames on every physical register, including helpers. -/
theorem final_alignment_compiled (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (x : ℕ → E) :
    FramedCircuit.run (FramedCircuit.edges (fun i => frameOf (snapshot after234 i))
      (fun i => frameOf (finalRefs i)) (List.range 661))
      (FramedCircuit.encode (fun i => frameOf (snapshot after234 i)) x) =
    FramedCircuit.encode (fun i => frameOf (snapshot finalRefs i)) x := by
  rw [FramedCircuit.edges_invariant]
  have h : FramedCircuit.afterEdges (fun i => frameOf (snapshot after234 i))
      (fun i => frameOf (finalRefs i)) (List.range 661) =
      fun i => frameOf (snapshot finalRefs i) := by
    funext i
    rw [FramedCircuit.afterEdges_apply]
    by_cases hi : i < 661 <;> simp [List.mem_range, snapshot, hi]
  rw [h]

/-- The retained final edge list is the actual compiler's ordered operator list. -/
theorem final_alignment_pairs (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) :
    FramedEdgeTrace.pairs (FramedCircuit.edges (fun i => frameOf (snapshot after234 i))
      (fun i => frameOf (finalRefs i)) (List.range 661)) =
    finalEdges.map (fun p => (frameOf p.1, frameOf p.2)) := by
  exact FramedEdgeTrace.pairs_edges frameOf (snapshot after234) finalRefs (List.range 661)

end IntegerMultBounds.Networks.Certificates.PR589.Frames
