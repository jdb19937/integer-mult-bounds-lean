module

public import IntegerMultBounds.MathlibTM2.M8.Frames.DesignB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceNodes
public import IntegerMultBounds.MathlibTM2.M8.Local.WitnessB

/-! Compiler alignment for design-B node frames uses actual donor sources.
No nesting from an unused raw argument is assumed. Per-use late-copy frames
still require the finer wire-chain alignment of the concrete assignment. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames

noncomputable section
open Local

/-- Restrict the frame relation to the checked node range. -/
def FrameBLe (a b : Nat) : Prop :=
  a < nodeCount → b < nodeCount → Nested (frameB a) (frameB b)

theorem frameB_source_order : dagB.SourceFrameOrder FrameBLe where
  refl n hn _ := ⟨frameB_idem hn, frameB_idem hn⟩
  source k hk hkN pos _ _ := by
    have hs : dagB.srcNode (.gate k pos) = dag.srcNode (.gate k pos) := rfl
    rw [hs, (Local.src_eq hk hkN pos).1]
    exact frameB_src hk hkN pos

theorem frameB_compile_chain (s : Nat) :
    (nodesOf s dagB.compile.ops).IsChain FrameBLe :=
  dagB.compile_chain_source dagB_valid frameB_source_order s

end
end IntegerMultBounds.MathlibTM2.M8.Frames
