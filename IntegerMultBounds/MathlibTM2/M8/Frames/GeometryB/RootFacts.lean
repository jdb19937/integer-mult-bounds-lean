module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootEndpointFacts
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Facts

/-! Soundness of root endpoint witnesses. Each witness reuses an existing
chain and a basis member; it introduces no new geometric certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section
open IntegerMultBounds Matrix

theorem rootOk_complement (j : Nat) (w : Nat × Nat) (h : rootOk j w = true) :
    Nested ((AssignmentB.rootLabel j).eval SignedFull.bankEntry)
      (rootFrame (SignedFull.bankEntry w.2).basis) ∧
    rvec (rootCode j) ∈ rspan (SignedFull.bankEntry w.2).basis := by
  unfold rootOk at h
  obtain ⟨hpath, hmem⟩ := Bool.and_eq_true_iff.mp h
  have he := (List.isChain_cons_cons.mp (chainAt_path w.1 _ hpath)).1
  refine ⟨he, ?_⟩
  exact Submodule.subset_span (List.mem_map_of_mem (List.contains_iff_mem.mp hmem))

theorem rootOk_output (j : Nat) (hj : j < 3 * Local.leafCount)
    (w : Nat × Nat) (h : rootOk j w = true) :
    Nested ((AssignmentB.rootLabel j).eval SignedFull.bankEntry)
      (hyperFrame (Local.leafTriple (j / 3))) := by
  obtain ⟨he, hspan⟩ := rootOk_complement j w h
  rw [rootCode_output j hj] at hspan
  exact he.trans (rootFrame_le_hyper_of_unit
    (RootBank.Record.check_spec (SignedFull.bankEntry_checked w.2)).2.1 hspan)

theorem rootOk_centre (c : Nat) (hc : c < 23) (w : Nat × Nat)
    (h : rootOk (3 * Local.leafCount + c) w = true) :
    Nested ((AssignmentB.rootLabel (3 * Local.leafCount + c)).eval SignedFull.bankEntry)
      (starFrame c) := by
  obtain ⟨he, hspan⟩ := rootOk_complement _ w h
  rw [rootCode_centre] at hspan
  exact he.trans (rootFrame_le_star_of_unit
    (RootBank.Record.check_spec (SignedFull.bankEntry_checked w.2)).2.1 hc hspan)

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
