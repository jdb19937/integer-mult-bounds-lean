module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.CopyRanks

/-! The first nonidentity phase-A MOVE uses the actual zero and source-line
labels; its rank is derived from the range of the actual projector difference. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry

theorem label_two : label 2 = Submodule.span ℚ {root 0} := by
  change Submodule.span ℚ (root '' {j | j ∈ ([0] : List ℕ)}) = Submodule.span ℚ {root 0}
  simp

theorem root_zero_norm : form (root 0) (root 0) = 2 := by decide +kernel

theorem root_zero_ne : root 0 ≠ 0 := by
  intro h
  have hn := root_zero_norm
  rw [h] at hn
  norm_num at hn

theorem dimension_two : Module.finrank ℚ (label 2) = 1 := by
  rw [label_two]
  exact finrank_span_singleton root_zero_ne

/-- Exact initial phase-A incidence: helper222 moves from zero to source0's line. -/
theorem first_move_pair :
    Frames.edges [sectionAGate0000] (Frames.snapshot Frames.before005) = [(0, 2), (2, 2)] := by
  decide +kernel

theorem first_move_rank : moveRank 0 2 = 1 := by
  have hz : Module.finrank ℚ (label 0) = 0 := by
    rw [label_zero]
    simp
  rw [moveRank_eq 0 2 (Or.inl (by rw [label_zero]; exact bot_le))]
  rw [hz, dimension_two]

end IntegerMultBounds.Networks.Certificates.PR589.Geometry
