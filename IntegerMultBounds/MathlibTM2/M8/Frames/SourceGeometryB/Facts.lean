module

public import IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB.Kernel
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootFacts

/-! Passed source paths bound their frames between the input line and one. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB
noncomputable section
open IntegerMultBounds Matrix Local

theorem sourceOk_chain (n start : Nat) (h : sourceOk n start = true) :
    List.IsChain Nested
      ((Signed.Frame.positive start).eval SignedFull.bankEntry ::
        (sourceLabels n).map (Signed.Frame.eval SignedFull.bankEntry) ++ [1]) := by
  unfold sourceOk at h
  have hp := GeometryB.chainAt_path (30637 + n) _ (Bool.and_eq_true_iff.mp h).1
  simpa only [List.map_cons, List.map_append, List.map_singleton, List.map_nil,
    Signed.Frame.eval] using hp

theorem sourceOk_initial (n start : Nat) (hn : n < leafCount)
    (h : sourceOk n start = true) :
    Nested (lineFrame (leafTriple n)) ((Signed.Frame.positive start).eval SignedFull.bankEntry) := by
  unfold sourceOk at h
  have hspan : rvec (GeometryB.rootCode (3 * n)) ∈ rspan (SignedFull.bankEntry start).basis :=
    Submodule.subset_span (List.mem_map_of_mem (List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1))
  rw [rootCode_output (3 * n) (by omega)] at hspan
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 3)] at hspan
  have hc := nested_one_sub (rootFrame_le_hyper_of_unit
    (RootBank.Record.check_spec (SignedFull.bankEntry_checked start)).2.1 hspan)
  simpa only [hyperFrame, rootFrame, sub_sub_cancel, Signed.Frame.eval] using hc

/-- The checked entrance has exactly the input line's rank; no extra entrance rank is paid. -/
theorem sourceOk_initial_rank (n start : Nat) (h : sourceOk n start = true) :
    ((Signed.Frame.positive start).eval SignedFull.bankEntry).rank = 1 := by
  unfold sourceOk at h
  have hlen := Nat.beq_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
  change (proj formG (rootMat (SignedFull.bankEntry start).basis)).rank = 1
  simpa only [Fintype.card_fin, hlen] using
    proj_rank (RootBank.Record.check_spec (SignedFull.bankEntry_checked start)).2.1

theorem sourceOk_source_chain (n start : Nat) (hn : n < leafCount)
    (h : sourceOk n start = true) :
    (lineFrame (leafTriple n) :: (sourceLabels n).map (Signed.Frame.eval SignedFull.bankEntry) ++
      [1]).Pairwise Nested := by
  let : IsTrans _ Nested := ⟨fun _ _ _ h h' => h.trans h'⟩
  obtain ⟨hb, ht⟩ := List.pairwise_cons.mp (List.isChain_iff_pairwise.mp (sourceOk_chain n start h))
  exact List.pairwise_cons.mpr ⟨fun F hF => (sourceOk_initial n start hn h).trans (hb F hF), ht⟩

end
end IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB
