module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeMomentsB
public import IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookupMoments

/-! Source-wire costs are bounded by the existing checked signed chains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The source checker starts at the input line itself, not a larger paid entrance. -/
theorem source_initial_eq (n : Nat) (hn : n < leafCount) :
    frameOfLabel (.positive (SourceGeometryB.sourceStart n)) = lineFrame (leafTriple n) := by
  let start := SourceGeometryB.sourceStart n
  have hc := SourceGeometryB.sourceOk_at n hn
  have hr := SourceGeometryB.sourceOk_initial_rank n start hc
  have he := SourceGeometryB.sourceOk_initial n start hn hc
  have hp := hc
  unfold SourceGeometryB.sourceOk at hp
  have hv : (Signed.Frame.positive start).validCheck SignedFull.bankSize = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hp).1).1
  exact (eq_of_le_rank_eq (lineFrame_idem (leafTriple_isTriple hn))
    (frameOfLabel_idem _ hv) (le_of_nested he)
    ((rank_lineFrame (leafTriple_isTriple hn)).trans hr.symm)).symm

/-- The full actual source path, including frame-one uncompute. -/
def sourceMoment (φ : Nat → ℝ) (n : Nat) : ℝ :=
  chainMoment φ (lineFrame (leafTriple n) :: fseq (.inl (.x n)) firstStage ++ [1])

/-- Each source's actual moves are bounded by its certified full-chain moment. -/
theorem sourceMoment_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (n : Nat) (hn : n < leafCount) :
    sourceMoment φ n ≤
      chainMoment φ ((SignedFull.chainAt (30637 + n)).map frameOfLabel) := by
  let start := SourceGeometryB.sourceStart n
  have hc := SourceGeometryB.sourceOk_at n hn
  have hp := hc
  unfold SourceGeometryB.sourceOk at hp
  have hcost := ChainLookup.pathCheck_moment_le φ hφ hsub SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) (SignedFull.chainAt (30637 + n))
    (SignedFull.chainAt_checked _) _ (Bool.and_eq_true_iff.mp hp).1
  change chainMoment φ ((Signed.Frame.positive start :: SourceGeometryB.sourceLabels n ++ [Signed.Frame.one]).map
    frameOfLabel) ≤ _ at hcost
  simp only [List.map_cons, List.map_append] at hcost
  rw [source_initial_eq n hn] at hcost
  change chainMoment φ (lineFrame (leafTriple n) ::
    (SourceGeometryB.sourceLabels n).map frameOfLabel ++ [1]) ≤ _ at hcost
  apply le_trans ?_ hcost
  have hchain := (SourceGeometryB.sourceOk_source_chain n start hn hc).imp le_of_nested
  change (lineFrame (leafTriple n) :: (SourceGeometryB.sourceLabels n).map frameOfLabel ++ [1]).Pairwise Le at hchain
  have ht : fseq (.inl (.x n)) firstStage =
      (SourceGeometryB.sourceLabels n).map frameOfLabel ++ sourceUncompute n := by
    rw [firstStage_source_label_trace, sourceGeometry_labels_eq n hn, List.map_append]
  apply chainMoment_le_of_subset φ hφ hsub ((firstStage_source_chain n hn).imp le_of_nested) hchain
  · intro F hF
    rw [ht] at hF
    apply padded_path_subset (lineFrame (leafTriple n)) 1 _ (sourceUncompute n)
      (sourceUncompute_one n) F
    simpa only [List.cons_append, List.append_assoc] using hF
  · intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact lineFrame_idem (leafTriple_isTriple hn)
      · obtain ⟨label, hl, rfl⟩ := List.mem_map.mp hF
        rw [sourceGeometry_labels_eq n hn, List.mem_append] at hl
        rcases hl with hl | hl <;>
          obtain ⟨u, _, rfl⟩ := List.mem_map.mp hl <;>
          exact frameOfLabel_idem _ (AssignmentB.startLabel_valid _)
    · rw [List.mem_singleton.mp hF]
      simp

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
