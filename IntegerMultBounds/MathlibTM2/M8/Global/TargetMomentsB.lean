module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceMomentsB
public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.EndpointRankChecked

/-! Target-wire costs are bounded by the existing full signed chains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The selected negative endpoint is exactly the output hyperplane. -/
theorem target_endpoint_eq (t : Nat) (ht : t < leafCount) :
    frameOfLabel (.negative (TargetGeometryB.endpoint t)) = hyperFrame (leafTriple t) := by
  let endpoint := TargetGeometryB.endpoint t
  have hc := SignedFull.bankEntry_checked endpoint
  have he := TargetGeometryB.targetOk_endpoint t endpoint ht (TargetGeometryB.targetOk_at t ht)
  have hr := RootBank.Record.rank _ hc
  rw [TargetGeometryB.endpoint_basis_length t ht] at hr
  change (rootFrame (SignedFull.bankEntry (TargetGeometryB.endpoint t)).basis).rank = 22 at hr
  have hH := rank_sub_of_le (lineFrame_idem (leafTriple_isTriple ht))
    (Matrix.one_mul (1 : LMat)) (le_one (lineFrame (leafTriple t)))
  rw [rank_lineFrame (leafTriple_isTriple ht), Matrix.rank_one, Fintype.card_fin] at hH
  exact eq_of_le_rank_eq (RootBank.Record.idem _ hc) (hyperFrame_idem (leafTriple_isTriple ht))
    (le_of_nested he) (by change (rootFrame _).rank = (1 - lineFrame (leafTriple t)).rank; omega)

def targetMoment (φ : Nat → ℝ) (t : Nat) : ℝ :=
  chainMoment φ (0 :: fseq (Sum.inl (Reg.y t) : LW) firstStage ++ [hyperFrame (leafTriple t)])

/-- Immediate zero reads, repeated deferred frames and final output reads are all priced. -/
theorem targetMoment_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (t : Nat) (ht : t < leafCount) :
    targetMoment φ t ≤ chainMoment φ ((SignedFull.chainAt (28866 + t)).map frameOfLabel) := by
  have hp := TargetGeometryB.targetOk_at t ht
  unfold TargetGeometryB.targetOk at hp
  have hcost := ChainLookup.pathCheck_moment_le φ hφ hsub SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) (SignedFull.chainAt (28866 + t))
    (SignedFull.chainAt_checked _) _ (Bool.and_eq_true_iff.mp hp).1
  change chainMoment φ ((Signed.Frame.zero :: TargetGeometryB.readoutLabels t ++
    [Signed.Frame.negative (TargetGeometryB.endpoint t)]).map frameOfLabel) ≤ _ at hcost
  simp only [List.map_cons, List.map_append] at hcost
  rw [target_endpoint_eq t ht] at hcost
  change chainMoment φ (0 :: (TargetGeometryB.readoutLabels t).map frameOfLabel ++
    [hyperFrame (leafTriple t)]) ≤ _ at hcost
  apply le_trans ?_ hcost
  have hc := (TargetGeometryB.targetOk_readout_chain t (TargetGeometryB.endpoint t) ht
    (TargetGeometryB.targetOk_at t ht)).imp le_of_nested
  apply chainMoment_le_of_subset φ hφ hsub ((firstStage_target_chain t ht).imp le_of_nested) hc
  · intro F hF
    rw [firstStage_target_label_trace t ht] at hF
    apply padded_path_both_subset 0 (hyperFrame (leafTriple t)) (targetZeroPrefix t) _
      ((outputRoots.filter fun j => decide (t ∈ targets j)).map assignment.output) ?_ ?_ F hF
    · intro K hK
      exact of_decide_eq_true (List.all_eq_true.mp (targetZeroPrefix_zero t) K hK)
    · intro K hK
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hK
      exact target_output_frame t j ht (List.mem_filter.mp hj).1
        (of_decide_eq_true (List.mem_filter.mp hj).2)
  · intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with rfl | hF
      · simp
      · obtain ⟨label, hl, rfl⟩ := List.mem_map.mp hF
        rw [target_readoutLabels_eq] at hl
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hl
        exact frameOfLabel_idem _ (AssignmentB.sigmaLabel_valid s)
    · rw [List.mem_singleton.mp hF]
      exact hyperFrame_idem (leafTriple_isTriple ht)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
