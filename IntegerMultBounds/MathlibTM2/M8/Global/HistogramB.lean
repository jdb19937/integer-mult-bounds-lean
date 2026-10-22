module

public import IntegerMultBounds.MathlibTM2.M8.Global.SignedNodeBoundB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedHistogramB.Checked

/-! Aggregate the actual signed chains over physical compiler slots and data roles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

private theorem slotTree_perfect : GeometryB.slotTree.Perfect 32768 := by
  exact ⟨by decide, by decide,
    ⟨by decide, by decide, ⟨by decide, by decide, GeometryB.slots00_perfect, GeometryB.slots01_perfect⟩,
      ⟨by decide, by decide, GeometryB.slots02_perfect, GeometryB.slots03_perfect⟩⟩,
    ⟨by decide, by decide, ⟨by decide, by decide, GeometryB.slots04_perfect, GeometryB.slots05_perfect⟩,
      ⟨by decide, by decide, GeometryB.slots06_perfect, GeometryB.slots07_perfect⟩⟩⟩

/-- The actual physical slot map, including any repeated chain indices, is counted directly. -/
theorem sum_auxiliary_chainMoment (φ : Nat → ℝ) :
    (∑ s : Slot, chainMoment φ (auxiliaryChain s)) = evalH φ SignedHistogramB.auxHist := by
  have h := signed_tree_hist_eq φ SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) SignedFull.chainAt SignedFull.chainAt_checked
    (fun _ i => i) GeometryB.slotCount GeometryB.slotTree 32768 0 slotTree_perfect
  have hc := SignedHistogramB.auxHist_checked
  unfold SignedHistogramB.chainMoves at hc
  rw [hc] at h
  simp only [Nat.zero_add] at h
  change evalH φ SignedHistogramB.auxHist =
    ∑ i ∈ Finset.range 32768, if i < GeometryB.slotCount then chainMoment φ (auxiliaryChain i) else 0 at h
  rw [sum_range_padded _ _ _ (by decide)] at h
  rw [Fin.sum_univ_eq_sum_range (fun s => chainMoment φ (auxiliaryChain s)), slot_count]
  exact h.symm

/-- Target chains contribute exactly the histogram reconstructed from their existing bank. -/
theorem sum_target_chainMoment (φ : Nat → ℝ) :
    (∑ t : V, chainMoment φ ((SignedFull.chainAt (28866 + t)).map frameOfLabel)) =
      evalH φ SignedHistogramB.targetHist := by
  have h := signed_chains_hist_eq φ SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) SignedFull.chainAt SignedFull.chainAt_checked
    (List.range' 28866 1771)
  have hc := SignedHistogramB.targetHist_checked
  unfold SignedHistogramB.chainMoves at hc
  rw [hc, sum_map_range'] at h
  rw [Fin.sum_univ_eq_sum_range (fun t => chainMoment φ ((SignedFull.chainAt (28866 + t)).map frameOfLabel))]
  exact h.symm

/-- Source chains are counted in their own canonical source order. -/
theorem sum_source_chainMoment (φ : Nat → ℝ) :
    (∑ n : V, chainMoment φ ((SignedFull.chainAt (30637 + n)).map frameOfLabel)) =
      evalH φ SignedHistogramB.sourceHist := by
  have h := signed_chains_hist_eq φ SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) SignedFull.chainAt SignedFull.chainAt_checked
    (List.range' 30637 1771)
  have hc := SignedHistogramB.sourceHist_checked
  unfold SignedHistogramB.chainMoves at hc
  rw [hc, sum_map_range'] at h
  rw [Fin.sum_univ_eq_sum_range (fun n => chainMoment φ ((SignedFull.chainAt (30637 + n)).map frameOfLabel))]
  exact h.symm

private theorem sigma_cost (φ : Nat → ℝ) (s : Nat) :
    evalL (fun r => φ (506 + r)) (SignedHistogramB.sigmaMoves s (AssignmentB.sigmaLabel s)) =
      φ (506 + (assignment.sigma s).rank) := by
  have hb := signed_rankValue_le SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) (AssignmentB.sigmaLabel s) (AssignmentB.sigmaLabel_valid s)
  unfold SignedHistogramB.sigmaMoves
  rw [evalL_eq_sum _ _ (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    omega)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hr : (assignment.sigma s).rank = (AssignmentB.sigmaLabel s).rankValue SignedFull.bankEntry :=
    Signed.Frame.rank_eval SignedFull.bankEntry SignedFull.bankSize
      (fun i _ => SignedFull.bankEntry_checked i) _ (AssignmentB.sigmaLabel_valid s)
  rw [hr]

/-- The exterior ranks are counted on the actual compiler's readout frames. -/
theorem sum_exterior_moment (φ : Nat → ℝ) :
    (∑ s : Slot, φ (506 + (assignment.sigma s).rank)) =
      evalH (fun r => φ (506 + r)) SignedHistogramB.sigmaHist := by
  have h := (hist_spec (fun r => φ (506 + r)) SignedHistogramB.sigmaMoves GeometryB.slotCount
    AssignmentB.sigmaTable 32768 0 KeyOrderB.sigmaTable_perfect (by
      intro i hi hs r hr
      unfold SignedHistogramB.sigmaMoves at hr
      rw [List.mem_singleton] at hr
      subst r
      have hb := signed_rankValue_le SignedFull.bankEntry SignedFull.bankSize
        (fun j _ => SignedFull.bankEntry_checked j) (AssignmentB.sigmaLabel i) (AssignmentB.sigmaLabel_valid i)
      change (AssignmentB.sigmaLabel i).rankValue SignedFull.bankEntry < 48
      omega)).2
  rw [SignedHistogramB.sigmaHist_checked] at h
  simp only [Nat.zero_add] at h
  change evalH (fun r => φ (506 + r)) SignedHistogramB.sigmaHist =
    ∑ i ∈ Finset.range 32768, if i < GeometryB.slotCount then
      evalL (fun r => φ (506 + r)) (SignedHistogramB.sigmaMoves i (AssignmentB.sigmaLabel i)) else 0 at h
  simp_rw [sigma_cost] at h
  rw [sum_range_padded _ _ _ (by decide)] at h
  rw [Fin.sum_univ_eq_sum_range (fun s => φ (506 + (assignment.sigma s).rank)), slot_count]
  exact h.symm

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
