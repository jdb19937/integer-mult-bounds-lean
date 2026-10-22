module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeBoundB
public import IntegerMultBounds.MathlibTM2.M8.Global.AuxMomentsB

/-! Every executed path is bounded by the canonical signed chains; all other charges remain explicit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The actual node's complete cost is bounded by signed chains, exteriors and owned temporaries. -/
theorem node_moment_le_signed_chains (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (hmono : Monotone φ)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) :
    edgeMoment φ framedNode ≤
      2 * 1771 * ((∑ n : V, chainMoment φ ((SignedFull.chainAt (30637 + n)).map frameOfLabel)) +
        (∑ t : V, chainMoment φ ((SignedFull.chainAt (28866 + t)).map frameOfLabel)) +
        (∑ s : Slot, (chainMoment φ (auxiliaryChain s) + φ (506 + (assignment.sigma s).rank))) + 23 * φ 22) +
        (1771 : ℝ) ^ 2 * (2 * φ 484 + φ 1) := by
  have hs : (∑ s : Slot, (localMoment φ s + φ (506 + (assignment.sigma s).rank))) ≤
      ∑ s : Slot, (chainMoment φ (auxiliaryChain s) + φ (506 + (assignment.sigma s).rank)) := by
    apply Finset.sum_le_sum
    intro s _
    have hs' : s.val < GeometryB.slotCount := lt_of_lt_of_eq s.2 slot_count
    have hslot := localMoment_le_chain φ hφ hsub s.val hs'
    linarith
  have h := node_moment_le_data_chains φ hφ hmono hsub
  linarith

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
