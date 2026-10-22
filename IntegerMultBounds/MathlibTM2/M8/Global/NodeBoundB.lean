module

public import IntegerMultBounds.MathlibTM2.M8.Global.DataMomentsB

/-! The executed design-B node is bounded by its local side and data paths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem centre_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (hmono : Monotone φ)
    (b : Bool) (k : V) (c : Fin 23) : wireMoment φ (wCentre b k c) ≤ φ 22 := by
  have hnot : wCentre b k c ∉ sideWires := fun h => by
    obtain ⟨_, _, _, he⟩ := mem_sideWires.mp h
    simp [wCentre, wSide] at he
  have hst := starFrame_idem c.2
  rw [wireMoment_of_not_side φ hnot]
  cases b
  · rw [fseq_centre1, show fseq (.inr c) firstStage = _ from stage_temporary_trace assignment c,
      show gInit (wCentre false k c) = lift1 (lineOf k) (starFrame c) from rfl,
      List.map_cons, List.map_map]
    refine (chainMoment_temp φ hφ _ (lift1 (lineOf k) 0) _).trans (hmono ?_)
    rw [lift1_rank k (Matrix.zero_mul 0) hst (zero_le _), sub_zero]
    exact rank_starFrame_le c.2
  · rw [fseq_centre2, show fseq (.inr c) finalStage = _ from secondStage_temporary_trace assignment c,
      show gInit (wCentre true k c) = lift2 (lineOf k) (1 - starFrame c) from rfl,
      List.map_cons, List.map_map]
    refine (chainMoment_temp φ hφ _ (lift2 (lineOf k) 1) _).trans (hmono ?_)
    rw [rank_sub_comm, lift2_rank k (compl_idem hst) (Matrix.one_mul 1) (le_one _), sub_sub_cancel]
    exact rank_starFrame_le c.2

theorem corr_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (S T : V) :
    wireMoment φ (wCorr S T) ≤ φ 1 := by
  have hnot : wCorr S T ∉ sideWires := fun h => by
    obtain ⟨_, _, _, he⟩ := mem_sideWires.mp h
    simp [wCorr, wSide] at he
  rw [wireMoment_of_not_side φ hnot, fseq_wCorr, show gInit (wCorr S T) = 1 from rfl]
  have h := chainMoment_temp φ hφ (1 : Mat 529) (1 - uFrame S T) [0]
  rw [sub_sub_cancel, rank_uFrame] at h
  exact h

theorem junk_le (φ : Nat → ℝ) : wireMoment φ wJunk ≤ 0 := by
  have hnot : wJunk ∉ sideWires := fun h => by
    obtain ⟨_, _, _, he⟩ := mem_sideWires.mp h
    simp [wJunk, wSide] at he
  rw [wireMoment_of_not_side φ hnot, fseq_wJunk]
  exact le_rfl

/-- The independent row and column path costs, side costs, and owned temporaries. -/
def pathMomentBoundOf {α β γ : Type} (f g : α → ℝ) (h : β → ℝ) (x y z : ℝ) :
    ((α × α) ⊕ (α × α) ⊕ (Bool × α × β)) ⊕ ((Bool × α × γ) ⊕ (α × α) ⊕ Unit) → ℝ
  | .inl (.inl (S, T)) => f S + x + g T
  | .inl (.inr (.inl (S, T))) => g S + x + f T
  | .inl (.inr (.inr (_, _, s))) => h s
  | .inr (.inl _) => y
  | .inr (.inr (.inl _)) => z
  | .inr (.inr (.inr _)) => 0

theorem sum_pathMomentBoundOf {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f g : α → ℝ) (h : β → ℝ) (x y z : ℝ) :
    ∑ w, pathMomentBoundOf (γ := γ) f g h x y z w =
      2 * (Fintype.card α : ℝ) * ((∑ i, f i) + (∑ i, g i) + (∑ s, h s) + Fintype.card γ * y) +
        (Fintype.card α : ℝ) ^ 2 * (2 * x + z) := by
  simp only [Fintype.sum_sum_type, pathMomentBoundOf, Fintype.sum_prod_type,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_bool, Fintype.card_unit, Fintype.card_prod,
    ← Finset.mul_sum]
  push_cast
  ring

/-- Every local path and every exterior, connector and owned temporary is charged. -/
theorem node_moment_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (hmono : Monotone φ)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) :
    edgeMoment φ framedNode ≤
      2 * 1771 * ((∑ n : V, sourceMoment φ n) + (∑ t : V, targetMoment φ t) +
        (∑ s : Slot, (localMoment φ s + φ (506 + (assignment.sigma s).rank))) + 23 * φ 22) +
        (1771 : ℝ) ^ 2 * (2 * φ 484 + φ 1) := by
  rw [edgeMoment_node]
  let bound : Wire → ℝ := pathMomentBoundOf (fun n : V => sourceMoment φ n) (fun t : V => targetMoment φ t)
    (fun s : Slot => localMoment φ s + φ (506 + (assignment.sigma s).rank)) (φ 484) (φ 22) (φ 1)
  refine (Finset.sum_le_sum (g := bound) fun w _ => ?_).trans (le_of_eq ?_)
  · rcases w with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
    · exact wX_le φ hφ hsub S T
    · exact wY_le φ hφ hsub S T
    · exact le_of_eq (wireMoment_side_eq φ b k s)
    · exact centre_le φ hφ hmono b k c
    · exact corr_le φ hφ S T
    · exact junk_le φ
  · rw [show (∑ w, bound w) = _ from sum_pathMomentBoundOf (γ := Fin 23) (fun n : V => sourceMoment φ n)
      (fun t : V => targetMoment φ t) (fun s : Slot => localMoment φ s + φ (506 + (assignment.sigma s).rank))
      (φ 484) (φ 22) (φ 1), card_V1771, Fintype.card_fin]
    norm_num only [Nat.cast_ofNat]
/-- The data-wire terms are already bounded by their certified full signed chains. -/
theorem node_moment_le_data_chains (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (hmono : Monotone φ)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) :
    edgeMoment φ framedNode ≤
      2 * 1771 * ((∑ n : V, chainMoment φ ((SignedFull.chainAt (30637 + n)).map frameOfLabel)) +
        (∑ t : V, chainMoment φ ((SignedFull.chainAt (28866 + t)).map frameOfLabel)) +
        (∑ s : Slot, (localMoment φ s + φ (506 + (assignment.sigma s).rank))) + 23 * φ 22) +
        (1771 : ℝ) ^ 2 * (2 * φ 484 + φ 1) := by
  have hx : (∑ n : V, sourceMoment φ n) ≤
      ∑ n : V, chainMoment φ ((SignedFull.chainAt (30637 + n)).map frameOfLabel) :=
    Finset.sum_le_sum (fun n _ => sourceMoment_le φ hφ hsub n n.2)
  have hy : (∑ t : V, targetMoment φ t) ≤
      ∑ t : V, chainMoment φ ((SignedFull.chainAt (28866 + t)).map frameOfLabel) :=
    Finset.sum_le_sum (fun t _ => targetMoment_le φ hφ hsub t t.2)
  have h := node_moment_le φ hφ hmono hsub
  linarith


end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
