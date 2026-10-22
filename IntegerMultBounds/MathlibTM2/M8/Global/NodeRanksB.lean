module

public import IntegerMultBounds.MathlibTM2.M8.Global.RankMoments
public import IntegerMultBounds.MathlibTM2.M8.Stage2LinkB
public import IntegerMultBounds.MathlibTM2.M8.Rev.Node

/-! Every executed design-B exchange has rank below the recursive width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

private theorem sourceMoment_linear (n : V) : sourceMoment (fun r => (r : ℝ)) n = 22 := by
  have hp := (firstStage_source_chain n n.2).imp le_of_nested
  have hi := padded_fseq_idem firstStage (fun v hv => (firstStage_frames v hv).1.idem)
    (Sum.inl (Reg.x n) : LW) (lineFrame (leafTriple n)) 1
    (lineFrame_idem (leafTriple_isTriple n.2)) (Matrix.one_mul 1)
  simp only [List.cons_append] at hp hi
  have h := chainMoment_linear (lineFrame (leafTriple n)) 1
    (fseq (Sum.inl (Reg.x n) : LW) firstStage) hp hi
  rw [rank_lineFrame (leafTriple_isTriple n.2), Matrix.rank_one, Fintype.card_fin] at h
  norm_num at h
  simpa only [sourceMoment, List.cons_append] using h

private theorem targetMoment_linear (t : V) : targetMoment (fun r => (r : ℝ)) t = 22 := by
  have hp := (firstStage_target_chain t t.2).imp le_of_nested
  have hi := padded_fseq_idem firstStage (fun v hv => (firstStage_frames v hv).1.idem)
    (Sum.inl (Reg.y t) : LW) 0 (hyperFrame (leafTriple t))
    (Matrix.zero_mul 0) (hyperFrame_idem (leafTriple_isTriple t.2))
  simp only [List.cons_append] at hp hi
  have h := chainMoment_linear 0 (hyperFrame (leafTriple t))
    (fseq (Sum.inl (Reg.y t) : LW) firstStage) hp hi
  rw [hyper_V, rank_compl_lineOf, Matrix.rank_zero] at h
  norm_num at h
  simpa only [targetMoment, hyper_V, List.cons_append] using h

/-- Indicator for exchanges that would recurse at full width. -/
private def fullRank (r : Nat) : Nat := if 529 ≤ r then 1 else 0

private theorem fullRank_le (r : Nat) : 529 * fullRank r ≤ r := by
  unfold fullRank
  split_ifs <;> omega

private theorem stepMoment_fullRank {d : Nat} {A B : Mat d} (h : (A - B).rank < 529) :
    stepMoment fullRank A B = 0 := by
  rw [stepMoment_eq]
  split_ifs
  · rfl
  · unfold fullRank
    split_ifs <;> omega

private theorem local_fullRank : ∀ fs : List LMat, chainMoment fullRank fs = 0
  | [] => rfl
  | [_] => rfl
  | a :: b :: fs => by
    rw [chainMoment_cons_cons, local_fullRank (b :: fs), add_zero]
    exact stepMoment_fullRank (lt_of_le_of_lt (Matrix.rank_le_width _) (by norm_num))

private theorem wireMoment_scale_le {φ ψ : Nat → Nat} {c : Nat} (h : ∀ r, c * φ r ≤ ψ r) (w : Wire) :
    c * wireMoment φ w ≤ wireMoment ψ w := by
  unfold wireMoment
  rw [mul_add]
  apply Nat.add_le_add (chainMoment_nat_scale_le h _) ?_
  split_ifs
  · rw [mul_add]
    apply Nat.add_le_add ?_ (h _)
    rw [stepMoment, stepMoment]
    split_ifs
    · simp
    · exact h _
  · simp

private theorem wireMoment_cast (φ : Nat → Nat) (w : Wire) :
    wireMoment (fun r => (φ r : ℝ)) w = ((wireMoment φ w : Nat) : ℝ) := by
  simp only [wireMoment, chainMoment_nat_cast, Nat.cast_add, Nat.cast_ite, Nat.cast_zero,
    stepMoment_nat_cast]

private theorem wireMoment_fullRank_of_le (w : Wire)
    (h : wireMoment (fun r => (r : ℝ)) w ≤ 528) : wireMoment fullRank w = 0 := by
  have h1 := wireMoment_scale_le (ψ := fun r => r) fullRank_le w
  rw [wireMoment_cast (fun r => r) w] at h
  have h2 : wireMoment (fun r => r) w ≤ 528 := by exact_mod_cast h
  omega

private theorem side_fullRank (b : Bool) (k : V) (s : Slot) : wireMoment fullRank (wSide b k s) = 0 := by
  rw [wireMoment_side_eq, localMoment, local_fullRank, zero_add]
  have hs : s.val < 28866 := lt_of_lt_of_eq s.2 slot_count
  have hr := AssignmentB.sigma_rank_le s hs
  change (assignment.sigma s).rank ≤ 22 at hr
  simp only [fullRank, ite_eq_right (by omega : ¬529 ≤ 506 + (assignment.sigma s).rank)]

/-- Every individual wire has no exchange of full rank. -/
private theorem wireMoment_fullRank (w : Wire) : wireMoment fullRank w = 0 := by
  have h0 : ∀ n : Nat, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have hm : Monotone (fun r : Nat => (r : ℝ)) := Nat.mono_cast
  have ha : ∀ a b : Nat, (((a + b : Nat) : ℝ)) ≤ (a : ℝ) + b := by intros; push_cast; rfl
  rcases w with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · apply wireMoment_fullRank_of_le
    have h := wX_le _ h0 ha S T
    rw [sourceMoment_linear, targetMoment_linear] at h
    exact h.trans (by norm_num)
  · apply wireMoment_fullRank_of_le
    have h := wY_le _ h0 ha S T
    rw [sourceMoment_linear, targetMoment_linear] at h
    exact h.trans (by norm_num)
  · exact side_fullRank b k s
  · exact wireMoment_fullRank_of_le _ ((centre_le _ h0 hm b k c).trans (by norm_num))
  · exact wireMoment_fullRank_of_le _ ((corr_le _ h0 S T).trans (by norm_num))
  · exact wireMoment_fullRank_of_le _ ((junk_le _).trans (by norm_num))

private theorem edgeMoment_eq_sum {M : Type} [AddCommMonoid M] (φ : Nat → M) :
    ∀ L : List (FStep Wire 529), edgeMoment φ L = ((Rev.edgeMats L).map fun U => φ U.rank).sum
  | [] => rfl
  | s :: rest => by cases s <;> simp [edgeMoment, Rev.edgeMats, edgeMoment_eq_sum φ rest]

/-- All block children of the reversed programs are strictly smaller than the node. -/
theorem rank_lt {U : Mat 529} (hU : U ∈ Rev.edgeMats framedNode) : U.rank < 529 := by
  have h : edgeMoment fullRank framedNode = 0 := by
    rw [edgeMoment_node]
    exact Finset.sum_eq_zero fun w _ => wireMoment_fullRank w
  rw [edgeMoment_eq_sum] at h
  have hU' := List.sum_eq_zero_iff.mp h _ (List.mem_map.mpr ⟨U, hU, rfl⟩)
  unfold fullRank at hU'
  split_ifs at hU'; omega

/-- The generic-basis degree budget remains valid for the actual gauged node. -/
theorem calls_node_le : calls (physOf framedNode) ≤ 57403754177 := by
  have h := Stage2Moments.edgeMomentB_le_histogram (fun r => (r : ℝ))
    (fun r => Nat.cast_nonneg r) Nat.mono_cast (by intros; push_cast; rfl)
  have hm : Stage2Moments.histMoment (fun r => (r : ℝ)) Stage2Moments.histogramB = 57403754177 := by
    norm_num [Stage2Moments.histMoment, Stage2Moments.histogramB]
  rw [edgeMoment_linear, hm] at h
  rw [calls_physOf]
  exact_mod_cast h

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
