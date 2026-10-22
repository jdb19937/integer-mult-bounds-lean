module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeTraceB

/-! Every aligned move in the gauged design-B node follows comparable frames. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Splice two increasing paths through a comparable pair of endpoints. -/
theorem pairwise_splice {d : Nat} {a b c e : Mat d} {xs ys : List (Mat d)}
    (hx : (a :: xs ++ [b]).Pairwise Le) (hy : (c :: ys ++ [e]).Pairwise Le)
    (hbc : Le b c) : (a :: xs ++ ys ++ [e]).Pairwise Le := by
  obtain ⟨hxs, _, hxend⟩ := List.pairwise_append.mp hx
  change (c :: (ys ++ [e])).Pairwise Le at hy
  obtain ⟨hystart, hys⟩ := List.pairwise_cons.mp hy
  have h := pw_app hxs hys fun x hx y hy =>
    le_trans' (le_trans' (hxend x hx b (List.mem_singleton_self b)) hbc) (hystart y hy)
  simpa only [List.cons_append, List.append_assoc] using h

/-- Data sources climb through both lifted paths and end at the correction's frame one. -/
theorem pairwise_wX (S T : V) : (gInit (wX S T) :: fseq (wX S T) allGates).Pairwise Le := by
  have h1 := pairwise_map_lift (le_lift1 (lineOf_idem T))
    ((firstStage_source_chain S S.2).imp le_of_nested)
  have h2 := pairwise_map_lift (le_lift2 (lineOf_idem S))
    ((finalStage_target_chain T T.2).imp le_of_nested)
  simp only [List.map_cons, List.map_append] at h1 h2
  rw [hyper_V, sub_sub_cancel, lift2_one] at h2
  rw [fseq_wX]
  exact pairwise_splice h1 h2 (connector_x (lineOf_idem T))

/-- Data targets climb to the complementary data gauge used by the correction. -/
theorem pairwise_wY (S T : V) : (gInit (wY S T) :: fseq (wY S T) allGates).Pairwise Le := by
  have h1 := pairwise_map_lift (le_lift1 (lineOf_idem T))
    ((firstStage_target_chain S S.2).imp le_of_nested)
  have h2 := pairwise_map_lift (le_lift2 (lineOf_idem S))
    ((finalStage_source_chain T T.2).imp le_of_nested)
  simp only [List.map_cons, List.map_append] at h1 h2
  rw [hyper_V, lift1_zero] at h1
  rw [lift2_compl] at h2
  rw [fseq_wY]
  exact pairwise_splice h1 h2 (connector_y (lineOf_idem S))

theorem pairwise_side1 (T : V) (s : Slot) :
    (gInit (wSide false T s) :: fseq (wSide false T s) allGates).Pairwise Le := by
  have hs : s.val < dagB.compile.next := by rw [compiler_slots_eq_plain]; exact s.2
  rw [fseq_side1]
  exact pairwise_map_lift (le_lift1 (lineOf_idem T))
    ((firstStage_aux_chain s hs).imp le_of_nested)

theorem pairwise_side2 (S : V) (s : Slot) :
    (gInit (wSide true S s) :: fseq (wSide true S s) allGates).Pairwise Le := by
  have hs : s.val < dagB.compile.next := by rw [compiler_slots_eq_plain]; exact s.2
  have h := (List.pairwise_append.mp ((finalStage_aux_chain s hs).imp le_of_nested)).1
  rw [fseq_side2]
  change (lift2 (lineOf S) 0 :: (fseq (.inl (.aux s)) finalStage).map (lift2 (lineOf S))).Pairwise Le
  rw [← List.map_cons]
  apply pairwise_map_lift (le_lift2 (lineOf_idem S))
  exact List.pairwise_cons.mpr ⟨fun K _ => zero_le K, h⟩

/-- Every physical alignment move of the actual node is between comparable frames. -/
theorem chainOk_node : ChainOk gInit allGates := by
  intro k
  rcases k with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · exact chain_of_pairwise (pairwise_wX S T)
  · exact chain_of_pairwise (pairwise_wY S T)
  · cases b
    · exact chain_of_pairwise (pairwise_side1 k s)
    · exact chain_of_pairwise (pairwise_side2 k s)
  · cases b
    · show (gInit (wCentre false k c) :: fseq (wCentre false k c) allGates).IsChain Cmp
      rw [fseq_centre1, show fseq (.inr c) firstStage = _ from stage_temporary_trace assignment c]
      change (lift1 (lineOf k) (starFrame c) ::
        (starFrame c :: (centreTargets c).map (fun _ => (0 : LMat))).map (lift1 (lineOf k))).IsChain Cmp
      rw [List.map_cons, List.map_map]
      exact chain_temp (lframe_lift1 k (smallFrame_star c.2).lframe).idem
        (lframe_lift1 k lframe_zero).idem
        (Or.inr (le_lift1 (lineOf_idem k) (zero_le _))) _
    · show (gInit (wCentre true k c) :: fseq (wCentre true k c) allGates).IsChain Cmp
      rw [fseq_centre2, show fseq (.inr c) finalStage = _ from secondStage_temporary_trace assignment c]
      change (lift2 (lineOf k) (1 - starFrame c) ::
        ((1 - starFrame c) :: (centreTargets c).map (fun _ => (1 : LMat))).map (lift2 (lineOf k))).IsChain Cmp
      rw [List.map_cons, List.map_map]
      exact chain_temp (lframe_lift2 k (smallFrame_star c.2).compl).idem
        (lframe_lift2 k lframe_one).idem
        (Or.inl (le_lift2 (lineOf_idem k) (le_one _))) _
  · show (gInit (wCorr S T) :: fseq (wCorr S T) allGates).IsChain Cmp
    rw [fseq_wCorr]
    change ([1, 1, 1 - uFrame S T] : List (Mat 529)).IsChain Cmp
    rw [List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨Or.inl (le_refl_of_idem (by simp)), Or.inr (le_one _), List.isChain_singleton _⟩
  · show (gInit wJunk :: fseq wJunk allGates).IsChain Cmp
    rw [fseq_wJunk]
    exact List.isChain_singleton _

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
