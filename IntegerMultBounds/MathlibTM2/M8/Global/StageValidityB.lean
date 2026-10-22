module

public import IntegerMultBounds.MathlibTM2.M8.Global.StageGateB

/-! Frame validity and gate legality of both actual design-B stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Reflection preserves every gate property invariant under frame complementation. -/
theorem secondStage_property (F : FrameAssignment) (P : FGate LW 23 → Prop)
    (h : ∀ v ∈ stage F, P v)
    (hc : ∀ v, P v → P ⟨v.gate, 1 - v.frame⟩) :
    ∀ v ∈ secondStage F, P v := by
  have hpre (v) (hv : v ∈ (preBlocks F).flatten) : P v :=
    h v (by rw [stage, blocks, List.flatten_append, List.flatten_append];
            exact List.mem_append_left _ (List.mem_append_left _ hv))
  have hpost (v) (hv : v ∈ (postBlocks F).flatten) : P v :=
    h v (by rw [stage, blocks, List.flatten_append, List.flatten_append];
            exact List.mem_append_right _ hv)
  have hcentre (c : Fin 23) (v) (hv : v ∈ centreBlockAt centreSlots centreTargets c) : P v := by
    apply h v
    rw [stage, blocks, List.flatten_append, List.flatten_append]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c, List.mem_finRange c, rfl⟩, hv⟩
  intro v hv
  simp only [secondStage, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hc u (hpost u (List.mem_reverse.mp hu))
  · obtain ⟨B, hB, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hB
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hc u (hcentre c u hu)
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hc u (hpre u (List.mem_reverse.mp hu))

theorem secondStage_gate_good (F : FrameAssignment) :
    ∀ v ∈ secondStage F, GateGood v.gate :=
  secondStage_property F (fun v => GateGood v.gate) (stage_gate_good F) (fun _ h => h)

/-- A frame predicate on an arbitrary assignment extends to its entire stage. -/
theorem stage_frame_property (F : FrameAssignment) (P : LMat → Prop)
    (h0 : P 0) (h1 : P 1) (hstar : ∀ c : Fin 23, P (starFrame c))
    (hsigma : ∀ s, P (F.sigma s)) (hsource : ∀ op, P (F.source op))
    (hside : ∀ op, P (F.side op)) (hout : ∀ j, P (F.output j)) :
    ∀ v ∈ stage F, P v.frame := by
  have hread (ss : List Nat) : ∀ v ∈ (readBlocks F ss).flatten, P v.frame := by
    intro v hv
    obtain ⟨B, hB, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨s, _, hB⟩ := List.mem_flatMap.mp hB
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hB
    have he := List.mem_singleton.mp hv
    subst v
    exact hsigma s
  have hop (ops : List Op) (f : Op → LMat) (hf : ∀ op, P (f op)) :
      ∀ v ∈ (opBlocks ops f).flatten, P v.frame := by
    intro v hv
    obtain ⟨B, hB, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨op, _, rfl⟩ := List.mem_map.mp hB
    have he := List.mem_singleton.mp hv
    subst v
    exact hf op
  have houtput : ∀ v ∈ (outBlocks F).flatten, P v.frame := by
    intro v hv
    obtain ⟨B, hB, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨j, _, hB⟩ := List.mem_flatMap.mp hB
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hB
    have he := List.mem_singleton.mp hv
    subst v
    exact hout j
  intro v hv
  simp only [stage, blocks, preBlocks, postBlocks, List.flatten_append,
    List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · rcases hv with (hv | hv) | hv
    · exact hread _ v hv
    · exact hop _ _ hsource v hv
    · exact hop _ _ hside v hv
  · obtain ⟨B, hB, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hB
    rw [centreBlockAt, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hstar c
    · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hv
      exact h0
  · rcases hv with (((hv | hv) | hv) | hv) | hv
    · exact hread _ v hv
    · exact hop _ _ hsource v hv
    · exact hop _ _ hside v hv
    · exact houtput v hv
    · exact hop _ _ (fun _ => h1) v hv

/-- Both orientations of every actual stage frame satisfy the local coefficient cap. -/
theorem firstStage_frames (v : FGate LW 23) (hv : v ∈ firstStage) :
    LFrame v.frame ∧ LFrame (1 - v.frame) := by
  apply stage_frame_property assignment (fun K => LFrame K ∧ LFrame (1 - K))
      ⟨lframe_zero, by simpa only [sub_zero] using lframe_one⟩
      ⟨lframe_one, by simpa only [sub_self] using lframe_zero⟩
      (fun c => ⟨(smallFrame_star c.2).lframe, (smallFrame_star c.2).compl⟩)
      (fun s => ⟨sigma_lframe s, sigma_compl_lframe s⟩) ?_ ?_ ?_ v hv
  · intro op
    exact ⟨source_lframe op,
      frameOfLabel_compl_lframe _ (AssignmentB.startLabel_valid op.target)⟩
  · intro op
    refine ⟨side_lframe op, ?_⟩
    cases op with
    | src s _ | copy _ s _ =>
      exact frameOfLabel_compl_lframe _ (AssignmentB.startLabel_valid s)
    | add _ _ n => exact frameOfLabel_compl_lframe _ (AssignmentB.nodeLabel_valid n)
  · intro j
    refine ⟨output_lframe j, ?_⟩
    dsimp only [assignment]
    split_ifs with h
    · simpa only [hyperFrame, sub_sub_cancel] using
        lframe_of (lineFrame_idem ⟨leafTriple_card h, leafTriple_lt h⟩)
          (lineFrame_bounded ⟨leafTriple_card h, leafTriple_lt h⟩)
    · simpa only [sub_zero] using lframe_one

theorem finalStage_frames (v : FGate LW 23) (hv : v ∈ finalStage) :
    LFrame v.frame ∧ LFrame (1 - v.frame) := by
  apply secondStage_property assignment (fun v => LFrame v.frame ∧ LFrame (1 - v.frame))
    firstStage_frames ?_ v hv
  intro u hu
  exact ⟨hu.2, by simpa only [sub_sub_cancel] using hu.1⟩

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
