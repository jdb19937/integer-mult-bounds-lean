module

public import IntegerMultBounds.MathlibTM2.M8.Global.LocalMomentsB
public import IntegerMultBounds.MathlibTM2.M8.Global.AuxTraceCoverageB
public import IntegerMultBounds.MathlibTM2.M8.Global.SlotAssignmentB
public import IntegerMultBounds.MathlibTM2.M8.Local.CompilerCoverage
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Facts
public import IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookupMoments

/-! The actual auxiliary paths refine the canonical signed slot chains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The canonical chain assigned to an allocated physical slot. -/
def auxiliaryChain (s : Nat) : List LMat :=
  (SignedFull.chainAt (AuxCoverageB.chainIndex s)).map frameOfLabel

private theorem label_mem (s : Nat) (f : Signed.Frame)
    (hf : f ∈ SignedFull.chainAt (AuxCoverageB.chainIndex s)) : frameOfLabel f ∈ auxiliaryChain s :=
  List.mem_map.mpr ⟨f, hf, rfl⟩

/-- All compiler frames belong to the canonical chain of their actual physical slot. -/
theorem compiler_aux_mem (s : Nat) (hs : s < GeometryB.slotCount) :
    ∀ F ∈ fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten, F ∈ auxiliaryChain s := by
  let P := fun s (f : Signed.Frame) => s < GeometryB.slotCount →
    f ∈ SignedFull.chainAt (AuxCoverageB.chainIndex s)
  have hc := FrameFlow.compileTo_covered dagB AssignmentB.nodeLabel AssignmentB.startLabel P
    (fun s hs => (AuxCoverageB.slot_parts s hs).2.2.1)
    (fun n hv hn pos => by
      intro _
      rw [argument_slotB n hv hn pos]
      exact AuxCoverageB.node_mem n hv hn pos)
    (fun n hv hn f hf => by
      intro _
      rw [dagB_compileTo_next n (Nat.le_of_lt hn), dagB_freeUses_eq n hn] at hf
      have hp : (dagB.compileTo n).pend (dagB.pivotUse n) =
          SlotAssignmentB.slotOf (dagB.pivotUse n) := by
        unfold Dag.pivotUse
        exact argument_slotB n hv hn _
      rw [hp, ← pivotSlot_eq]
      exact AuxCoverageB.copy_mem n hv hn f hf)
    dagB.N (Nat.le_refl _)
  have hc' : FrameFlow.Covered (FrameFlow.opLabel AssignmentB.nodeLabel AssignmentB.startLabel) P dagB.opsB := by
    simpa only [Dag.opsB, Dag.compile] using hc
  intro F hF
  rw [fseq_opBlocks, FrameFlow.framesOf] at hF
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hF
  obtain ⟨hop, hsop⟩ := List.mem_filter.mp hop
  have hm := hc' op hop s (of_decide_eq_true hsop) hs
  have he : opFrame op = frameOfLabel (FrameFlow.opLabel AssignmentB.nodeLabel AssignmentB.startLabel op) := by
    cases op <;> rfl
  rw [he]
  exact label_mem s _ hm

/-- The checked root complement has rank 22. -/
theorem auxiliary_endpoint_rank (j : Nat) (hj : j < rootCount) :
    (frameOfLabel (.negative (GeometryB.endpointTree.get 8192 j).2)).rank = 22 := by
  have h := RootBank.Record.rank _
    (SignedFull.bankEntry_checked (GeometryB.endpointTree.get 8192 j).2)
  rw [(AuxCoverageB.root_parts j hj).2.2] at h
  exact h

/-- The root endpoint on an output slot is the actual output hyperplane. -/
theorem auxiliary_output_endpoint (j : Nat) (hj : j < 3 * leafCount) :
    frameOfLabel (.negative (GeometryB.endpointTree.get 8192 j).2) = assignment.output j := by
  have hr := out_root_lt hj
  let w := GeometryB.endpointTree.get 8192 j
  have hc := SignedFull.bankEntry_checked w.2
  have hspan := (GeometryB.rootOk_complement j w (GeometryB.rootOk_at j hr)).2
  rw [rootCode_output j hj] at hspan
  have he := rootFrame_le_hyper_of_unit (RootBank.Record.check_spec hc).2.1 hspan
  have ht : j / 3 < leafCount := by omega
  have hH := rank_sub_of_le (lineFrame_idem (leafTriple_isTriple ht))
    (Matrix.one_mul (1 : LMat)) (le_one (lineFrame (leafTriple (j / 3))))
  rw [rank_lineFrame (leafTriple_isTriple ht), Matrix.rank_one, Fintype.card_fin] at hH
  have heq := eq_of_le_rank_eq (RootBank.Record.idem _ hc) (hyperFrame_idem (leafTriple_isTriple ht))
    (le_of_nested he) (by
      have h := auxiliary_endpoint_rank j hr
      change (rootFrame (SignedFull.bankEntry w.2).basis).rank = 22 at h
      change (rootFrame _).rank = (1 - lineFrame (leafTriple (j / 3))).rank
      omega)
  simpa only [frameOfLabel, Signed.Frame.eval, assignment, ite_eq_left ht, w] using heq

/-- The endpoint on a retained centre is exactly its star frame. -/
theorem auxiliary_centre_endpoint (c : Fin 23) :
    frameOfLabel (.negative (GeometryB.endpointTree.get 8192 (3 * leafCount + c.val)).2) = starFrame c.val := by
  let j := 3 * leafCount + c.val
  let w := GeometryB.endpointTree.get 8192 j
  have hc := SignedFull.bankEntry_checked w.2
  have hspan := (GeometryB.rootOk_complement j w (GeometryB.rootOk_at j (centre_root_lt c))).2
  rw [rootCode_centre] at hspan
  have he := rootFrame_le_star_of_unit (RootBank.Record.check_spec hc).2.1 c.isLt hspan
  exact eq_of_le_rank_eq (RootBank.Record.idem _ hc) (starFrame_idem c.isLt)
    (le_of_nested he) ((auxiliary_endpoint_rank j (centre_root_lt c)).trans (starFrame_rank c.isLt).symm)

/-- Every retained or output root frame belongs to its slot's canonical chain. -/
theorem auxiliary_root_mem (j : Nat) (hj : j < rootCount) :
    frameOfLabel (.negative (GeometryB.endpointTree.get 8192 j).2) ∈
      auxiliaryChain (dagB.compile.pend (.root j)) := by
  apply label_mem
  rw [root_slotB j hj, ← (AuxCoverageB.root_parts j hj).1]
  exact (AuxCoverageB.root_parts j hj).2.1

/-- All boundaries and compiler frames are covered, including uncompute frame one. -/
theorem local_path_mem (s : Nat) (hs : s < GeometryB.slotCount) :
    ∀ F ∈ assignment.sigma s :: fseq (Sum.inl (Reg.aux s) : LW) firstStage ++ [1], F ∈ auxiliaryChain s := by
  have hσ : assignment.sigma s ∈ auxiliaryChain s := label_mem s _ (AuxCoverageB.slot_parts s hs).2.1
  have hone : (1 : LMat) ∈ auxiliaryChain s := label_mem s _ (AuxCoverageB.slot_parts s hs).2.2.2
  have htrace := firstStage_aux_property s (fun F => F ∈ auxiliaryChain s) hσ (compiler_aux_mem s hs)
    (fun c hc => by
      rw [hc]
      have h := auxiliary_root_mem _ (centre_root_lt c)
      rw [auxiliary_centre_endpoint c] at h
      exact h)
    (fun j hj hc => by
      rw [hc]
      have h := auxiliary_root_mem j (out_root_lt (output_root_lt hj))
      rw [auxiliary_output_endpoint j (output_root_lt hj)] at h
      exact h) hone
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact hσ
    · exact htrace F hF
  · rw [List.mem_singleton.mp hF]
    exact hone

/-- Repeated and skipped frames cannot increase the canonical auxiliary moment. -/
theorem localMoment_le_chain (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (s : Nat) (hs : s < GeometryB.slotCount) :
    localMoment φ s ≤ chainMoment φ (auxiliaryChain s) := by
  apply chainMoment_le_of_subset φ hφ hsub
    (local_pairwise s (by rw [compiler_slot_count]; exact hs))
    ((Signed.chainCheck_pairwise SignedFull.bankEntry SignedFull.bankSize
      (fun i _ => SignedFull.bankEntry_checked i) _ (SignedFull.chainAt_checked _)).imp le_of_nested)
  · exact local_path_mem s hs
  · intro F hF
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
    exact frameOfLabel_idem _ (Signed.chainCheck_valid SignedFull.bankEntry SignedFull.bankSize
      _ (SignedFull.chainAt_checked _) f hf)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
