module

public import IntegerMultBounds.MathlibTM2.M8.Global.CompilerFramesB
public import IntegerMultBounds.MathlibTM2.M8.Local.FrameBirth
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.SlotFacts

/-! Compiler wire chains start at their declared slot frame and finish at
an explicit root-use frame. These are the interfaces for boundary readouts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames

/-- All frames on a compiler prefix lie above the slot's start frame. -/
theorem compilerTo_start_bound (k : Nat) (hk : k ≤ nodeCount) (s : Nat) :
    (frameOfLabel (AssignmentB.startLabel s) ::
      FrameFlow.framesOf opFrame s ((dagB.compileTo k).ops.map dagB.vop)).Pairwise Nested := by
  let : IsTrans LMat Nested := ⟨fun _ _ _ h h' => h.trans h'⟩
  have hchain := compilerTo_aux_chain
    (fun n hv hn pos => GeometryB.argument_nested n hv hn pos)
    (fun n hv hn => GeometryB.copies_chain n hv hn) k hk s
  rw [fseq_opBlocks] at hchain
  have hp := List.isChain_iff_pairwise.mp hchain
  apply List.pairwise_cons.mpr
  refine ⟨?_, hp⟩
  by_cases hs : s < (dagB.compileTo k).next
  · have hh : (FrameFlow.framesOf opFrame s ((dagB.compileTo k).ops.map dagB.vop)).head? =
        some (frameOfLabel (AssignmentB.startLabel s)) := by
      rw [opFrame_eq_opLabel]
      exact FrameFlow.compileTo_head dagB dagB_valid _ _ k hk s hs
    have hi := frameOfLabel_idem _ (AssignmentB.startLabel_valid s)
    exact FrameFlow.pairwise_head_bound Nested _ _ hp hh ⟨hi, hi⟩
  · have hf := FrameFlow.compileTo_frames_fresh dagB dagB_valid opFrame k hk s
      (Nat.le_of_not_gt hs)
    rw [hf]
    simp

theorem compiler_start_bound (s : Nat) :
    (frameOfLabel (AssignmentB.startLabel s) ::
      fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten).Pairwise Nested := by
  rw [fseq_opBlocks, Dag.opsB, Dag.compile]
  exact compilerTo_start_bound dagB.N le_rfl s

theorem freeLabel_valid (n i : Nat) :
    (freeLabel n i).validCheck SignedFull.bankSize = true := by
  unfold freeLabel AssignmentB.freeUseLabel
  split_ifs <;> first | exact AssignmentB.startLabel_valid _ | exact AssignmentB.nodeLabel_valid _

theorem rootLabel_valid (j : Nat) : (rootLabel j).validCheck SignedFull.bankSize = true :=
  freeLabel_valid _ _

/-- Every compiler frame touching a final read slot lies below its root frame. -/
theorem compiler_root_bound (j : Nat) (hj : j < rootCount) :
    ∀ f ∈ fseq (.inl (.aux (dagB.compile.pend (.root j)))) (opBlocks dagB.opsB opFrame).flatten,
      Nested f (frameOfLabel (rootLabel j)) := by
  have hp := compiler_aux_pairwise (dagB.compile.pend (.root j))
  rw [fseq_opBlocks, Dag.opsB] at hp ⊢
  have hl := root_frame j hj
  rw [FrameFlow.last_getLast] at hl
  have hi := frameOfLabel_idem _ (rootLabel_valid j)
  exact FrameFlow.pairwise_last_bound Nested _ _ hp hl ⟨hi, hi⟩

theorem compiler_slot_count : dagB.compile.next = GeometryB.slotCount := by
  rw [Dag.compile, dagB_compileTo_next dagB.N le_rfl]
  exact GeometryB.slotsBefore_final

/-- An allocated wire's readout frame lies below every compiler frame on it. -/
theorem compiler_readout_bound (s : Nat) (hs : s < dagB.compile.next) :
    (assignment.sigma s ::
      fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten).Pairwise Nested := by
  have hp := List.pairwise_cons.mp (compiler_start_bound s)
  have he : Nested (assignment.sigma s) (frameOfLabel (AssignmentB.startLabel s)) :=
    GeometryB.sigma_start_nested s (by rwa [compiler_slot_count] at hs)
  exact List.pairwise_cons.mpr ⟨fun f hf => he.trans (hp.1 f hf), hp.2⟩

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
