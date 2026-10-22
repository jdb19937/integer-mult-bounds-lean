module

public import IntegerMultBounds.MathlibTM2.M8.Global.AuxStageFramesB
public import IntegerMultBounds.MathlibTM2.M8.Local.WordOrderB

/-! Actual side-slot traces finish at one, supplying the gauged exit's input frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Every allocated V-compiler slot is touched by an operation. -/
theorem allocated_slot_touched (s : Nat) (hs : s < dagB.compile.next) :
    ∃ op ∈ dagB.opsB, s ∈ op.slots := by
  have hh : (FrameFlow.framesOf (FrameFlow.opLabel (fun _ => (0 : Nat)) (fun _ => 0)) s dagB.opsB).head? = some 0 := by
    exact FrameFlow.compileTo_head dagB dagB_valid _ _ nodeCount le_rfl s hs
  have hn : FrameFlow.framesOf (FrameFlow.opLabel (fun _ => (0 : Nat)) (fun _ => 0)) s dagB.opsB ≠ [] := by
    intro he
    rw [he] at hh
    cases hh
  have hf : (dagB.opsB.filter fun op => decide (s ∈ op.slots)) ≠ [] := by
    intro he
    apply hn
    simp only [FrameFlow.framesOf, he, List.map_nil]
  obtain ⟨op, ho⟩ := List.exists_mem_of_ne_nil _ hf
  exact ⟨op, (List.mem_filter.mp ho).1, of_decide_eq_true (List.mem_filter.mp ho).2⟩

/-- Uncompute touches every allocated side slot at frame one. -/
theorem uncompute_aux_last (s : Nat) (hs : s < dagB.compile.next) :
    (fseq (.inl (.aux s))
      (opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
        dagB.opsRest planB).reverse (fun _ => 1)).flatten).getLast? = some 1 := by
  obtain ⟨op, ho, hslot⟩ := allocated_slot_touched s hs
  have hm : (1 : LMat) ∈ fseq (.inl (.aux s))
      (opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
        dagB.opsRest planB).reverse (fun _ => 1)).flatten := by
    rw [fseq_opBlocks]
    apply List.mem_map.mpr
    refine ⟨op, List.mem_filter.mpr ⟨?_, by simpa using hslot⟩, rfl⟩
    exact List.mem_reverse.mpr ((dagB.orderedOps_perm planB).mem_iff.mpr ho)
  have hn := List.ne_nil_of_mem hm
  rw [List.getLast?_eq_some_getLast hn]
  congr 1
  exact opBlocks_const_frame _ 1 _ _ (List.getLast_mem hn)

/-- The actual first stage ends every side slot at frame one. -/
theorem firstStage_aux_last (s : Nat) (hs : s < dagB.compile.next) :
    (fseq (.inl (.aux s)) firstStage).getLast? = some 1 := by
  have hp : ∃ headGates : List (FGate LW 23), firstStage = headGates ++
      (opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
        dagB.opsRest planB).reverse (fun _ => 1)).flatten := by
    refine ⟨(preBlocks assignment ++ (List.finRange 23).map (centreBlockAt centreSlots centreTargets) ++
      readBlocks assignment (lateSlots assignment.readoutOrder) ++
      opBlocks (dagB.vLate planB) assignment.source ++ opBlocks (dagB.opsRest planB) assignment.side ++
      outBlocks assignment).flatten, ?_⟩
    simp only [firstStage, stage, blocks, postBlocks, List.flatten_append, List.append_assoc]
  obtain ⟨headGates, hp⟩ := hp
  rw [hp, fseq_append, List.getLast?_append, uncompute_aux_last s hs, Option.some_or]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
