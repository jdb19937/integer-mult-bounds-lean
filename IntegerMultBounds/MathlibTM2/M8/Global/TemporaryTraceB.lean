module

public import IntegerMultBounds.MathlibTM2.M8.Global.BlockTraceB
public import IntegerMultBounds.MathlibTM2.M8.Global.StageBReverse

/-! Each centre temporary is touched only in its own centre block. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem readBlocks_temporary_trace (F : FrameAssignment) (ss : List Nat) (c : Fin 23) :
    fseq (.inr c) (readBlocks F ss).flatten = [] := by
  rw [fseq_flatten, readBlocks, List.flatMap_assoc, List.flatMap_eq_nil_iff]
  intro s _
  rw [fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro g _
  simpa only [decide_eq_true_eq] using inr_not_mem_gL g c

theorem opBlocks_temporary_trace (ops : List Op) (frame : Op → LMat) (c : Fin 23) :
    fseq (.inr c) (opBlocks ops frame).flatten = [] := by
  rw [fseq_flatten, opBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op _
  simpa only [decide_eq_true_eq] using inr_not_mem_gL (opGate op) c

theorem outBlocks_temporary_trace (F : FrameAssignment) (c : Fin 23) :
    fseq (.inr c) (outBlocks F).flatten = [] := by
  rw [fseq_flatten, outBlocks, List.flatMap_assoc, List.flatMap_eq_nil_iff]
  intro j _
  rw [fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro t _
  simpa only [decide_eq_true_eq] using
    inr_not_mem_gL (ReversibleFanout.add (.y t) (.aux (dagB.compile.pend (.root j)))) c

theorem preBlocks_temporary_trace (F : FrameAssignment) (c : Fin 23) :
    fseq (.inr c) (preBlocks F).flatten = [] := by
  simp only [preBlocks, List.flatten_append, fseq_append, readBlocks_temporary_trace,
    opBlocks_temporary_trace, List.append_nil]

theorem postBlocks_temporary_trace (F : FrameAssignment) (c : Fin 23) :
    fseq (.inr c) (postBlocks F).flatten = [] := by
  simp only [postBlocks, List.flatten_append, fseq_append, readBlocks_temporary_trace,
    opBlocks_temporary_trace, outBlocks_temporary_trace, List.append_nil]

theorem centreBlockAt_temporary_trace (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (c : Fin 23) :
    fseq (.inr c) (centreBlockAt slots reads c) =
      starFrame c.val :: (reads c).map (fun _ => 0) := by
  rw [centreBlockAt, fseq_cons, fseq_map]
  simp only [mem_touched_add, reduceCtorEq, or_true, true_or, ite_true, decide_true, List.filter_true]

theorem centreBlockAt_other_temporary (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (c c' : Fin 23) (hne : c' ≠ c) :
    fseq (.inr c) (centreBlockAt slots reads c') = [] := by
  have hs : fseq (.inr c)
      ((reads c').map fun t => (⟨ReversibleFanout.add (.inl (.y t)) (.inr c'), 0⟩ : FGate LW 23)) = [] := by
    rw [fseq_map, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro t _
    simp [mem_touched_add, Ne.symm hne]
  rw [centreBlockAt, fseq_cons, hs]
  simp [mem_touched_add, Ne.symm hne]

theorem centres_temporary_trace (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (cs : List (Fin 23)) (hnd : cs.Nodup) (c : Fin 23) (hc : c ∈ cs) :
    fseq (.inr c) (cs.map (centreBlockAt slots reads)).flatten =
      starFrame c.val :: (reads c).map (fun _ => 0) := by
  rw [fseq_flatten, List.flatMap_map, flatMap_one hnd hc]
  · exact centreBlockAt_temporary_trace slots reads c
  · intro c' _ hne
    exact centreBlockAt_other_temporary slots reads c c' hne

/-- The first stage uses each centre temporary at its star frame, then at zero. -/
theorem stage_temporary_trace (F : FrameAssignment) (c : Fin 23) :
    fseq (.inr c) (stage F) = starFrame c.val :: (centreTargets c).map (fun _ => 0) := by
  rw [stage, blocks, List.flatten_append, List.flatten_append, fseq_append, fseq_append,
    preBlocks_temporary_trace, postBlocks_temporary_trace, List.nil_append, List.append_nil]
  exact centres_temporary_trace _ _ _ (List.nodup_finRange 23) c (List.mem_finRange c)

/-- The reflected stage keeps the internal centre-block order and complements frames. -/
theorem secondStage_temporary_trace (F : FrameAssignment) (c : Fin 23) :
    fseq (.inr c) (secondStage F) =
      (1 - starFrame c.val) :: (centreTargets c).map (fun _ => 1) := by
  rw [secondStage, fseq_append, fseq_append, fseq_complB, fseq_complB,
    fseq_reverse, fseq_reverse, preBlocks_temporary_trace, postBlocks_temporary_trace,
    List.reverse_nil, List.map_nil, List.nil_append, List.append_nil,
    fseq_flatten, List.flatMap_map]
  rw [flatMap_one (List.nodup_reverse.mpr (List.nodup_finRange 23))
    (List.mem_reverse.mpr (List.mem_finRange c))]
  · rw [fseq_complB, centreBlockAt_temporary_trace, List.map_cons, List.map_map]
    simp only [Function.comp_def, sub_zero]
  · intro c' _ hne
    rw [fseq_complB, centreBlockAt_other_temporary _ _ c c' hne, List.map_nil]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
