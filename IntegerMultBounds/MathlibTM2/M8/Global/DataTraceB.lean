module

public import IntegerMultBounds.MathlibTM2.M8.Global.StageB
public import IntegerMultBounds.MathlibTM2.M8.Global.StageFrames

/-! Structural source-wire traces of the design-B stage. Only source gates
and their uncompute touch a data source; readouts and centre scatters do not. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem fseq_opBlocks_x (n : Nat) (ops : List Op) (frame : Op → LMat) :
    fseq (.inl (.x n)) (opBlocks ops frame).flatten =
      (ops.filter fun op => decide (∃ s, op = .src s n)).map frame := by
  rw [fseq_flatten, opBlocks, fseq_singles]
  simp only [x_mem_opGate]

theorem fseq_opBlocks_y (t : Nat) (ops : List Op) (frame : Op → LMat) :
    fseq (.inl (.y t)) (opBlocks ops frame).flatten = [] := by
  rw [fseq_flatten, opBlocks, fseq_singles]
  simp only [y_not_mem_opGate, decide_false, List.filter_false, List.map_nil]

theorem fseq_sideBlocks_x (n : Nat) (ops : List Op) (frame : Op → LMat)
    (hs : ∀ op ∈ ops, op.isSrc = false) :
    fseq (.inl (.x n)) (opBlocks ops frame).flatten = [] := by
  rw [fseq_opBlocks_x, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op ho h
  obtain ⟨s, rfl⟩ := of_decide_eq_true h
  simpa [Op.isSrc] using hs (.src s n) ho

theorem fseq_readBlocks_x (F : FrameAssignment) (ss : List Nat) (n : Nat) :
    fseq (.inl (.x n)) (readBlocks F ss).flatten = [] := by
  rw [fseq_flatten, readBlocks, List.flatMap_assoc, List.flatMap_eq_nil_iff]
  intro s _
  rw [fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro g hg
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hg
  simp [gL_add, mem_touched_add]

theorem fseq_outBlocks_x (F : FrameAssignment) (n : Nat) :
    fseq (.inl (.x n)) (outBlocks F).flatten = [] := by
  rw [fseq_flatten, outBlocks, List.flatMap_assoc, List.flatMap_eq_nil_iff]
  intro j _
  rw [fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro t _
  simp [gL_add, mem_touched_add]

theorem fseq_centreBlockAt_x (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (c : Fin 23) (n : Nat) :
    fseq (.inl (.x n)) (centreBlockAt slots reads c) = [] := by
  rw [centreBlockAt, fseq_cons]
  simp only [mem_touched_add, Sum.inl.injEq, reduceCtorEq, or_self, ite_false]
  rw [fseq_map, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro t _
  simp [mem_touched_add]

/-- The actual source trace, retaining the plan's source order and repeated frames. -/
theorem stage_source_trace (F : FrameAssignment) (n : Nat) :
    fseq (.inl (.x n)) (stage F) =
      fseq (.inl (.x n)) (opBlocks (dagB.vNow planB) F.source).flatten ++
      fseq (.inl (.x n)) (opBlocks (dagB.vLate planB) F.source).flatten ++
      fseq (.inl (.x n))
        (opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
          dagB.opsRest planB).reverse (fun _ => 1)).flatten := by
  have hfirst := fseq_sideBlocks_x n (dagB.opsFirst planB) F.side
    (fun op ho => by
      have hm := (dagB.mem_opsFirst planB ho).1
      simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hm).2)
  have hrest := fseq_sideBlocks_x n (dagB.opsRest planB) F.side
    (fun op ho => by
      have hm := (dagB.mem_opsRest planB ho).1
      simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hm).2)
  have hc : fseq (.inl (.x n))
      ((List.finRange 23).map (centreBlockAt centreSlots centreTargets)).flatten = [] := by
    rw [fseq_flatten, List.flatMap_map, List.flatMap_eq_nil_iff]
    intro c _
    exact fseq_centreBlockAt_x _ _ c n
  simp only [stage, blocks, preBlocks, postBlocks, List.flatten_append, fseq_append,
    fseq_readBlocks_x, hfirst, hrest, fseq_outBlocks_x, hc, List.nil_append,
    List.append_assoc]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
