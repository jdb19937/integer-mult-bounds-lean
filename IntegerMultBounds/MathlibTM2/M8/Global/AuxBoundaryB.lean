module

public import IntegerMultBounds.MathlibTM2.M8.Global.BlockTraceB
public import IntegerMultBounds.MathlibTM2.M8.Global.PhaseFramesB
public import IntegerMultBounds.MathlibTM2.M8.Global.RootBoundaryB

/-! Boundary and membership facts for assembling complete auxiliary stage chains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem root_frame_mem (j : Nat) (hj : j < rootCount) :
    frameOfLabel (rootLabel j) ∈
      fseq (.inl (.aux (dagB.compile.pend (.root j)))) (opBlocks dagB.opsB opFrame).flatten := by
  rw [fseq_opBlocks, Dag.opsB]
  apply List.mem_of_getLast?
  rw [← FrameFlow.last_getLast]
  exact root_frame j hj

theorem sigma_root_bound (j : Nat) (hj : j < rootCount) :
    Nested (assignment.sigma (dagB.compile.pend (.root j))) (frameOfLabel (rootLabel j)) :=
  (List.pairwise_cons.mp (compiler_readout_bound _ (dagB.root_slot_lt dagB_valid hj))).1
    _ (root_frame_mem j hj)

theorem sigma_output_bound (j : Nat) (hj : j < 3 * leafCount) :
    Nested (assignment.sigma (dagB.compile.pend (.root j))) (assignment.output j) := by
  have hr : j < rootCount := out_root_lt hj
  exact (sigma_root_bound j hr).trans (by
    simpa only [frameOfLabel, rootLabel, assignment,
      ite_eq_left (show j / 3 < leafCount by omega)] using
      GeometryB.rootOk_output j hj _ (GeometryB.rootOk_at j hr))

theorem sigma_centre_bound (c : Fin 23) :
    Nested (assignment.sigma (centreSlots c)) (starFrame c.val) :=
  (sigma_root_bound _ (centre_root_lt c)).trans
    (GeometryB.rootOk_centre c.val c.isLt _ (GeometryB.rootOk_at _ (centre_root_lt c)))

theorem now_source_mem (op : Op) (ho : op ∈ dagB.vNow planB) :
    op ∈ dagB.opsB ∧ op.isSrc = true := by
  simp only [Dag.vNow, keyedOps, List.mem_mergeSort, List.mem_filter, Dag.srcB] at ho
  exact ho.1

theorem late_source_mem (op : Op) (ho : op ∈ dagB.vLate planB) :
    op ∈ dagB.opsB ∧ op.isSrc = true := by
  simp only [Dag.vLate, keyedOps, List.mem_mergeSort, List.mem_filter, Dag.srcB] at ho
  exact ho.1

theorem source_aux_mem_compiler (ops : List Op)
    (hops : ∀ op ∈ ops, op ∈ dagB.opsB ∧ op.isSrc = true) (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (opBlocks ops assignment.source).flatten) :
    f ∈ fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten := by
  rw [fseq_opBlocks] at hf ⊢
  obtain ⟨op, hop, he⟩ := List.mem_map.mp hf
  obtain ⟨hop, hs⟩ := List.mem_filter.mp hop
  obtain ⟨hm, hsrc⟩ := hops op hop
  refine List.mem_map.mpr ⟨op, List.mem_filter.mpr ⟨hm, hs⟩, ?_⟩
  simpa only [opFrame, hsrc, ite_true] using he

theorem side_aux_mem_compiler (ops : List Op) (hops : ops.Sublist dagB.sideB)
    (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (opBlocks ops assignment.side).flatten) :
    f ∈ fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten := by
  rw [opBlocks_side_eq ops hops, fseq_opBlocks] at hf
  rw [fseq_opBlocks]
  exact (((hops.trans List.filter_sublist).filter
    fun op : Op => decide (s ∈ op.slots)).map opFrame).subset hf

theorem source_side_aux_mem_compiler (sources ops : List Op)
    (hsrc : ∀ op ∈ sources, op ∈ dagB.opsB ∧ op.isSrc = true)
    (hops : ops.Sublist dagB.sideB) (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s))
      ((opBlocks sources assignment.source).flatten ++ (opBlocks ops assignment.side).flatten)) :
    f ∈ fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten := by
  rw [fseq_append, List.mem_append] at hf
  exact hf.elim (source_aux_mem_compiler sources hsrc s f)
    (side_aux_mem_compiler ops hops s f)

theorem first_aux_empty (s : Nat) (hs : planB.isDef s = true) :
    fseq (.inl (.aux s))
      ((opBlocks (dagB.vNow planB) assignment.source).flatten ++
        (opBlocks (dagB.opsFirst planB) assignment.side).flatten) = [] := by
  rw [fseq_append, first_side_aux_empty s hs, List.append_nil,
    fseq_opBlocks, FrameFlow.framesOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op ho hmem
  obtain ⟨hsrc, hdef⟩ := dagB.mem_vNow planB ho
  obtain ⟨p, n, rfl, _⟩ := opGate_src hsrc
  have he : s = p := by simpa [Op.slots] using of_decide_eq_true hmem
  subst p
  simp only [Op.target] at hdef
  simp [hs] at hdef

theorem centre_not_deferred (c : Fin 23) : planB.isDef (centreSlots c) = false :=
  planB_cen _ (centre_root_lt c) (by simp [planB, cenB])

theorem late_readBlocks_aux_empty (F : FrameAssignment) (s : Nat)
    (hs : planB.isDef s = false) :
    fseq (.inl (.aux s)) (readBlocks F (lateSlots F.readoutOrder)).flatten = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro f hf
  have hm := (readBlocks_aux_frame F _ s f hf).1
  simp only [lateSlots, keyed, List.mem_mergeSort, List.mem_filter] at hm
  simp [hs] at hm

theorem centre_rest_aux_empty (c : Fin 23) :
    fseq (.inl (.aux (centreSlots c)))
      ((opBlocks (dagB.vLate planB) assignment.source).flatten ++
        (opBlocks (dagB.opsRest planB) assignment.side).flatten) = [] := by
  rw [fseq_append, List.append_eq_nil_iff]
  constructor
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro f hf
    have h := late_source_aux_deferred _ f hf
    simp [centre_not_deferred] at h
  · rw [fseq_opBlocks, FrameFlow.framesOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro op ho hmem
    obtain ⟨ho, hp⟩ := dagB.mem_opsRest planB ho
    exact planB_rest op ho hp _ (centre_root_lt c) (by simp [planB, cenB])
      (of_decide_eq_true hmem)

theorem output_root_lt {j : Nat} (hj : j ∈ outputRoots) : j < 3 * leafCount := by
  obtain ⟨_, hc⟩ := List.mem_filter.mp hj
  have hc : (3 * leafCount).ble j = false := by
    simpa only [planB, cenB, Bool.not_eq_true'] using hc
  apply Nat.lt_of_not_ge
  intro h
  have he := Nat.ble_eq.mpr h
  rw [hc] at he
  cases he

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
