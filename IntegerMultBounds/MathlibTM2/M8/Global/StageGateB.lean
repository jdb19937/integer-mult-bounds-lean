module

public import IntegerMultBounds.MathlibTM2.M8.Global.SideExitB
public import IntegerMultBounds.MathlibTM2.M8.Global.CompilerBoundaryB
public import IntegerMultBounds.MathlibTM2.M8.Local.WordOrderB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceListB

/-! Gate ranges and XOR legality of the concrete design-B stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The two compilers allocate the same role count, although their operations differ. -/
theorem compiler_slots_eq_plain : dagB.compile.next = dag.compile.next := by
  rw [compiler_slot_count, slot_count]
  rfl

/-- A local gate is an XOR on distinct in-range wires. -/
def GateGood (g : Circuit.Gate LW (ZMod 2)) : Prop :=
  (∀ w ∈ FramedCircuit.touched g, InR w) ∧
    ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src

theorem add_gate_good (dst src : LW) (hne : dst ≠ src) (hd : InR dst) (hs : InR src) :
    GateGood (ReversibleFanout.add dst src) := by
  refine ⟨?_, dst, src, hne, rfl⟩
  intro w hw
  rcases (mem_touched_add dst src w).mp hw with rfl | rfl
  · exact hd
  · exact hs

theorem op_gate_good (op : Op) (hd : op.Distinct) (hs : op.SlotsLt dag.compile.next)
    (hn : ∀ s n, op = .src s n → n < leafCount) : GateGood (gL (opGate op)) := by
  cases op with
  | src s n =>
    rw [opGate, gL_add]
    exact add_gate_good _ _ (by simp) hs (hn s n rfl)
  | add p o n =>
    rw [opGate, gL_add]
    exact add_gate_good _ _ (by simpa only [Sum.inl.injEq, Reg.aux.injEq, Op.Distinct, ne_eq] using hd) hs.1 hs.2
  | copy p f n =>
    rw [opGate, gL_add]
    exact add_gate_good _ _ (by simpa only [Sum.inl.injEq, Reg.aux.injEq, Op.Distinct, ne_eq, eq_comm] using hd) hs.2 hs.1

theorem compiler_gate_good (op : Op) (ho : op ∈ dagB.opsB) : GateGood (gL (opGate op)) := by
  have hd : op.Distinct := (dagB.opsB_ok dagB_valid op ho).1
  have hs : op.SlotsLt dag.compile.next := by
    rw [← compiler_slots_eq_plain]
    exact (dagB.opsB_ok dagB_valid op ho).2
  apply op_gate_good op hd hs
  intro s n he
  subst op
  exact dagB.srcB_node_lt dagB_valid (.src s n) (List.mem_filter.mpr ⟨ho, rfl⟩)

theorem opBlocks_gate_good (ops : List Op) (frame : Op → LMat)
    (hops : ∀ op ∈ ops, op ∈ dagB.opsB) :
    ∀ v ∈ (opBlocks ops frame).flatten, GateGood v.gate := by
  intro v hv
  have hg : v.gate ∈ gatesOf (opBlocks ops frame).flatten := List.mem_map_of_mem hv
  rw [gatesOf_flatten, opBlocks_gates] at hg
  obtain ⟨g, hg, he⟩ := List.mem_map.mp hg
  obtain ⟨op, ho, rfl⟩ := List.mem_map.mp hg
  rw [← he]
  exact compiler_gate_good op (hops op ho)

theorem readBlocks_gate_good (F : FrameAssignment) (ss : List Nat)
    (hs : ∀ s ∈ ss, s < dagB.compile.next) :
    ∀ v ∈ (readBlocks F ss).flatten, GateGood v.gate := by
  intro v hv
  have hg : v.gate ∈ gatesOf (readBlocks F ss).flatten := List.mem_map_of_mem hv
  rw [gatesOf_flatten, readBlocks_gates] at hg
  obtain ⟨g, hg, he⟩ := List.mem_map.mp hg
  obtain ⟨s, hss, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [← he, gL_add]
  apply add_gate_good _ _ (by simp)
  · exact List.mem_range.mp (List.mem_filter.mp ht).1
  · change s < dag.compile.next
    rw [← compiler_slots_eq_plain]
    exact hs s hss

theorem outBlocks_gate_good (F : FrameAssignment) :
    ∀ v ∈ (outBlocks F).flatten, GateGood v.gate := by
  intro v hv
  have hg : v.gate ∈ gatesOf (outBlocks F).flatten := List.mem_map_of_mem hv
  rw [gatesOf_flatten, outBlocks_gates] at hg
  obtain ⟨g, hg, he⟩ := List.mem_map.mp hg
  unfold Dag.outReads Dag.rootReadsAt at hg
  obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [← he, gL_add]
  apply add_gate_good (.inl (.y t)) (.inl (.aux (dagB.compile.pend (.root j)))) (by simp)
  · exact targets_lt ht
  change dagB.compile.pend (.root j) < dag.compile.next
  rw [← compiler_slots_eq_plain]
  exact dagB.root_slot_lt dagB_valid (List.mem_range.mp (List.mem_filter.mp hj).1)

theorem centreBlock_gate_good (c : Fin 23) :
    ∀ v ∈ centreBlockAt centreSlots centreTargets c, GateGood v.gate := by
  intro v hv
  rw [centreBlockAt, List.mem_cons] at hv
  rcases hv with rfl | hv
  · apply add_gate_good (.inr c) (.inl (.aux (centreSlots c))) (by simp)
    · trivial
    change centreSlots c < dag.compile.next
    rw [← compiler_slots_eq_plain]
    exact dagB.root_slot_lt dagB_valid (centre_root_lt c)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact add_gate_good (.inl (.y t)) (.inr c) (by simp) (targets_lt ht) trivial

/-- Every gate of a stage is legal, independently of its frame assignment. -/
theorem stage_gate_good (F : FrameAssignment) :
    ∀ v ∈ stage F, GateGood v.gate := by
  have hops (op : Op) := (dagB.orderedOps_perm planB).mem_iff (a := op)
  have hnow : ∀ op ∈ dagB.vNow planB, op ∈ dagB.opsB := by
    intro op ho
    exact (hops op).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ho)))
  have hlate : ∀ op ∈ dagB.vLate planB, op ∈ dagB.opsB := by
    intro op ho
    exact (hops op).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ho)))
  have hfirst : ∀ op ∈ dagB.opsFirst planB, op ∈ dagB.opsB := by
    intro op ho
    exact (hops op).mp (List.mem_append_left _ (List.mem_append_right _ ho))
  have hrest : ∀ op ∈ dagB.opsRest planB, op ∈ dagB.opsB := by
    intro op ho
    exact (hops op).mp (List.mem_append_right _ ho)
  have huncompute : ∀ op ∈ (dagB.vNow planB ++ dagB.vLate planB ++
      dagB.opsFirst planB ++ dagB.opsRest planB).reverse, op ∈ dagB.opsB := by
    intro op ho
    exact (hops op).mp (List.mem_reverse.mp ho)
  have hn : ∀ s ∈ nowSlots, s < dagB.compile.next := by
    intro s hs
    exact List.mem_range.mp (List.mem_filter.mp hs).1
  have hl : ∀ s ∈ lateSlots F.readoutOrder, s < dagB.compile.next := by
    intro s hs
    unfold lateSlots keyed at hs
    exact List.mem_range.mp (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp hs)).1
  intro v hv
  simp only [stage, blocks, preBlocks, postBlocks, List.flatten_append,
    List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · rcases hv with (hv | hv) | hv
    · exact readBlocks_gate_good F nowSlots hn v hv
    · exact opBlocks_gate_good _ _ hnow v hv
    · exact opBlocks_gate_good _ _ hfirst v hv
  · obtain ⟨B, hB, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hB
    exact centreBlock_gate_good c v hv
  · rcases hv with (((hv | hv) | hv) | hv) | hv
    · exact readBlocks_gate_good F _ hl v hv
    · exact opBlocks_gate_good _ _ hlate v hv
    · exact opBlocks_gate_good _ _ hrest v hv
    · exact outBlocks_gate_good F v hv
    · exact opBlocks_gate_good _ _ huncompute v hv

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
