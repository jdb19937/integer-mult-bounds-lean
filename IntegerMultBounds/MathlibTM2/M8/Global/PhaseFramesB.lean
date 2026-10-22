module

public import IntegerMultBounds.MathlibTM2.M8.Global.CompilerBoundaryB

/-! Splitting the side compiler into phases preserves its trace on each slot.
The phase invariant forbids a second-phase operation before a first-phase
operation on the same slot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames

private theorem filter_split {α : Type*} (p q : α → Bool) (xs : List α)
    (h : xs.Pairwise fun a b => p a = false → p b = true → q b = true → q a = false) :
    ((xs.filter p) ++ xs.filter (fun a => !p a)).filter q = xs.filter q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, Bool.not_true, Bool.false_eq_true,
        ite_true, ite_false, List.cons_append]
      rw [ih ht]
    · have hp : p a = false := Bool.eq_false_iff.mpr hp
      by_cases hq : q a = true
      · have hempty : (xs.filter p).filter q = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          obtain ⟨hb, hpb⟩ := List.mem_filter.mp hb
          have hn : q b ≠ true := fun hqb => by
            have := ha b hb hp hpb hqb
            simp [hq] at this
          exact hn
        have hi := ih ht
        rw [List.filter_append, hempty, List.nil_append] at hi
        simp [hp, hq, List.filter_append, hempty, hi]
      · have hq : q a = false := Bool.eq_false_iff.mpr hq
        simpa [hp, hq, List.filter_append] using ih ht

/-- The two side phases concatenate to precisely the original auxiliary trace. -/
theorem side_phases_trace (s : Nat) :
    fseq (.inl (.aux s))
      ((opBlocks (dagB.opsFirst planB) assignment.side).flatten ++
        (opBlocks (dagB.opsRest planB) assignment.side).flatten) =
      fseq (.inl (.aux s)) (opBlocks dagB.sideB assignment.side).flatten := by
  rw [fseq_append, fseq_opBlocks, fseq_opBlocks, fseq_opBlocks]
  simp only [FrameFlow.framesOf]
  rw [← List.map_append, ← List.filter_append]
  apply congrArg (List.map assignment.side)
  unfold Dag.opsFirst Dag.opsRest
  apply filter_split
  have h := Dag.sideB_pairwise (Dag.phase_sorted dagB_valid phaseHypB)
  exact h.imp fun {a b} hab hpa hpb hqb => by
    have hs : s ∈ b.slots := of_decide_eq_true hqb
    exact decide_eq_false (hab hpa hpb s hs)

/-- Phase splitting preserves nesting even across the phase boundary. -/
theorem side_phases_aux_chain (s : Nat) :
    (fseq (.inl (.aux s))
      ((opBlocks (dagB.opsFirst planB) assignment.side).flatten ++
        (opBlocks (dagB.opsRest planB) assignment.side).flatten)).Pairwise Nested := by
  rw [side_phases_trace]
  exact side_aux_subchain _ (List.Sublist.refl _) s

/-- Source order does not affect auxiliary geometry: a source touches its own
slot only, and always at that slot's start frame. -/
theorem source_aux_frame (ops : List Op) (hsrc : ∀ op ∈ ops, op.isSrc = true)
    (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (opBlocks ops assignment.source).flatten) :
    f = frameOfLabel (AssignmentB.startLabel s) := by
  rw [fseq_opBlocks] at hf
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hf
  obtain ⟨hop, hs⟩ := List.mem_filter.mp hop
  obtain ⟨p, n, rfl, _⟩ := opGate_src (hsrc op hop)
  have he : s = p := by simpa [Op.slots] using hs
  subst p
  rfl

theorem source_aux_chain (ops : List Op) (hsrc : ∀ op ∈ ops, op.isSrc = true)
    (s : Nat) :
    (fseq (.inl (.aux s)) (opBlocks ops assignment.source).flatten).Pairwise Nested := by
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  rw [source_aux_frame ops hsrc s a ha, source_aux_frame ops hsrc s b hb]
  have hi := frameOfLabel_idem _ (AssignmentB.startLabel_valid s)
  exact ⟨hi, hi⟩

/-- Moving sources before side operations preserves the auxiliary frame order. -/
theorem source_side_aux_chain (sources ops : List Op)
    (hsrc : ∀ op ∈ sources, op.isSrc = true) (hops : ops.Sublist dagB.sideB) (s : Nat) :
    (fseq (.inl (.aux s))
      ((opBlocks sources assignment.source).flatten ++
        (opBlocks ops assignment.side).flatten)).Pairwise Nested := by
  rw [fseq_append, List.pairwise_append]
  refine ⟨source_aux_chain sources hsrc s, side_aux_subchain ops hops s, ?_⟩
  intro a ha b hb
  rw [source_aux_frame sources hsrc s a ha]
  apply (List.pairwise_cons.mp (compiler_start_bound s)).1 b
  rw [opBlocks_side_eq ops hops, fseq_opBlocks] at hb
  rw [fseq_opBlocks]
  exact (((hops.trans List.filter_sublist).filter
    fun op : Op => decide (s ∈ op.slots)).map opFrame).subset hb

theorem first_source_side_aux_chain (s : Nat) :
    (fseq (.inl (.aux s))
      ((opBlocks (dagB.vNow planB) assignment.source).flatten ++
        (opBlocks (dagB.opsFirst planB) assignment.side).flatten)).Pairwise Nested :=
  source_side_aux_chain _ _ (fun _op ho => (dagB.mem_vNow planB ho).1) List.filter_sublist s

theorem rest_source_side_aux_chain (s : Nat) :
    (fseq (.inl (.aux s))
      ((opBlocks (dagB.vLate planB) assignment.source).flatten ++
        (opBlocks (dagB.opsRest planB) assignment.side).flatten)).Pairwise Nested :=
  source_side_aux_chain _ _ (fun _op ho => (dagB.mem_vLate planB ho).1) List.filter_sublist s

theorem first_side_aux_empty (s : Nat) (hs : planB.isDef s = true) :
    fseq (.inl (.aux s)) (opBlocks (dagB.opsFirst planB) assignment.side).flatten = [] := by
  rw [fseq_opBlocks, FrameFlow.framesOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op ho
  obtain ⟨ho, hp⟩ := dagB.mem_opsFirst planB ho
  intro hmem
  have := planB_first op ho hp s (of_decide_eq_true hmem)
  simp [hs] at this

theorem late_source_aux_deferred (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (opBlocks (dagB.vLate planB) assignment.source).flatten) :
    planB.isDef s = true := by
  rw [fseq_opBlocks] at hf
  obtain ⟨op, hop, _⟩ := List.mem_map.mp hf
  obtain ⟨hop, hs⟩ := List.mem_filter.mp hop
  obtain ⟨hsrc, hdef⟩ := dagB.mem_vLate planB hop
  obtain ⟨p, n, rfl, _⟩ := opGate_src hsrc
  have he : s = p := by simpa [Op.slots] using hs
  simpa [he, Op.target] using hdef

/-- Both source phases and both side phases retain the compiler's auxiliary order. -/
theorem forward_aux_chain (s : Nat) :
    (fseq (.inl (.aux s))
      (((opBlocks (dagB.vNow planB) assignment.source).flatten ++
        (opBlocks (dagB.opsFirst planB) assignment.side).flatten) ++
       ((opBlocks (dagB.vLate planB) assignment.source).flatten ++
        (opBlocks (dagB.opsRest planB) assignment.side).flatten))).Pairwise Nested := by
  rw [fseq_append]
  apply pw_app (first_source_side_aux_chain s) (rest_source_side_aux_chain s)
  intro a ha b hb
  rw [fseq_append, List.mem_append] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [source_aux_frame _ (fun op ho => (dagB.mem_vNow planB ho).1) s a ha,
      source_aux_frame _ (fun op ho => (dagB.mem_vLate planB ho).1) s b hb]
    have hi := frameOfLabel_idem _ (AssignmentB.startLabel_valid s)
    exact ⟨hi, hi⟩
  · have h := source_side_aux_chain (dagB.vNow planB) (dagB.opsRest planB)
      (fun _op ho => (dagB.mem_vNow planB ho).1) List.filter_sublist s
    rw [fseq_append, List.pairwise_append] at h
    exact h.2.2 a ha b hb
  · rw [first_side_aux_empty s (late_source_aux_deferred s b hb)] at ha
    exact False.elim (List.not_mem_nil ha)
  · have h := side_phases_aux_chain s
    rw [fseq_append, List.pairwise_append] at h
    exact h.2.2 a ha b hb

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
