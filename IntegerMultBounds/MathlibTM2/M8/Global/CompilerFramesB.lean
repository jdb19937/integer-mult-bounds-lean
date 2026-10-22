module

public import IntegerMultBounds.MathlibTM2.M8.Global.ArgumentFramesB
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Facts

/-! The actual design-B compiler has nested auxiliary frame chains,
including varying late-copy frames. All geometric hypotheses are discharged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames

/-- Every auxiliary wire of the actual framed compiler follows nested frames. -/
theorem compiler_aux_nested (s : Nat) :
    List.IsChain Nested (fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten) :=
  compiler_aux_chain
    (fun k hv hk pos => GeometryB.argument_nested k hv hk pos)
    (fun k hv hk => GeometryB.copies_chain k hv hk) s

theorem compiler_aux_pairwise (s : Nat) :
    (fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten).Pairwise Nested := by
  let : IsTrans LMat Nested := ⟨fun _ _ _ h h' => h.trans h'⟩
  exact List.isChain_iff_pairwise.mp (compiler_aux_nested s)

/-- Filtering compiler operations preserves every auxiliary nesting relation. -/
theorem compiler_aux_subchain (ops : List Op) (hops : ops.Sublist dagB.opsB) (s : Nat) :
    (fseq (.inl (.aux s)) (opBlocks ops opFrame).flatten).Pairwise Nested := by
  rw [fseq_opBlocks]
  have h := compiler_aux_pairwise s
  rw [fseq_opBlocks] at h
  exact h.sublist ((hops.filter fun op : Op => decide (s ∈ op.slots)).map opFrame)

theorem opBlocks_side_eq (ops : List Op) (hops : ops.Sublist dagB.sideB) :
    opBlocks ops assignment.side = opBlocks ops opFrame := by
  unfold opBlocks
  apply List.map_congr_left
  intro op ho
  have hm := hops.subset ho
  rw [Dag.sideB, List.mem_filter] at hm
  have hs : op.isSrc = false := by simpa only [Bool.not_eq_true'] using hm.2
  simp only [opFrame, hs, Bool.false_eq_true, ite_false]

theorem side_aux_subchain (ops : List Op) (hops : ops.Sublist dagB.sideB) (s : Nat) :
    (fseq (.inl (.aux s)) (opBlocks ops assignment.side).flatten).Pairwise Nested := by
  rw [opBlocks_side_eq ops hops]
  exact compiler_aux_subchain ops (hops.trans List.filter_sublist) s

/-- The first phase's actual side blocks already satisfy auxiliary nesting. -/
theorem first_side_aux_chain (s : Nat) :
    (fseq (.inl (.aux s)) (opBlocks (dagB.opsFirst planB) assignment.side).flatten).Pairwise Nested :=
  side_aux_subchain _ List.filter_sublist s

/-- The remaining phase's actual side blocks satisfy the same nesting property. -/
theorem rest_side_aux_chain (s : Nat) :
    (fseq (.inl (.aux s)) (opBlocks (dagB.opsRest planB) assignment.side).flatten).Pairwise Nested :=
  side_aux_subchain _ List.filter_sublist s

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
