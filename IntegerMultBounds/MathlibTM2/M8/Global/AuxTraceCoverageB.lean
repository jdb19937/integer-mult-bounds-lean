module

public import IntegerMultBounds.MathlibTM2.M8.Global.AuxBoundaryB

/-! Propagate an arbitrary property from compiler frames and boundaries to the full side trace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Readouts, reordered compiler phases, root reads and uncompute exhaust the side frames. -/
theorem firstStage_aux_property (s : Nat) (P : LMat → Prop)
    (hσ : P (assignment.sigma s))
    (hcompiler : ∀ F ∈ fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten, P F)
    (hcentre : ∀ c : Fin 23, s = centreSlots c → P (starFrame c.val))
    (houtput : ∀ j ∈ outputRoots, s = dagB.compile.pend (.root j) → P (assignment.output j))
    (hone : P 1) : ∀ F ∈ fseq (.inl (.aux s)) firstStage, P F := by
  intro F hF
  simp only [firstStage, stage, blocks, preBlocks, postBlocks, List.flatten_append,
    fseq_append, List.mem_append, or_assoc] at hF
  rcases hF with hR | hA | hB | hM | hR | hC | hD | hO | hU
  · rw [(readBlocks_aux_frame assignment _ s F hR).2]
    exact hσ
  · exact hcompiler F (source_aux_mem_compiler _ now_source_mem s F hA)
  · exact hcompiler F (side_aux_mem_compiler (dagB.opsFirst planB) List.filter_sublist s F hB)
  · obtain ⟨c, _, hs, rfl⟩ := centreBlocks_aux_frame _ _ _ s F hM
    exact hcentre c hs
  · rw [(readBlocks_aux_frame assignment _ s F hR).2]
    exact hσ
  · exact hcompiler F (source_aux_mem_compiler _ late_source_mem s F hC)
  · exact hcompiler F (side_aux_mem_compiler (dagB.opsRest planB) List.filter_sublist s F hD)
  · obtain ⟨j, hj, hs, rfl⟩ := outBlocks_aux_frame assignment s F hO
    exact houtput j hj hs
  · rw [opBlocks_const_frame _ 1 _ F hU]
    exact hone

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
