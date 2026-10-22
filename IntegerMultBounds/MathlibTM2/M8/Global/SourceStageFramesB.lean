module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceSlotTraceB
public import IntegerMultBounds.MathlibTM2.M8.Global.TargetStageFramesB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB.Checked
public import IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB.Facts

/-! Complete source chains in the actual forward and reflected design-B stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Every actual source wire climbs from its input line through both keys to one. -/
theorem firstStage_source_chain (n : Nat) (hn : n < leafCount) :
    (lineFrame (leafTriple n) :: fseq (Sum.inl (Reg.x n) : LW) firstStage ++ [1]).Pairwise Nested := by
  have hc := SourceGeometryB.sourceOk_source_chain n (SourceGeometryB.sourceStart n) hn
    (SourceGeometryB.sourceOk_at n hn)
  change (lineFrame (leafTriple n) :: (SourceGeometryB.sourceLabels n).map frameOfLabel ++ [1]).Pairwise Nested at hc
  rw [sourceGeometry_labels_eq n hn, List.map_append] at hc
  have hp : ∀ F ∈ [lineFrame (leafTriple n)], F = lineFrame (leafTriple n) := by simp
  have hq : ∀ F ∈ sourceUncompute n ++ [1], F = (1 : LMat) := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact sourceUncompute_one n F hF
    · exact List.mem_singleton.mp hF
  have hh := lineFrame_idem (leafTriple_isTriple hn)
  have h := pw_pad hc ⟨hh, hh⟩ (by simp [Nested] : Nested (1 : LMat) 1) hp hq
  rw [firstStage_source_label_trace]
  simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using h

/-- Reflection gives the source chain from zero to the complement of its input line. -/
theorem finalStage_source_chain (n : Nat) (hn : n < leafCount) :
    (0 :: fseq (Sum.inl (Reg.x n) : LW) finalStage ++ [1 - lineFrame (leafTriple n)]).Pairwise Nested := by
  have h := pairwise_complement_reverse (firstStage_source_chain n hn)
  have htrace : fseq (Sum.inl (Reg.x n) : LW) finalStage =
      ((fseq (Sum.inl (Reg.x n) : LW) firstStage).map (1 - ·)).reverse :=
    secondStage_reg_trace assignment (.x n)
  rw [htrace]
  have hrev (fs : List LMat) :
      ((lineFrame (leafTriple n) :: fs ++ [1]).map (1 - ·)).reverse =
        0 :: (fs.map (1 - ·)).reverse ++ [1 - lineFrame (leafTriple n)] := by
    simp only [List.map_cons, List.map_append, List.map_nil, List.reverse_cons,
      List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append, sub_self]
  rw [hrev] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
