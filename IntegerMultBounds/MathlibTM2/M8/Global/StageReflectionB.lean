module

public import IntegerMultBounds.MathlibTM2.M8.Global.TargetTraceB
public import IntegerMultBounds.MathlibTM2.M8.Global.StageBReverse

/-! Every register sees the second-stage frames in reverse complemented order.
A centre block touches a register at most once, so its retained internal order
has the same register trace as its reversal. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem centreBlockAt_reg_short (c : Fin 23) (r : Reg) :
    (fseq (.inl r) (centreBlockAt centreSlots centreTargets c)).length ≤ 1 := by
  cases r with
  | aux s => rw [centreBlockAt_aux_trace]; split_ifs <;> simp
  | x n => rw [fseq_centreBlockAt_x]; simp
  | y t =>
    rw [centreBlockAt_target_trace centreSlots centreTargets c
      (targets_nodup (3 * leafCount + c.val)) t]
    split_ifs <;> simp

/-- Reflection is structural and holds for every frame assignment and register. -/
theorem secondStage_reg_trace (F : FrameAssignment) (r : Reg) :
    fseq (.inl r) (secondStage F) = ((fseq (.inl r) (stage F)).map (1 - ·)).reverse := by
  have hc := fseq_reflect (.inl r)
    ((List.finRange 23).map (centreBlockAt centreSlots centreTargets)) (by
      intro B hB
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hB
      exact centreBlockAt_reg_short c r)
  simp only [List.map_reverse, List.map_map, Function.comp_def] at hc
  simp only [secondStage, stage, blocks, List.flatten_append, fseq_append, fseq_complB,
    fseq_reverse, List.map_append, List.reverse_append, List.map_reverse, hc, List.append_assoc]

theorem nested_complement {A B : LMat} (h : Nested A B) : Nested (1 - B) (1 - A) := by
  have hc := le_compl (le_of_nested h)
  exact ⟨hc.2, hc.1⟩

/-- Complementation reverses every nested-frame chain. -/
theorem pairwise_complement_reverse {fs : List LMat} (h : fs.Pairwise Nested) :
    (fs.map (1 - ·)).reverse.Pairwise Nested := by
  rw [List.pairwise_reverse, List.pairwise_map]
  exact h.imp fun {A B} hAB => nested_complement hAB

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
