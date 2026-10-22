module

public import IntegerMultBounds.MathlibTM2.M8.Global.TargetLabelTraceB
public import IntegerMultBounds.MathlibTM2.M8.Global.StageReflectionB
public import IntegerMultBounds.MathlibTM2.M8.Global.AuxBoundaryB
public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.Checked
public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.Facts

/-! Complete first-stage target chains, retaining every repeated frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- A chain may repeat either endpoint any number of times. -/
theorem pw_pad {α : Type*} {R : α → α → Prop} {a b : α} {xs p q : List α}
    (h : (a :: xs ++ [b]).Pairwise R) (haa : R a a) (hbb : R b b)
    (hp : ∀ x ∈ p, x = a) (hq : ∀ x ∈ q, x = b) :
    (p ++ xs ++ q).Pairwise R := by
  obtain ⟨ha, htail⟩ := List.pairwise_cons.mp h
  obtain ⟨hx, _, hb⟩ := List.pairwise_append.mp htail
  have hpx : (p ++ xs).Pairwise R := pw_app (pw_const haa hp) hx (by
    intro x hx y hy
    rw [hp x hx]
    exact ha y (List.mem_append_left _ hy))
  apply pw_app hpx (pw_const hbb hq)
  intro x hx y hy
  rcases List.mem_append.mp hx with hx | hx
  · rw [hp x hx, hq y hy]
    exact ha b (by simp)
  · rw [hq y hy]
    exact hb x hx b (by simp)

theorem target_output_frame (t j : Nat) (ht : t < leafCount)
    (hj : j ∈ outputRoots) (hm : t ∈ targets j) :
    assignment.output j = hyperFrame (leafTriple t) := by
  have hj := output_root_lt hj
  have he : t = j / 3 := by simpa only [targets, ite_eq_left hj, List.mem_singleton] using hm
  simp [assignment, ← he, ht]

/-- The actual target trace lies between zero and its output hyperplane. -/
theorem firstStage_target_chain (t : Nat) (ht : t < leafCount) :
    (0 :: fseq (.inl (.y t)) firstStage ++ [hyperFrame (leafTriple t)]).Pairwise Nested := by
  rw [firstStage_target_label_trace t ht]
  have hc := TargetGeometryB.targetOk_readout_chain t (TargetGeometryB.endpoint t) ht
    (TargetGeometryB.targetOk_at t ht)
  change (0 :: (TargetGeometryB.readoutLabels t).map frameOfLabel ++
    [hyperFrame (leafTriple t)]).Pairwise Nested at hc
  have hp : ∀ F ∈ (0 :: targetZeroPrefix t), F = (0 : LMat) := by
    intro F hF
    rcases List.mem_cons.mp hF with hF | hF
    · exact hF
    · exact of_decide_eq_true (List.all_eq_true.mp (targetZeroPrefix_zero t) F hF)
  have hq : ∀ F ∈ ((outputRoots.filter fun j => decide (t ∈ targets j)).map assignment.output ++
      [hyperFrame (leafTriple t)]), F = hyperFrame (leafTriple t) := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hF
      obtain ⟨hj, hm⟩ := List.mem_filter.mp hj
      exact target_output_frame t j ht hj (of_decide_eq_true hm)
    · exact List.mem_singleton.mp hF
  have hh := hyperFrame_idem (leafTriple_isTriple ht)
  simpa only [List.cons_append, List.append_assoc] using
    pw_pad hc (by simp [Nested] : Nested (0 : LMat) 0) ⟨hh, hh⟩ hp hq

/-- The reflected stage has the reversed complemented target chain. -/
theorem finalStage_target_chain (t : Nat) (ht : t < leafCount) :
    ((1 - hyperFrame (leafTriple t)) :: fseq (Sum.inl (Reg.y t) : LW) finalStage ++ [1]).Pairwise Nested := by
  have h := pairwise_complement_reverse (firstStage_target_chain t ht)
  have htrace : fseq (Sum.inl (Reg.y t) : LW) finalStage =
      ((fseq (.inl (.y t)) firstStage).map (1 - ·)).reverse :=
    secondStage_reg_trace assignment (.y t)
  rw [htrace]
  have hrev (fs : List LMat) :
      ((0 :: fs ++ [hyperFrame (leafTriple t)]).map (1 - ·)).reverse =
        (1 - hyperFrame (leafTriple t)) :: (fs.map (1 - ·)).reverse ++ [1] := by
    simp only [List.map_cons, List.map_append, List.map_nil, List.reverse_cons,
      List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append, sub_zero]
  rw [hrev] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
