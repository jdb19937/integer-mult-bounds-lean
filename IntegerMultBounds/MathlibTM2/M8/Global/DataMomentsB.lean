module

public import IntegerMultBounds.MathlibTM2.M8.Global.TargetMomentsB
public import IntegerMultBounds.MathlibTM2.M8.Global.LocalMomentsB

/-! The two data paths are charged by their local moments and a rank-484 connector. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

private theorem lifted_splice_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (f g : LMat → Mat 529)
    (A B C E : LMat) (xs ys : List LMat)
    (hx : ((A :: xs) ++ [B]).Pairwise Le) (hy : ((C :: ys) ++ [E]).Pairwise Le)
    (hix : ∀ F ∈ (A :: xs) ++ [B], F * F = F)
    (hiy : ∀ F ∈ (C :: ys) ++ [E], F * F = F)
    (hf : ∀ {a b}, Le a b → Le (f a) (f b))
    (hg : ∀ {a b}, Le a b → Le (g a) (g b))
    (hfi : ∀ a, a * a = a → f a * f a = f a)
    (hgi : ∀ a, a * a = a → g a * g a = g a)
    (hfr : ∀ {a b}, a * a = a → b * b = b → Le a b → (f b - f a).rank = (b - a).rank)
    (hgr : ∀ {a b}, a * a = a → b * b = b → Le a b → (g b - g a).rank = (b - a).rank)
    (hbc : Le (f B) (g C)) :
    chainMoment φ ((f A :: xs.map f) ++ ys.map g ++ [g E]) ≤
      chainMoment φ ((A :: xs) ++ [B]) + stepMoment φ (f B) (g C) +
        chainMoment φ ((C :: ys) ++ [E]) := by
  have hpx : ((f A :: xs.map f) ++ [f B]).Pairwise Le := by
    simpa only [List.map_cons, List.map_append, List.map_nil] using pairwise_map_lift hf hx
  have hpy : ((g C :: ys.map g) ++ [g E]).Pairwise Le := by
    simpa only [List.map_cons, List.map_append, List.map_nil] using pairwise_map_lift hg hy
  have hidx : ∀ F ∈ (f A :: xs.map f) ++ [f B], F * F = F := by
    intro F hF
    have hF' : F ∈ ((A :: xs) ++ [B]).map f := by
      simpa only [List.map_cons, List.map_append, List.map_nil] using hF
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hF'
    exact hfi K (hix K hK)
  have hidy : ∀ F ∈ (g C :: ys.map g) ++ [g E], F * F = F := by
    intro F hF
    have hF' : F ∈ ((C :: ys) ++ [E]).map g := by
      simpa only [List.map_cons, List.map_append, List.map_nil] using hF
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hF'
    exact hgi K (hiy K hK)
  have h := chainMoment_splice_le φ hφ hsub (f A) (f B) (g C) (g E) _ _ hpx hpy hbc hidx hidy
  have hmx := chainMoment_lift φ hfr _ hx hix
  have hmy := chainMoment_lift φ hgr _ hy hiy
  simp only [List.map_cons, List.map_append, List.map_nil] at hmx hmy
  rw [hmx, hmy] at h
  exact h

private theorem padded_fseq_idem (L : List (FGate LW 23))
    (hL : ∀ v ∈ L, v.frame * v.frame = v.frame) (w : LW) (A B : LMat)
    (hA : A * A = A) (hB : B * B = B) :
    ∀ F ∈ (A :: fseq w L) ++ [B], F * F = F := by
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact hA
    · obtain ⟨v, hv, rfl⟩ := fseq_frames hF
      exact hL v hv
  · rw [List.mem_singleton.mp hF]
    exact hB

private theorem reflect_path (A B : LMat) (fs : List LMat) :
    ((A :: fs ++ [B]).map (1 - ·)).reverse =
      (1 - B) :: (fs.map (1 - ·)).reverse ++ [1 - A] := by
  simp only [List.map_cons, List.map_append, List.map_nil, List.reverse_cons,
    List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append]

theorem reflected_source_moment (φ : Nat → ℝ) (n : Nat) :
    chainMoment φ (0 :: fseq (Sum.inl (Reg.x n) : LW) finalStage ++
      [1 - lineFrame (leafTriple n)]) = sourceMoment φ n := by
  rw [show fseq (Sum.inl (Reg.x n) : LW) finalStage = _ from secondStage_reg_trace assignment (.x n)]
  have h := chainMoment_compl φ (lineFrame (leafTriple n) :: fseq (Sum.inl (Reg.x n) : LW) firstStage ++ [1])
  rw [reflect_path, sub_self] at h
  exact h

theorem reflected_target_moment (φ : Nat → ℝ) (n : Nat) :
    chainMoment φ ((1 - hyperFrame (leafTriple n)) :: fseq (Sum.inl (Reg.y n) : LW) finalStage ++ [1]) =
      targetMoment φ n := by
  rw [show fseq (Sum.inl (Reg.y n) : LW) finalStage = _ from secondStage_reg_trace assignment (.y n)]
  have h := chainMoment_compl φ (0 :: fseq (Sum.inl (Reg.y n) : LW) firstStage ++ [hyperFrame (leafTriple n)])
  rw [reflect_path, sub_zero] at h
  exact h

theorem wireMoment_of_not_side (φ : Nat → ℝ) {w : Wire} (h : w ∉ sideWires) :
    wireMoment φ w = chainMoment φ (gInit w :: fseq w allGates) := by
  rw [wireMoment, ite_eq_right h, add_zero]

/-- A data source pays its two actual local paths and one rank-484 connector. -/
theorem wX_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (S T : V) :
    wireMoment φ (wX S T) ≤ sourceMoment φ S + φ 484 + targetMoment φ T := by
  have hx := (firstStage_source_chain S S.2).imp le_of_nested
  have hy := (finalStage_target_chain T T.2).imp le_of_nested
  rw [hyper_V, sub_sub_cancel] at hy
  have hi1 := padded_fseq_idem firstStage (fun v hv => (firstStage_frames v hv).1.idem)
    (.inl (.x S)) (lineOf S) 1 (lineOf_idem S) (Matrix.one_mul 1)
  have hi2 := padded_fseq_idem finalStage (fun v hv => (finalStage_frames v hv).1.idem)
    (.inl (.y T)) (lineOf T) 1 (lineOf_idem T) (Matrix.one_mul 1)
  have h := lifted_splice_le φ hφ hsub (lift1 (lineOf T)) (lift2 (lineOf S)) (lineOf S) 1 (lineOf T) 1
    _ _ hx hy hi1 hi2 (le_lift1 (lineOf_idem T)) (le_lift2 (lineOf_idem S))
    (fun _ h => lift1_idem T h) (fun _ h => lift2_idem S h)
    (fun ha hb h => lift1_rank T ha hb h) (fun ha hb h => lift2_rank S ha hb h)
    (connector_x (lineOf_idem T))
  rw [step_connector_x, lift2_one] at h
  have hm : chainMoment φ (lineOf T :: fseq (.inl (.y T)) finalStage ++ [1]) = targetMoment φ T := by
    simpa only [hyper_V, sub_sub_cancel] using reflected_target_moment φ T
  rw [hm] at h
  rw [wireMoment_of_not_side φ (fun hm => by
    obtain ⟨_, _, _, he⟩ := mem_sideWires.mp hm; simp [wX, wSide] at he), fseq_wX]
  exact h

/-- A data target pays its two actual local paths and one rank-484 connector. -/
theorem wY_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (S T : V) :
    wireMoment φ (wY S T) ≤ targetMoment φ S + φ 484 + sourceMoment φ T := by
  have hx := (firstStage_target_chain S S.2).imp le_of_nested
  have hy := (finalStage_source_chain T T.2).imp le_of_nested
  rw [hyper_V] at hx
  have hi1 := padded_fseq_idem firstStage (fun v hv => (firstStage_frames v hv).1.idem)
    (.inl (.y S)) 0 (1 - lineOf S) (Matrix.zero_mul 0) (compl_idem (lineOf_idem S))
  have hi2 := padded_fseq_idem finalStage (fun v hv => (finalStage_frames v hv).1.idem)
    (.inl (.x T)) 0 (1 - lineOf T) (Matrix.zero_mul 0) (compl_idem (lineOf_idem T))
  have h := lifted_splice_le φ hφ hsub (lift1 (lineOf T)) (lift2 (lineOf S)) 0 (1 - lineOf S) 0 (1 - lineOf T)
    _ _ hx hy hi1 hi2 (le_lift1 (lineOf_idem T)) (le_lift2 (lineOf_idem S))
    (fun _ h => lift1_idem T h) (fun _ h => lift2_idem S h)
    (fun ha hb h => lift1_rank T ha hb h) (fun ha hb h => lift2_rank S ha hb h)
    (connector_y (lineOf_idem S))
  rw [step_connector_y, lift1_zero, lift2_compl] at h
  have hm : chainMoment φ (0 :: fseq (.inl (.x T)) finalStage ++ [1 - lineOf T]) = sourceMoment φ T :=
    reflected_source_moment φ T
  rw [hm] at h
  rw [wireMoment_of_not_side φ (fun hm => by
    obtain ⟨_, _, _, he⟩ := mem_sideWires.mp hm; simp [wY, wSide] at he), fseq_wY]
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
