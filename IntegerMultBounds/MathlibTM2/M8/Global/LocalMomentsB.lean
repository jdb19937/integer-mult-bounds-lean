module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeMomentsB
public import IntegerMultBounds.MathlibTM2.M8.Global.NodeMoments

/-! The actual gauged side roles pay one local path and one whole exterior each. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

variable {M : Type} [AddCommMonoid M]

/-- Complete first-stage side path from the readout gauge to frame one. -/
def localMoment (φ : Nat → M) (s : Nat) : M :=
  chainMoment φ (assignment.sigma s :: fseq (Sum.inl (Reg.aux s) : LW) firstStage ++ [1])

theorem local_pairwise (s : Nat) (hs : s < dagB.compile.next) :
    (assignment.sigma s :: fseq (Sum.inl (Reg.aux s) : LW) firstStage ++ [1]).Pairwise Le := by
  exact pw_app ((firstStage_aux_chain s hs).imp le_of_nested) (List.pairwise_singleton _ _)
    (fun A _ B hB => by rw [List.mem_singleton.mp hB]; exact le_one A)

theorem local_chain_idem (s : Nat) :
    ∀ F ∈ assignment.sigma s :: fseq (Sum.inl (Reg.aux s) : LW) firstStage ++ [1], F * F = F := by
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact sigma_idem s
    · obtain ⟨v, hv, rfl⟩ := fseq_frames hF
      exact (firstStage_frames v hv).1.idem
  · rw [List.mem_singleton.mp hF]
    simp

/-- Reflection includes both gauges, so it preserves the entire side-path moment. -/
theorem reflected_local_path (s : Nat) :
    0 :: fseq (Sum.inl (Reg.aux s) : LW) finalStage ++ [1 - assignment.sigma s] =
      ((assignment.sigma s :: fseq (Sum.inl (Reg.aux s) : LW) firstStage ++ [1]).map (1 - ·)).reverse := by
  rw [finalStage_aux_trace]
  simp only [List.map_cons, List.map_append, List.map_nil, List.reverse_cons,
    List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append, sub_self]

theorem wireMoment_side1 (φ : Nat → M) (k : V) (s : Slot) :
    wireMoment φ (wSide false k s) = localMoment φ s + φ (506 + (assignment.sigma s).rank) := by
  have hs : s.val < dagB.compile.next := by rw [compiler_slots_eq_plain]; exact s.2
  have hl := chainMoment_lift φ (f := lift1 (lineOf k))
    (fun ha hb h => lift1_rank k ha hb h) _ (local_pairwise s hs) (local_chain_idem s)
  rw [wireMoment_side_path, fseq_side1]
  change chainMoment φ (lift1 (lineOf k) (assignment.sigma s) ::
      (fseq (Sum.inl (Reg.aux s) : LW) firstStage).map (lift1 (lineOf k)) ++ [lift1 (lineOf k) 1]) + _ = _
  simpa only [List.map_cons, List.map_append, List.map_nil, localMoment] using
    congrArg (· + φ (506 + (assignment.sigma s).rank)) hl

theorem wireMoment_side2 (φ : Nat → M) (k : V) (s : Slot) :
    wireMoment φ (wSide true k s) = localMoment φ s + φ (506 + (assignment.sigma s).rank) := by
  have hs : s.val < dagB.compile.next := by rw [compiler_slots_eq_plain]; exact s.2
  have hp : (0 :: fseq (Sum.inl (Reg.aux s) : LW) finalStage ++ [1 - assignment.sigma s]).Pairwise Le := by
    rw [reflected_local_path]
    exact pairwise_reflect (local_pairwise s hs)
  have hi : ∀ F ∈ 0 :: fseq (Sum.inl (Reg.aux s) : LW) finalStage ++ [1 - assignment.sigma s], F * F = F := by
    rw [reflected_local_path]
    intro F hF
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hF)
    exact compl_idem (local_chain_idem s K hK)
  have hl := chainMoment_lift φ (f := lift2 (lineOf k))
    (fun ha hb h => lift2_rank k ha hb h) _ hp hi
  have hm : chainMoment φ (0 :: fseq (Sum.inl (Reg.aux s) : LW) finalStage ++
      [1 - assignment.sigma s]) = localMoment φ s := by
    rw [reflected_local_path, chainMoment_compl]
    rfl
  rw [hm] at hl
  rw [wireMoment_side_path, fseq_side2]
  change chainMoment φ (lift2 (lineOf k) 0 ::
      (fseq (Sum.inl (Reg.aux s) : LW) finalStage).map (lift2 (lineOf k)) ++
        [lift2 (lineOf k) (1 - assignment.sigma s)]) + _ = _
  simpa only [List.map_cons, List.map_append, List.map_nil, localMoment] using
    congrArg (· + φ (506 + (assignment.sigma s).rank)) hl

/-- Both orientations have exactly the same priced side cost. -/
theorem wireMoment_side_eq (φ : Nat → M) (b : Bool) (k : V) (s : Slot) :
    wireMoment φ (wSide b k s) = localMoment φ s + φ (506 + (assignment.sigma s).rank) := by
  cases b
  · exact wireMoment_side1 φ k s
  · exact wireMoment_side2 φ k s

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
