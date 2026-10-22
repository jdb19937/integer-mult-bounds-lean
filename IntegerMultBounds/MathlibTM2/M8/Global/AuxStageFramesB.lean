module

public import IntegerMultBounds.MathlibTM2.M8.Global.AuxBoundaryB

/-! The complete auxiliary chains of both design-B stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Readouts, both compiler phases, centre/output reads and uncompute form one chain. -/
theorem firstStage_aux_chain (s : Nat) (hs : s < dagB.compile.next) :
    (assignment.sigma s :: fseq (.inl (.aux s)) firstStage).Pairwise Nested := by
  let R₀ := fseq (.inl (.aux s)) (readBlocks assignment nowSlots).flatten
  let R₁ := fseq (.inl (.aux s))
    (readBlocks assignment (lateSlots assignment.readoutOrder)).flatten
  let A := fseq (.inl (.aux s))
    ((opBlocks (dagB.vNow planB) assignment.source).flatten ++
      (opBlocks (dagB.opsFirst planB) assignment.side).flatten)
  let C := fseq (.inl (.aux s))
    ((opBlocks (dagB.vLate planB) assignment.source).flatten ++
      (opBlocks (dagB.opsRest planB) assignment.side).flatten)
  let M := fseq (.inl (.aux s))
    ((List.finRange 23).map (centreBlockAt centreSlots centreTargets)).flatten
  let O := fseq (.inl (.aux s)) (outBlocks assignment).flatten
  let U := fseq (.inl (.aux s))
    (opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
      dagB.opsRest planB).reverse (fun _ => 1)).flatten
  have htrace : fseq (.inl (.aux s)) firstStage = R₀ ++ A ++ M ++ R₁ ++ C ++ O ++ U := by
    simp only [firstStage, stage, blocks, preBlocks, postBlocks, List.flatten_append,
      fseq_append, R₀, R₁, A, C, M, O, U, List.append_assoc]
  have hM (f : LMat) (hf : f ∈ M) :
      ∃ c : Fin 23, s = centreSlots c ∧ f = starFrame c.val := by
    obtain ⟨c, _, hc, he⟩ := centreBlocks_aux_frame _ _ _ s f hf
    exact ⟨c, hc, he⟩
  have hO (f : LMat) (hf : f ∈ O) :
      ∃ j ∈ outputRoots, s = dagB.compile.pend (.root j) ∧ f = assignment.output j :=
    outBlocks_aux_frame assignment s f hf
  have hAR : A ++ R₁ = R₁ ++ A := by
    by_cases hd : planB.isDef s = true
    · have ha : A = [] := first_aux_empty s hd
      simp [ha]
    · have hr : R₁ = [] := late_readBlocks_aux_empty assignment s (Bool.eq_false_iff.mpr hd)
      simp [hr]
  have hMR : M ++ (R₁ ++ C) = (R₁ ++ C) ++ M := by
    by_cases hm : M = []
    · simp [hm]
    · obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hm
      obtain ⟨c, hc, _⟩ := hM f hf
      have hr : R₁ = [] := by
        dsimp only [R₁]
        rw [hc]
        exact late_readBlocks_aux_empty assignment _ (centre_not_deferred c)
      have hC : C = [] := by
        dsimp only [C]
        rw [hc]
        exact centre_rest_aux_empty c
      simp [hr, hC]
  have horder : R₀ ++ A ++ M ++ R₁ ++ C ++ O ++ U =
      (R₀ ++ R₁) ++ (A ++ C) ++ M ++ O ++ U := calc
    _ = R₀ ++ A ++ (M ++ (R₁ ++ C)) ++ O ++ U := by simp only [List.append_assoc]
    _ = R₀ ++ A ++ ((R₁ ++ C) ++ M) ++ O ++ U := by rw [hMR]
    _ = R₀ ++ (A ++ R₁) ++ C ++ M ++ O ++ U := by simp only [List.append_assoc]
    _ = R₀ ++ (R₁ ++ A) ++ C ++ M ++ O ++ U := by rw [hAR]
    _ = _ := by simp only [List.append_assoc]
  have hcompiler (f : LMat) (hf : f ∈ A ++ C) :
      f ∈ fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten := by
    rcases List.mem_append.mp hf with hf | hf
    · exact source_side_aux_mem_compiler (dagB.vNow planB) (dagB.opsFirst planB)
        now_source_mem List.filter_sublist s f hf
    · exact source_side_aux_mem_compiler (dagB.vLate planB) (dagB.opsRest planB)
        late_source_mem List.filter_sublist s f hf
  have hread (f : LMat) (hf : f ∈ assignment.sigma s :: (R₀ ++ R₁)) :
      f = assignment.sigma s := by
    rcases List.mem_cons.mp hf with hf | hf
    · exact hf
    · rcases List.mem_append.mp hf with hf | hf
      · exact (readBlocks_aux_frame assignment _ s f hf).2
      · exact (readBlocks_aux_frame assignment _ s f hf).2
  have hR : (assignment.sigma s :: (R₀ ++ R₁)).Pairwise Nested :=
    pw_const ⟨sigma_idem s, sigma_idem s⟩ hread
  have hF : (A ++ C).Pairwise Nested := by
    have h := forward_aux_chain s
    rw [fseq_append] at h
    exact h
  have hMM : M.Pairwise Nested := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := hM a ha
    obtain ⟨c', hc', rfl⟩ := hM b hb
    have he := dagB.root_slot_inj dagB_valid (centre_root_lt c) (centre_root_lt c')
      (hc.symm.trans hc')
    have he : c = c' := Fin.ext (by omega)
    subst c'
    exact ⟨starFrame_idem c.isLt, starFrame_idem c.isLt⟩
  have hOO : O.Pairwise Nested := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    obtain ⟨j, hj, hs', rfl⟩ := hO a ha
    obtain ⟨j', hj', hs'', rfl⟩ := hO b hb
    have he := dagB.root_slot_inj dagB_valid (out_root_lt (output_root_lt hj))
      (out_root_lt (output_root_lt hj')) (hs'.symm.trans hs'')
    subst j'
    exact ⟨output_idem j, output_idem j⟩
  have hRF : ∀ a ∈ assignment.sigma s :: (R₀ ++ R₁), ∀ b ∈ A ++ C, Nested a b := by
    intro a ha b hb
    rw [hread a ha]
    exact (List.pairwise_cons.mp (compiler_readout_bound s hs)).1 b (hcompiler b hb)
  have hRM : ∀ a ∈ assignment.sigma s :: (R₀ ++ R₁), ∀ b ∈ M, Nested a b := by
    intro a ha b hb
    rw [hread a ha]
    obtain ⟨c, hc, rfl⟩ := hM b hb
    rw [hc]
    exact sigma_centre_bound c
  have hRO : ∀ a ∈ assignment.sigma s :: (R₀ ++ R₁), ∀ b ∈ O, Nested a b := by
    intro a ha b hb
    rw [hread a ha]
    obtain ⟨j, hj, hc, rfl⟩ := hO b hb
    rw [hc]
    exact sigma_output_bound j (output_root_lt hj)
  have hFM : ∀ a ∈ A ++ C, ∀ b ∈ M, Nested a b := by
    intro a ha b hb
    have hm := hcompiler a ha
    obtain ⟨c, hc, rfl⟩ := hM b hb
    rw [hc] at hm
    exact compiler_centre_boundary c a hm
  have hFO : ∀ a ∈ A ++ C, ∀ b ∈ O, Nested a b := by
    intro a ha b hb
    have hm := hcompiler a ha
    obtain ⟨j, hj, hc, rfl⟩ := hO b hb
    rw [hc] at hm
    exact compiler_output_boundary j (output_root_lt hj) a hm
  have hMO : ∀ a ∈ M, ∀ b ∈ O, Nested a b := by
    intro a ha b hb
    obtain ⟨c, hc, _⟩ := hM a ha
    obtain ⟨j, hj, hc', _⟩ := hO b hb
    have he := dagB.root_slot_inj dagB_valid (centre_root_lt c)
      (out_root_lt (output_root_lt hj)) (hc.symm.trans hc')
    have hj := output_root_lt hj
    omega
  have hRFM := pw_app (pw_app hR hF hRF) hMM (by
    intro a ha b hb
    exact (List.mem_append.mp ha).elim (fun ha => hRM a ha b hb) (fun ha => hFM a ha b hb))
  have hRFMO := pw_app hRFM hOO (by
    intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · exact (List.mem_append.mp ha).elim (fun ha => hRO a ha b hb) (fun ha => hFO a ha b hb)
    · exact hMO a ha b hb)
  have hU (f : LMat) (hf : f ∈ U) : f = 1 := opBlocks_const_frame _ 1 _ f hf
  have hone (f : LMat) : Nested f 1 := ⟨by simp, by simp⟩
  have hall := pw_app hRFMO (pw_const (hone 1) hU) (by
    intro a _ b hb
    rw [hU b hb]
    exact hone a)
  rw [htrace, horder]
  simpa only [List.cons_append, List.append_assoc] using hall

/-- The second stage sees each auxiliary trace reversed and complemented. -/
theorem finalStage_aux_trace (s : Nat) :
    fseq (.inl (.aux s)) finalStage =
      ((fseq (.inl (.aux s)) firstStage).map (1 - ·)).reverse := by
  have hc := fseq_reflect (.inl (.aux s))
    ((List.finRange 23).map (centreBlockAt centreSlots centreTargets)) (by
      intro B hB
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hB
      rw [centreBlockAt_aux_trace]
      split_ifs <;> simp)
  simp only [List.map_reverse, List.map_map, Function.comp_def] at hc
  simp only [finalStage, secondStage, firstStage, stage, blocks, List.flatten_append,
    fseq_append, fseq_complB, fseq_reverse, List.map_append, List.reverse_append,
    List.map_reverse, hc, List.append_assoc]

private theorem nested_complement {A B : LMat} (h : Nested A B) :
    Nested (1 - B) (1 - A) := by
  have hc := le_compl (le_of_nested h)
  exact ⟨hc.2, hc.1⟩

/-- The complete reversed auxiliary chain ends at the complement of its readout frame. -/
theorem finalStage_aux_chain (s : Nat) (hs : s < dagB.compile.next) :
    (fseq (.inl (.aux s)) finalStage ++ [1 - assignment.sigma s]).Pairwise Nested := by
  have hr : (assignment.sigma s :: fseq (.inl (.aux s)) firstStage).reverse.Pairwise
      (fun A B => Nested B A) := List.pairwise_reverse.mpr (firstStage_aux_chain s hs)
  have hc := List.pairwise_map.mpr (hr.imp fun {A B} h => nested_complement h)
  simpa only [List.reverse_cons, List.map_append, List.map_singleton, List.map_reverse,
    finalStage_aux_trace] using hc

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
