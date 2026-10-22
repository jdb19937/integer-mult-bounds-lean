module

public import IntegerMultBounds.MathlibTM2.M8.Global.DataTraceB

/-! Auxiliary traces of the boundary blocks, independently of their frames. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem readBlocks_aux_frame (F : FrameAssignment) (ss : List Nat) (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (readBlocks F ss).flatten) :
    s ∈ ss ∧ f = F.sigma s := by
  rw [fseq_flatten, readBlocks, List.flatMap_assoc, List.mem_flatMap] at hf
  obtain ⟨p, hp, hf⟩ := hf
  rw [fseq_singles, mem_map_filter] at hf
  obtain ⟨g, hg, hw, rfl⟩ := hf
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hg
  have he : s = p := by simpa [gL_add, mem_touched_add] using hw
  subst p
  exact ⟨hp, rfl⟩

theorem outBlocks_aux_frame (F : FrameAssignment) (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (outBlocks F).flatten) :
    ∃ j ∈ outputRoots, s = dagB.compile.pend (.root j) ∧ f = F.output j := by
  rw [fseq_flatten, outBlocks, List.flatMap_assoc, List.mem_flatMap] at hf
  obtain ⟨j, hj, hf⟩ := hf
  rw [fseq_singles, mem_map_filter] at hf
  obtain ⟨t, _, hw, rfl⟩ := hf
  have he : s = dagB.compile.pend (.root j) := by
    simpa [gL_add, mem_touched_add] using hw
  exact ⟨j, hj, he, rfl⟩

theorem centreBlockAt_aux_trace (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (c : Fin 23) (s : Nat) :
    fseq (.inl (.aux s)) (centreBlockAt slots reads c) =
      if s = slots c then [starFrame c.val] else [] := by
  have hscatter : fseq (.inl (.aux s))
      ((reads c).map fun t => (⟨ReversibleFanout.add (.inl (.y t)) (.inr c), 0⟩ : FGate LW 23)) = [] := by
    rw [fseq_map, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro t _
    simp [mem_touched_add]
  rw [centreBlockAt, fseq_cons, hscatter]
  simp [mem_touched_add]

theorem centreBlocks_aux_frame (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (cs : List (Fin 23)) (s : Nat) (f : LMat)
    (hf : f ∈ fseq (.inl (.aux s)) (cs.map (centreBlockAt slots reads)).flatten) :
    ∃ c ∈ cs, s = slots c ∧ f = starFrame c.val := by
  rw [fseq_flatten, List.flatMap_map, List.mem_flatMap] at hf
  obtain ⟨c, hc, hf⟩ := hf
  rw [centreBlockAt_aux_trace] at hf
  split_ifs at hf with hs
  · exact ⟨c, hc, hs, List.mem_singleton.mp hf⟩
  · cases hf

theorem opBlocks_const_frame (ops : List Op) (F : LMat) (w : LW) (f : LMat)
    (hf : f ∈ fseq w (opBlocks ops (fun _ => F)).flatten) : f = F := by
  rw [fseq_flatten, opBlocks, fseq_singles, List.mem_map] at hf
  obtain ⟨_, _, he⟩ := hf
  exact he.symm

theorem fseq_reverse (w : LW) (gs : List (FGate LW 23)) :
    fseq w gs.reverse = (fseq w gs).reverse := by
  simp only [fseq, List.filter_reverse, List.map_reverse]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
