module

public import IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookupFacts
public import IntegerMultBounds.MathlibTM2.M8.Global.ChainRefinement

/-! Existing path checks certify cost bounds even with repeated and skipped frames. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup
noncomputable section
open IntegerMultBounds Matrix

/-- A checked path is covered by its reference chain, unless it is constant and costs zero. -/
theorem pathCheck_subset_or_constant (size : Nat) (chain : List Signed.Frame) :
    ∀ frames, pathCheck size chain frames = true →
      (∀ f ∈ frames, f ∈ chain) ∨ ∃ a, ∀ f ∈ frames, f = a
  | [], _ => Or.inl (by simp)
  | [a], _ => Or.inr ⟨a, by simp⟩
  | a :: b :: frames, h => by
    change (a.validCheck size && (edgeCheck a b chain && pathCheck size chain (b :: frames))) = true at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨_, he, ht⟩ := h
    have ih := pathCheck_subset_or_constant size chain (b :: frames) ht
    rcases Bool.or_eq_true_iff.mp he with he | he
    · have he : a = b := of_decide_eq_true he
      cases he
      rcases ih with hm | ⟨c, hc⟩
      · exact Or.inl (fun f hf => by
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hm _ (List.mem_cons_self)
          · exact hm f hf)
      · exact Or.inr ⟨c, fun f hf => by
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hc _ (List.mem_cons_self)
          · exact hc f hf⟩
    · have hs := (sublistCheck_sound [a, b] chain he).subset
      have ha : a ∈ chain := hs (by simp)
      have hb : b ∈ chain := hs (by simp)
      apply Or.inl
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ha
      · rcases ih with hm | ⟨c, hc⟩
        · exact hm f hf
        · rw [hc f hf, ← hc b (List.mem_cons_self)]
          exact hb

/-- A path check prices the actual projector path by the known chain's move moment. -/
theorem pathCheck_moment_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b)
    (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (chain : List Signed.Frame)
    (hc : Signed.chainCheck bank size chain = true) (frames : List Signed.Frame)
    (hp : pathCheck size chain frames = true) :
    Global.chainMoment φ (frames.map (Signed.Frame.eval bank)) ≤
      Global.chainMoment φ (chain.map (Signed.Frame.eval bank)) := by
  rcases pathCheck_subset_or_constant size chain frames hp with hm | ⟨a, ha⟩
  · let : IsTrans _ Nested := ⟨fun _ _ _ h h' => h.trans h'⟩
    have hpath := (List.isChain_iff_pairwise.mp (pathCheck_chain bank size hbank chain hc frames hp)).imp
      Global.le_of_nested
    have hchain := (Signed.chainCheck_pairwise bank size hbank chain hc).imp Global.le_of_nested
    apply Global.chainMoment_le_of_subset φ hφ hsub hpath hchain
    · intro F hF
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
      exact List.mem_map.mpr ⟨f, hm f hf, rfl⟩
    · intro F hF
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
      exact f.idem bank size hbank (Signed.chainCheck_valid bank size chain hc f hf)
  · rw [Global.chainMoment_of_constant φ (a.eval bank) _ (by
      intro F hF
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
      rw [ha f hf])]
    exact Global.chainMoment_nonneg φ hφ _

end
end IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookup
