module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Model

/-! Rational dual and spanning witnesses certify dimensions of literal labels. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

structure Certificate (d : ℕ) where
  frameId : ℕ
  indices : Fin d → ℕ
  dual : Fin d → Address

def Certificate.Checked {d : ℕ} (c : Certificate d) : Prop :=
  (∀ i, c.indices i ∈ Frames.labels c.frameId) ∧
  (∀ i j, form (c.dual i) (root (c.indices j)) = if i = j then 1 else 0) ∧
  ∀ j ∈ Frames.labels c.frameId,
    root j = ∑ i, form (c.dual i) (root j) • root (c.indices i)

instance {d : ℕ} (c : Certificate d) : Decidable c.Checked := inferInstanceAs
  (Decidable ((∀ i, c.indices i ∈ Frames.labels c.frameId) ∧
    (∀ i j, form (c.dual i) (root (c.indices j)) = if i = j then 1 else 0) ∧
    ∀ j ∈ Frames.labels c.frameId,
      root j = ∑ i, form (c.dual i) (root j) • root (c.indices i)))

theorem Certificate.dimension {d : ℕ} (c : Certificate d) (h : c.Checked) :
    Module.finrank ℚ (label c.frameId) = d := by
  obtain ⟨hm, hd, hs⟩ := h
  have hi : LinearIndependent ℚ (fun i : Fin d => root (c.indices i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => form (c.dual i))
    · intro i j hij
      simpa [hij] using hd i j
    · intro i
      simpa using hd i i
  have he : label c.frameId = Submodule.span ℚ (Set.range (fun i => root (c.indices i))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      rw [hs j hj]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact root_mem _ _ (hm i)
  rw [he, finrank_span_eq_card hi, Fintype.card_fin]

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
