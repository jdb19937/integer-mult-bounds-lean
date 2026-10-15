module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.All

/-! Ordered rank profiles use the ranges of genuine rational projector differences.
Finite root-list inclusions imply actual subspace nesting. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Moves

def value (p : ℕ × ℕ) : ℕ :=
  (Dimensions.value p.2 - Dimensions.value p.1) +
    (Dimensions.value p.1 - Dimensions.value p.2)

def CheckedPair (p : ℕ × ℕ) : Prop :=
  p.1 < 636 ∧ p.2 < 636 ∧
    (p.1 = p.2 ∨
      (∀ j ∈ Frames.labels p.1, j ∈ Frames.labels p.2) ∨
      (∀ j ∈ Frames.labels p.2, j ∈ Frames.labels p.1))

instance (p : ℕ × ℕ) : Decidable (CheckedPair p) := inferInstanceAs
  (Decidable (p.1 < 636 ∧ p.2 < 636 ∧
    (p.1 = p.2 ∨
      (∀ j ∈ Frames.labels p.1, j ∈ Frames.labels p.2) ∨
      (∀ j ∈ Frames.labels p.2, j ∈ Frames.labels p.1))))

theorem label_le (i j : ℕ) (h : ∀ k ∈ Frames.labels i, k ∈ Frames.labels j) :
    label i ≤ label j := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, rfl⟩
  exact root_mem _ _ (h k hk)

theorem nested (p : ℕ × ℕ) (h : CheckedPair p) :
    label p.1 ≤ label p.2 ∨ label p.2 ≤ label p.1 := by
  rcases h.2.2 with he | hf | hb
  · exact Or.inl (le_of_eq (congrArg label he))
  · exact Or.inl (label_le _ _ hf)
  · exact Or.inr (label_le _ _ hb)

theorem rank (p : ℕ × ℕ) (h : CheckedPair p) : moveRank p.1 p.2 = value p := by
  rw [moveRank_eq _ _ (nested p h), Dimensions.dimension _ h.1,
    Dimensions.dimension _ h.2.1]
  rfl

theorem profile (ps : List (ℕ × ℕ)) (h : ∀ p ∈ ps, CheckedPair p) :
    ps.map (fun p => moveRank p.1 p.2) = ps.map value := by
  apply List.map_congr_left
  intro p hp
  exact rank p (h p hp)

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Moves
