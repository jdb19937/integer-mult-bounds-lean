module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Model

/-! Exact rational certificates bound an actual root-span label between seven
independent roots and a nonzero normal's seven-dimensional orthogonal space. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry

structure HyperplaneCertificate where
  frameId : ℕ
  indices : Fin 7 → ℕ
  dual : Fin 7 → Address
  normal : Address

def HyperplaneCertificate.Checked (c : HyperplaneCertificate) : Prop :=
  (∀ i, c.indices i ∈ Frames.labels c.frameId) ∧
  (∀ i j, form (c.dual i) (root (c.indices j)) = if i = j then 1 else 0) ∧
  form c.normal c.normal ≠ 0 ∧
  ∀ j ∈ Frames.labels c.frameId, form c.normal (root j) = 0

instance (c : HyperplaneCertificate) : Decidable c.Checked := inferInstanceAs
  (Decidable ((∀ i, c.indices i ∈ Frames.labels c.frameId) ∧
    (∀ i j, form (c.dual i) (root (c.indices j)) = if i = j then 1 else 0) ∧
    form c.normal c.normal ≠ 0 ∧
    ∀ j ∈ Frames.labels c.frameId, form c.normal (root j) = 0))

theorem HyperplaneCertificate.dimension (c : HyperplaneCertificate) (h : c.Checked) :
    Module.finrank ℚ (label c.frameId) = 7 := by
  obtain ⟨hm, hd, hn, ho⟩ := h
  have hi : LinearIndependent ℚ (fun i : Fin 7 => root (c.indices i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => form (c.dual i))
    · intro i j hij
      simpa [hij] using hd i j
    · intro i
      simpa using hd i i
  have hs : Submodule.span ℚ (Set.range (fun i : Fin 7 => root (c.indices i))) ≤ label c.frameId := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact root_mem _ _ (hm i)
  have hl : 7 ≤ Module.finrank ℚ (label c.frameId) := by
    have hh := Submodule.finrank_mono hs
    rw [finrank_span_eq_card hi, Fintype.card_fin] at hh
    exact hh
  have hu : label c.frameId ≤ form.orthogonal (Submodule.span ℚ {c.normal}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change form (a • c.normal) (root j) = 0
    rw [LinearMap.BilinForm.smul_left, ho j hj, mul_zero]
  have hnormal : c.normal ≠ 0 := by
    intro he
    apply hn
    simp [he]
  have hr : Module.finrank ℚ (form.orthogonal (Submodule.span ℚ {c.normal})) = 7 := by
    rw [LinearMap.BilinForm.finrank_orthogonal nondegenerate,
      finrank_span_singleton hnormal]
    norm_num
  have hh := Submodule.finrank_mono hu
  rw [hr] at hh
  omega

/-- The corresponding actual inverse projector has rank seven, not an assigned cost. -/
theorem HyperplaneCertificate.copy_rank (c : HyperplaneCertificate) (h : c.Checked) :
    Module.finrank ℚ (LinearMap.range (-projector c.frameId)) = 7 := by
  rw [copyRank_eq, c.dimension h]

end IntegerMultBounds.Networks.Certificates.PR589.Geometry
