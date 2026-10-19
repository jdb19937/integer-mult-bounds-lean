module

public import IntegerMultBounds.Networks.ProjectionRank
public import IntegerMultBounds.Networks.BinaryOrthonormal

/-! The degree-one residual between neighboring triple lines. Its dimension
and nondegeneracy are derived from actual orthogonal subspaces. Binary unit
witnesses are coordinate vectors outside the triple supports. -/

@[expose] public section

namespace IntegerMultBounds.Networks.NeighborResidual

open Module

section Pair
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (u v : E) (hu : B u u ≠ 0) (hv : B v v ≠ 0) (huv : B u v = 0)

def pairSpace : Submodule K E := (K ∙ u) ⊔ (K ∙ v)

/-- The side-wire residual from the first line into the second line's
complement is exactly the complement of their span. -/
theorem side_residual [FiniteDimensional K E] :
    ProjectionRank.residual B (K ∙ u) (B.orthogonal (K ∙ v)) =
      B.orthogonal (pairSpace u v) := by
  apply le_antisymm
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add, LinearMap.add_apply, hx.2 a ha, hx.1 b hb, add_zero]
  · intro x hx
    exact ⟨fun y hy => hx y (Submodule.mem_sup_right hy),
      fun y hy => hx y (Submodule.mem_sup_left hy)⟩

include hs hu hv huv in
theorem pair_nondegenerate : (B.restrict (pairSpace u v)).Nondegenerate := by
  have hl : (B.restrict (pairSpace u v)).SeparatingLeft := by
    rintro ⟨x, hx⟩ hxorth
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have h1 := hxorth ⟨u, (show K ∙ u ≤ pairSpace u v from le_sup_left)
      (Submodule.mem_span_singleton_self u)⟩
    have h2 := hxorth ⟨v, (show K ∙ v ≤ pairSpace u v from le_sup_right)
      (Submodule.mem_span_singleton_self v)⟩
    have hvu : B v u = 0 := (hs.eq v u).trans huv
    change B (s • u + t • v) u = 0 at h1
    change B (s • u + t • v) v = 0 at h2
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, huv, hvu, mul_zero, add_zero, zero_add] at h1 h2
    have hs0 := (mul_eq_zero.mp h1).resolve_right hu
    have ht0 := (mul_eq_zero.mp h2).resolve_right hv
    apply Subtype.ext
    simp [hs0, ht0]
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  exact (hs.eq x y).trans (hx y)

include hu huv in
theorem pair_disjoint : Disjoint (K ∙ u) (K ∙ v) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hy
  have he := congrArg (B u) ht
  simp only [map_smul, smul_eq_mul, huv, mul_zero] at he
  have hs0 := (mul_eq_zero.mp he.symm).resolve_right hu
  simp [hs0]

end Pair

section Binary
open Labels
open scoped TensorProduct
variable {h : ℕ}

theorem coordinate_norm (i : Fin h) : binary h (Pi.single i 1) (Pi.single i 1) = 1 := by
  simp [binary, form_single]

theorem coordinate_orthogonal (S : Finset (Fin h)) (i : Fin h) (hi : i ∉ S) :
    Pi.single i 1 ∈ (binary h).orthogonal ((ZMod 2) ∙ indicator S) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [map_smul, LinearMap.smul_apply, binary, form_single, indicator, hi]

theorem exists_coordinate_outside (S : Finset (Fin h)) (hs : S.card < h) :
    ∃ i : Fin h, i ∉ S := by
  by_contra! hall
  have he : S = Finset.univ := Finset.eq_univ_of_forall hall
  simp [he] at hs

/-- A triple complement has an explicit unit, even in characteristic two. -/
theorem triple_complement_unit (S : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    ∃ x : (binary h).orthogonal ((ZMod 2) ∙ indicator S), binary h x x = 1 := by
  obtain ⟨i, hi⟩ := exists_coordinate_outside S (by omega)
  exact ⟨⟨Pi.single i 1, coordinate_orthogonal S i hi⟩, coordinate_norm i⟩

/-- Outside the union of two supports the coordinate unit lies in their common
orthogonal complement. The witness does not require the triples to be neighbors. -/
theorem pair_complement_unit (S T : Finset (Fin h)) (hs : S.card = 3)
    (ht : T.card = 3) (hh : 6 < h) :
    ∃ x : (binary h).orthogonal (pairSpace (indicator S) (indicator T)),
      binary h x x = 1 := by
  have hc : (S ∪ T).card < h := lt_of_le_of_lt (Finset.card_union_le S T) (by omega)
  obtain ⟨i, hi⟩ := exists_coordinate_outside (S ∪ T) hc
  have hS := coordinate_orthogonal S i (fun h => hi (Finset.mem_union_left T h))
  have hT := coordinate_orthogonal T i (fun h => hi (Finset.mem_union_right S h))
  refine ⟨⟨Pi.single i 1, ?_⟩, coordinate_norm i⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  simp only [map_add, LinearMap.add_apply, hS a ha, hT b hb, add_zero]

/-- The earlier/future two-factor line also has a unit in its complement.
The witness is an actual pure tensor of coordinate vectors. -/
theorem square_complement_unit (S T : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    let B : LinearMap.BilinForm (ZMod 2)
      ((Fin h → ZMod 2) ⊗[ZMod 2] (Fin h → ZMod 2)) := (binary h).tmul (binary h)
    let w := indicator S ⊗ₜ[ZMod 2] indicator T
    ∃ x : B.orthogonal ((ZMod 2) ∙ w), B x x = 1 := by
  obtain ⟨i, hi⟩ := exists_coordinate_outside S (by omega)
  let e : Fin h → ZMod 2 := Pi.single i 1
  have hn : binary h e e = 1 := coordinate_norm i
  have ho : binary h (indicator S) e = 0 := by
    simp [e, binary, form_single, indicator, hi]
  refine ⟨⟨e ⊗ₜ[ZMod 2] e, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [map_smul, LinearMap.smul_apply, LinearMap.BilinForm.tmul,
      LinearMap.BilinForm.tensorDistrib_tmul, ho]
  · simp [LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul, hn]

end Binary

end IntegerMultBounds.Networks.NeighborResidual
