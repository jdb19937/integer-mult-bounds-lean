module

public import IntegerMultBounds.Networks.TensorSubspace
public import IntegerMultBounds.Networks.ProjectionRank

/-! The actual local tensor-label table for one motif invocation. The earlier
space splits as the orthogonal complement of a nondegenerate line plus that
line. Gate labels are embedded tensor subspaces, not dimension annotations.
The side-wire comparison uses orthogonality of its two physical triple lines.
Tensoring by the future line preserves every dimension and comparison. -/

@[expose] public section

namespace IntegerMultBounds.Networks.MotifLabels

open scoped TensorProduct
open Module TensorSubspace

section OrthogonalSums
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Orthogonal sums of actual nondegenerate subspaces remain nondegenerate. -/
theorem orthogonal_sup_nondegenerate (B : LinearMap.BilinForm K V) (hs : B.IsSymm)
    (U W : Submodule K V) (hu : (B.restrict U).Nondegenerate)
    (hw : (B.restrict W).Nondegenerate) (huw : U ≤ B.orthogonal W) :
    (B.restrict (U ⊔ W)).Nondegenerate := by
  have hl : (B.restrict (U ⊔ W)).SeparatingLeft := by
    rintro ⟨x, hx⟩ hxorth
    obtain ⟨u, huMem, w, hwMem, rfl⟩ := Submodule.mem_sup.mp hx
    have hu0 : (⟨u, huMem⟩ : U) = 0 := by
      apply hu.1
      intro y
      have hh := hxorth ⟨y, Submodule.mem_sup_left y.property⟩
      have hcross : B w y = 0 := huw y.property w hwMem
      change B (u + w) y = 0 at hh
      change B u y = 0
      simpa only [map_add, LinearMap.add_apply, hcross, add_zero] using hh
    have hw0 : (⟨w, hwMem⟩ : W) = 0 := by
      apply hw.1
      intro y
      have hh := hxorth ⟨y, Submodule.mem_sup_right y.property⟩
      have hcross : B u y = 0 := (hs.eq u y).trans (huw huMem y y.property)
      change B (u + w) y = 0 at hh
      change B w y = 0
      simpa only [map_add, LinearMap.add_apply, hcross, zero_add] using hh
    apply Subtype.ext
    have hu' : u = 0 := congrArg Subtype.val hu0
    have hw' : w = 0 := congrArg Subtype.val hw0
    simp [hu', hw']
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  exact (hs.eq x y).trans (hx y)

theorem top_nondegenerate (B : LinearMap.BilinForm K V) (hn : B.Nondegenerate) :
    (B.restrict ⊤).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact hn.1 x (fun y => hx ⟨y, Submodule.mem_top⟩)
  · intro x hx
    apply Subtype.ext
    exact hn.2 x (fun y => hx ⟨y, Submodule.mem_top⟩)

theorem bot_nondegenerate (B : LinearMap.BilinForm K V) :
    (B.restrict ⊥).Nondegenerate := by
  exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
/-- A subspace filling the whole ambient space with a nondegenerate label,
while orthogonal to that label, is its actual orthogonal complement. -/
theorem orthogonal_eq_of_sup [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hs : B.IsSymm) (U W : Submodule K V) (hu : (B.restrict U).Nondegenerate)
    (hW : W ≤ B.orthogonal U) (hfull : U ⊔ W = ⊤) : W = B.orthogonal U := by
  have hc := B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hu
  have hd := hc.disjoint.mono_right hW
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq U (B.orthogonal U)
  rw [hfull, hd.eq_bot, finrank_bot, add_zero] at h1
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_bot, add_zero] at h2
  exact Submodule.eq_of_le_of_finrank_le hW (by omega)

end OrthogonalSums

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]

/-- Data defining the earlier orthogonal splitting and the current tensor factor.
No gate-label comparability or residual dimension is assumed. -/
structure Geometry (K E F : Type*) [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] where
  earlier : LinearMap.BilinForm K E
  current : LinearMap.BilinForm K F
  earlier_symm : earlier.IsSymm
  current_symm : current.IsSymm
  earlier_nd : earlier.Nondegenerate
  current_nd : current.Nondegenerate
  p : E
  p_norm : earlier p p ≠ 0

namespace Geometry
variable (g : Geometry K E F)

def past : Submodule K E := K ∙ g.p
def base : Submodule K E := g.earlier.orthogonal g.past
def pairing : LinearMap.BilinForm K (E ⊗[K] F) := form g.earlier g.current

def common : Submodule K (E ⊗[K] F) := space g.base ⊤
def full (_g : Geometry K E F) : Submodule K (E ⊗[K] F) := space (⊤ : Submodule K E) (⊤ : Submodule K F)
def xIn (_g : Geometry K E F) (t : F) : Submodule K (E ⊗[K] F) := space (⊤ : Submodule K E) (K ∙ t)
def yIn (t : F) : Submodule K (E ⊗[K] F) := space g.base (K ∙ t)
def xMiddle (t : F) : Submodule K (E ⊗[K] F) := g.common ⊔ space g.past (K ∙ t)
def yOut (t : F) : Submodule K (E ⊗[K] F) :=
  g.common ⊔ space g.past (g.current.orthogonal (K ∙ t))

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem pairing_symm : g.pairing.IsSymm := by
  exact LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp g.earlier_symm).tmul
      (LinearMap.BilinForm.isSymm_iff.mp g.current_symm))

theorem pairing_nondegenerate : g.pairing.Nondegenerate :=
  Labels.tmul_nondegenerate _ _ g.earlier_nd g.current_nd

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem past_nondegenerate : (g.earlier.restrict g.past).Nondegenerate :=
  Labels.line_nondegenerate g.earlier g.p g.p_norm

omit [FiniteDimensional K F] in
theorem base_nondegenerate : (g.earlier.restrict g.base).Nondegenerate :=
  ProjectionRank.orthogonal_nondegenerate _ g.earlier_symm g.earlier_nd _ g.past_nondegenerate

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem base_sup_past : g.base ⊔ g.past = ⊤ :=
  (LinearMap.BilinForm.isCompl_span_singleton_orthogonal g.p_norm).symm.sup_eq_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem past_finrank : finrank K g.past = 1 := by
  apply finrank_span_singleton
  intro hp
  exact g.p_norm (by simp [hp])

omit [FiniteDimensional K F] in
theorem base_finrank_add : finrank K g.base + 1 = finrank K E := by
  have hi : IsCompl g.past g.base := LinearMap.BilinForm.isCompl_span_singleton_orthogonal g.p_norm
  have hd := Submodule.finrank_sup_add_finrank_inf_eq g.base g.past
  rw [g.base_sup_past, hi.symm.inf_eq_bot, finrank_bot, add_zero, g.past_finrank] at hd
  simpa using hd.symm

theorem common_nondegenerate : (g.pairing.restrict g.common).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ g.base_nondegenerate (top_nondegenerate _ g.current_nd)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem full_eq_top : g.full = ⊤ := top_top

theorem full_nondegenerate : (g.pairing.restrict g.full).Nondegenerate := by
  rw [g.full_eq_top]
  exact top_nondegenerate _ g.pairing_nondegenerate

theorem xIn_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.xIn t)).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ (top_nondegenerate _ g.earlier_nd)
    (Labels.line_nondegenerate _ _ ht)

theorem yIn_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.yIn t)).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ g.base_nondegenerate (Labels.line_nondegenerate _ _ ht)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem common_orthogonal_past (U : Submodule K F) :
    g.common ≤ g.pairing.orthogonal (space g.past U) :=
  orthogonal_left _ _ _ _ le_rfl

theorem xMiddle_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.xMiddle t)).Nondegenerate :=
  orthogonal_sup_nondegenerate _ g.pairing_symm _ _ g.common_nondegenerate
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate (Labels.line_nondegenerate _ _ ht))
    (g.common_orthogonal_past _)

theorem yOut_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.yOut t)).Nondegenerate :=
  orthogonal_sup_nondegenerate _ g.pairing_symm _ _ g.common_nondegenerate
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate
      (ProjectionRank.orthogonal_nondegenerate _ g.current_symm g.current_nd _
        (Labels.line_nondegenerate _ _ ht))) (g.common_orthogonal_past _)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- The earlier decomposition yields the prescribed incoming X label. -/
theorem xIn_le_middle (t : F) : g.xIn t ≤ g.xMiddle t := by
  change space ⊤ (K ∙ t) ≤ g.common ⊔ space g.past (K ∙ t)
  rw [← g.base_sup_past, sup_left]
  exact sup_le_sup (mono le_rfl le_top) le_rfl

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem yIn_le_common (t : F) : g.yIn t ≤ g.common := mono le_rfl le_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem common_le_yOut (t : F) : g.common ≤ g.yOut t := le_sup_left

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem middle_le_full (t : F) : g.xMiddle t ≤ g.full := by rw [g.full_eq_top]; exact le_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem yOut_le_full (t : F) : g.yOut t ≤ g.full := by rw [g.full_eq_top]; exact le_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem common_le_full : g.common ≤ g.full := mono le_top le_rfl

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- This is the essential neighbor-dependent comparison on a side wire. -/
theorem neighbor_line (tX tY : F) (hneigh : g.current tX tY = 0) :
    K ∙ tX ≤ g.current.orthogonal (K ∙ tY) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hyx : g.current tY tX = 0 := (g.current_symm.eq tY tX).trans hneigh
  simp [map_smul, LinearMap.smul_apply, hyx]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem side_middle_le_out (tX tY : F) (hneigh : g.current tX tY = 0) :
    g.xMiddle tX ≤ g.yOut tY :=
  sup_le_sup le_rfl (mono le_rfl (g.neighbor_line tX tY hneigh))

/-- The side-wire last label is exactly the complement of the exposed tensor
line, which is the earlier-space complement needed by the next stage. -/
theorem yOut_eq_orthogonal (t : F) (ht : g.current t t ≠ 0) :
    g.yOut t = g.pairing.orthogonal (space g.past (K ∙ t)) := by
  apply orthogonal_eq_of_sup _ g.pairing_symm
    (space g.past (K ∙ t)) (g.yOut t)
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate
      (Labels.line_nondegenerate _ _ ht))
  · exact sup_le (g.common_orthogonal_past _)
      (orthogonal_right g.earlier g.current g.past g.past le_rfl)
  · have hcurrent : (K ∙ t) ⊔ g.current.orthogonal (K ∙ t) = ⊤ :=
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal ht).sup_eq_top
    have hsplit : space g.past (K ∙ t) ⊔ space g.past (g.current.orthogonal (K ∙ t)) =
        space g.past (⊤ : Submodule K F) := by rw [← sup_right, hcurrent]
    have hfull : g.common ⊔ space g.past (⊤ : Submodule K F) = ⊤ := by
      change space g.base ⊤ ⊔ space g.past ⊤ = ⊤
      rw [← sup_left, g.base_sup_past, top_top]
    calc
      space g.past (K ∙ t) ⊔ g.yOut t =
          g.common ⊔ (space g.past (K ∙ t) ⊔
            space g.past (g.current.orthogonal (K ∙ t))) := by dsimp [yOut]; ac_rfl
      _ = ⊤ := by rw [hsplit, hfull]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Every X data edge in the local table is increasing or stationary. -/
theorem x_chain (t : F) :
    List.IsChain (· ≤ ·) [g.xIn t, g.xMiddle t, g.full, g.full, g.full] := by
  simp [List.isChain_cons_cons, g.xIn_le_middle, g.middle_le_full]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Every Y data edge in the local table is increasing or stationary. -/
theorem y_chain (t : F) :
    List.IsChain (· ≤ ·) [g.yIn t, g.yIn t, g.common, g.common, g.yOut t] := by
  simp [List.isChain_cons_cons, g.yIn_le_common, g.common_le_yOut]

/-- The unique returning central edge removes the entire remaining tensor factor. -/
theorem central_dimension_loss : finrank K g.full - finrank K g.common = finrank K F := by
  have hb := g.base_finrank_add
  change finrank K (space (⊤ : Submodule K E) (⊤ : Submodule K F)) -
    finrank K (space g.base (⊤ : Submodule K F)) = finrank K F
  rw [finrank_space, finrank_space]
  have ht : finrank K (⊤ : Submodule K E) = finrank K E := by simp
  have hf : finrank K (⊤ : Submodule K F) = finrank K F := by simp
  rw [ht, hf]
  have he := congrArg (· * finrank K F) hb
  simp only [Nat.add_mul, one_mul] at he
  omega

/-- The rank loss is also the dimension of the actual orthogonal residual. -/
theorem central_residual_dimension :
    finrank K (ProjectionRank.residual g.pairing g.common g.full) = finrank K F := by
  rw [ProjectionRank.residual_finrank _ g.pairing_symm _ _ g.common_nondegenerate
    g.common_le_full, g.central_dimension_loss]

/-- The removed central subspace is concretely P tensor F. -/
theorem central_residual_eq :
    ProjectionRank.residual g.pairing g.common g.full =
      space g.past (⊤ : Submodule K F) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · apply le_inf
    · rw [g.full_eq_top]
      exact le_top
    · intro x hx y hy
      exact (g.pairing_symm.eq y x).trans (g.common_orthogonal_past ⊤ hy x hx)
  · rw [g.central_residual_dimension, finrank_space, g.past_finrank, one_mul]
    simp

section Future
variable {H : Type*} [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- Restore the one-dimensional future factor in the actual ambient tensor space. -/
def liftLabel (q : H) (U : Submodule K (E ⊗[K] F)) :
    Submodule K ((E ⊗[K] F) ⊗[K] H) := space U (K ∙ q)

def liftedPairing (D : LinearMap.BilinForm K H) :
    LinearMap.BilinForm K ((E ⊗[K] F) ⊗[K] H) := form g.pairing D

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H] in
theorem liftLabel_mono (q : H) {U V : Submodule K (E ⊗[K] F)} (hUV : U ≤ V) :
    liftLabel q U ≤ liftLabel q V := mono hUV le_rfl

theorem liftLabel_finrank (D : LinearMap.BilinForm K H) (q : H) (hq : D q q ≠ 0)
    (U : Submodule K (E ⊗[K] F)) : finrank K (liftLabel q U) = finrank K U := by
  change finrank K (space U (K ∙ q)) = _
  rw [finrank_space, finrank_span_singleton (show q ≠ 0 from fun hz => hq (by simp [hz])), mul_one]

theorem liftLabel_nondegenerate (D : LinearMap.BilinForm K H) (q : H) (hq : D q q ≠ 0)
    (U : Submodule K (E ⊗[K] F)) (hU : (g.pairing.restrict U).Nondegenerate) :
    ((g.liftedPairing D).restrict (liftLabel q U)).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ hU (Labels.line_nondegenerate _ _ hq)

theorem lifted_central_dimension_loss (D : LinearMap.BilinForm K H) (q : H)
    (hq : D q q ≠ 0) :
    finrank K (liftLabel q g.full) - finrank K (liftLabel q g.common) = finrank K F := by
  rw [liftLabel_finrank D q hq, liftLabel_finrank D q hq, g.central_dimension_loss]

end Future

end Geometry
end IntegerMultBounds.Networks.MotifLabels
