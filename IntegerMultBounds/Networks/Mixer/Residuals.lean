module

public import IntegerMultBounds.Networks.GlobalBinaryResiduals
public import IntegerMultBounds.Networks.Mixer.Labels

/-! Residual witnesses for the physical binary mixer network. Every label of a
side role has the form `common ⊔ (past ⊗ U)`, so certified growth between two
such labels follows from certified growth of the current-factor subspaces: the
past line's unit tensored with a current-factor unit is a unit in the residual.
Data and central roles reuse the motif table of the network without mixers.
Every edge of the complete trace, including the final sink alignment, grows or
shrinks with a norm-one residual vector. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Residuals

open scoped TensorProduct
open BinaryMotifResiduals GroupedFrames LabeledMotif GlobalLabels GlobalRank
  GlobalBinaryResiduals Scalar

section Mid
variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup F] [Module (ZMod 2) F]
  (g : MotifLabels.Geometry (ZMod 2) E F)

theorem mid_bot : Motif.mid g ⊥ = g.common := by
  have hz : TensorSubspace.space g.past (⊥ : Submodule (ZMod 2) F) = ⊥ := by
    apply le_antisymm _ bot_le
    apply StageLabels.space_le
    intro u _ v hv
    have hv0 : v = 0 := by simpa using hv
    simp [hv0]
  simp [Motif.mid, hz]

theorem mid_top : Motif.mid g ⊤ = g.full := by
  change g.common ⊔ TensorSubspace.space g.past ⊤ = TensorSubspace.space ⊤ ⊤
  change TensorSubspace.space g.base ⊤ ⊔ TensorSubspace.space g.past ⊤ = _
  rw [← TensorSubspace.sup_left, g.base_sup_past]

/-- Certified growth of current-factor subspaces lifts to their gate labels. -/
theorem up_mid {U V : Submodule (ZMod 2) F} (h : Up g.current U V) :
    Up g.pairing (Motif.mid g U) (Motif.mid g V) := by
  rcases h with rfl | ⟨hle, x, hx⟩
  · exact Up.refl _ _
  · obtain ⟨z, hz⟩ := unit_tensor g.earlier g.current (line_unit _ _ g.p_norm) ⟨x, hx⟩
    refine Or.inr ⟨Motif.mid_mono g hle, ⟨⟨z, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩, hz⟩⟩
    · exact Submodule.mem_sup_right (TensorSubspace.mono le_rfl inf_le_left z.property)
    · have hpb : g.past ≤ g.earlier.orthogonal g.base := by
        intro u hu b hb
        exact (g.earlier_symm.eq b u).trans (hb u hu)
      have h₁ := TensorSubspace.orthogonal_left g.earlier g.current
        (ProjectionRank.residual g.current U V) ⊤ hpb z.property
      have h₂ := TensorSubspace.orthogonal_right g.earlier g.current g.past g.past
        (show ProjectionRank.residual g.current U V ≤ g.current.orthogonal U from inf_le_right)
        z.property
      intro w hw
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
      change g.pairing (u + v) z = 0
      rw [map_add, LinearMap.add_apply]
      have hu' : g.pairing u z = 0 := h₁ u hu
      have hv' : g.pairing v z = 0 := h₂ v hv
      rw [hu', hv', add_zero]

end Mid

section Steps
variable {F : Type*} [AddCommGroup F] [Module (ZMod 2) F] {n a M : ℕ}

/-- Current-factor growth along the forward side roles. -/
structure ForwardSteps (D : LinearMap.BilinForm (ZMod 2) F) (t : Fin n → F)
    (kind : Fin a → Kind n M) (U : Fin M → Submodule (ZMod 2) F) : Prop where
  line : ∀ i, Up D ⊥ ((ZMod 2) ∙ t i)
  input_line : ∀ {p k S}, kind p = .input k S → Up D ((ZMod 2) ∙ t S) (U k)
  input_top : ∀ {p k S}, kind p = .input k S → Up D (U k) ⊤
  output_bot : ∀ {p k T}, kind p = .output k T → Up D ⊥ (U k)
  output_compl : ∀ {p k T}, kind p = .output k T →
    Up D (U k) (D.orthogonal ((ZMod 2) ∙ t T))
  direct : ∀ {p S T}, kind p = .direct S T →
    Up D ((ZMod 2) ∙ t S) (D.orthogonal ((ZMod 2) ∙ t T))

/-- Current-factor growth along the inverse side roles, where sources and targets swap. -/
structure InverseSteps (D : LinearMap.BilinForm (ZMod 2) F) (t : Fin n → F)
    (kind : Fin a → Kind n M) (U' : Fin M → Submodule (ZMod 2) F) : Prop where
  line : ∀ i, Up D ⊥ ((ZMod 2) ∙ t i)
  input_bot : ∀ {p k S}, kind p = .input k S → Up D ⊥ (U' k)
  input_compl : ∀ {p k S}, kind p = .input k S →
    Up D (U' k) (D.orthogonal ((ZMod 2) ∙ t S))
  output_line : ∀ {p k T}, kind p = .output k T → Up D ((ZMod 2) ∙ t T) (U' k)
  output_top : ∀ {p k T}, kind p = .output k T → Up D (U' k) ⊤
  direct : ∀ {p S T}, kind p = .direct S T →
    Up D ((ZMod 2) ∙ t T) (D.orthogonal ((ZMod 2) ∙ t S))

end Steps

section Chains
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (B : LinearMap.BilinForm (ZMod 2) E)

/-- A history that grows step by step, and whose last label grows to the final
label, has a complete path certificate. -/
theorem chain_certificate {initial final : Submodule (ZMod 2) E}
    {labels : List (Submodule (ZMod 2) E)} (hc : pathRel (Up B) initial labels)
    (hlast : Up B (labels.getLast?.getD initial) final) :
    PathCertificate B initial final labels := by
  induction labels generalizing initial with
  | nil =>
    exact ⟨trivial, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      by simpa using hlast⟩
  | cons U us ih =>
    have hl : Up B (us.getLast?.getD U) final := by
      cases hu : us.getLast? with
      | none =>
        have : us = [] := List.getLast?_eq_none_iff.mp hu
        subst this
        simpa using hlast
      | some V =>
        have hv : (U :: us).getLast? = some V := by
          rw [List.getLast?_cons, hu]
          rfl
        simpa [hv] using hlast
    have hrest := ih hc.2 hl
    refine ⟨⟨Or.inl hc.1, hrest.edges⟩, ?_, ?_, hc.1.trans B hrest.endpoints⟩
    · intro V hV
      rcases List.mem_cons.mp hV with rfl | hV
      · exact hc.1
      · exact hc.1.trans B (hrest.lower V hV)
    · intro V hV
      rcases List.mem_cons.mp hV with rfl | hV
      · exact hrest.endpoints
      · exact hrest.upper V hV

end Chains

section LocalCertificates
variable {h : ℕ} {E R : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [CommRing R] [DecidableEq R] [Nontrivial R] {n a c M : ℕ}
  (g : MotifLabels.Geometry (ZMod 2) E (Fin h → ZMod 2))
  (t : Fin n → (Fin h → ZMod 2)) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule (ZMod 2) (Fin h → ZMod 2))
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)
  (hs : LocalSteps g t (Fin.elim0 : Fin 0 → Fin n) Fin.elim0)

include hJ hout hs

/-- Every forward history, including the mixer roles, has a path certificate. -/
theorem mixer_forward_certificate (hf : ForwardSteps g.current t kind U)
    (i : Circuit.Role n a c 0) :
    PathCertificate g.pairing (input g t i) (output g t i)
      (history (Motif.forward g t kind U G J H) i) := by
  have hline (j : Fin n) : Up g.pairing g.common (g.xMiddle (t j)) := by
    rw [← mid_bot g]
    exact up_mid g (hf.line j)
  rcases i with i | i | p | i | i
  · change PathCertificate _ (g.xIn (t i)) ⊤ (history _ (Circuit.x i))
    rw [Motif.forward_x_history, ← g.full_eq_top]
    have h₁ := hs.x_middle i
    have h₂ := hs.middle_full i
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ (g.yIn (t i)) (g.yOut (t i)) (history _ (Circuit.y i))
    rw [Motif.forward_y_history]
    have h₁ := hs.y_common i
    have h₂ := hs.common_out i
    have h₃ := h₁.trans _ h₂
    constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.side p))
    rw [← g.full_eq_top]
    cases hp : kind p with
    | input k S =>
      rw [Motif.forward_input_history g t kind U G J H hJ hout hp]
      have h₃ : Up g.pairing (g.xMiddle (t S)) (Motif.mid g (U k)) :=
        up_mid g (hf.input_line hp)
      have h₄ : Up g.pairing (Motif.mid g (U k)) g.full := by
        rw [← mid_top g]
        exact up_mid g (hf.input_top hp)
      exact chain_certificate _ ⟨hs.bot_common, Up.refl _ _, hline S, h₃, h₄, Up.refl _ _, trivial⟩
        (by simp)
    | output k T =>
      rw [Motif.forward_output_history g t kind U G J H hJ hp]
      have h₃ : Up g.pairing g.common (Motif.mid g (U k)) := by
        rw [← mid_bot g]
        exact up_mid g (hf.output_bot hp)
      have h₄ : Up g.pairing (Motif.mid g (U k)) (g.yOut (t T)) :=
        up_mid g (hf.output_compl hp)
      exact chain_certificate _ ⟨hs.bot_common, Up.refl _ _, Up.refl _ _, h₃, h₄,
        hs.out_full T, trivial⟩ (by simp)
    | direct S T =>
      rw [Motif.forward_direct_history g t kind U G J H hJ hp]
      have h₃ : Up g.pairing (g.xMiddle (t S)) (g.yOut (t T)) := up_mid g (hf.direct hp)
      exact chain_certificate _ ⟨hs.bot_common, hline S, h₃, hs.out_full T, trivial⟩ (by simp)
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.center i))
    rw [Motif.forward_center_history, ← g.full_eq_top]
    have h₁ := hs.bot_common
    have h₂ := hs.common_full
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge, Up.edge_rev]
  · exact Fin.elim0 i

/-- Every inverse history, in logical names, has a path certificate. -/
theorem mixer_inverse_certificate (hf : InverseSteps g.current t kind U')
    (i : Circuit.Role n a c 0) :
    PathCertificate g.pairing (inverseInput g t i)
      (output g t (Circuit.exchangeRoles n a c 0 i))
      (history (Motif.inverse g t kind U' G J H) i) := by
  have hline (j : Fin n) : Up g.pairing g.common (g.xMiddle (t j)) := by
    rw [← mid_bot g]
    exact up_mid g (hf.line j)
  rcases i with i | i | p | i | i
  · change PathCertificate _ (g.yIn (t i)) (g.yOut (t i)) (history _ (Circuit.x i))
    rw [Motif.inverse_x_history]
    have h₁ := hs.y_common i
    have h₂ := hs.common_out i
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ (g.xIn (t i)) ⊤ (history _ (Circuit.y i))
    rw [Motif.inverse_y_history, ← g.full_eq_top]
    have h₁ := hs.x_middle i
    have h₂ := hs.middle_full i
    have h₃ := h₁.trans _ h₂
    constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.side p))
    rw [← g.full_eq_top]
    cases hp : kind p with
    | input k S =>
      rw [Motif.inverse_input_history g t kind U' G J H hJ hout hp]
      have h₃ : Up g.pairing g.common (Motif.mid g (U' k)) := by
        rw [← mid_bot g]
        exact up_mid g (hf.input_bot hp)
      have h₄ : Up g.pairing (Motif.mid g (U' k)) (g.yOut (t S)) :=
        up_mid g (hf.input_compl hp)
      exact chain_certificate _ ⟨hs.bot_common, Up.refl _ _, h₃, h₄, hs.out_full S,
        Up.refl _ _, trivial⟩ (by simp)
    | output k T =>
      rw [Motif.inverse_output_history g t kind U' G J H hJ hp]
      have h₃ : Up g.pairing (g.xMiddle (t T)) (Motif.mid g (U' k)) :=
        up_mid g (hf.output_line hp)
      have h₄ : Up g.pairing (Motif.mid g (U' k)) g.full := by
        rw [← mid_top g]
        exact up_mid g (hf.output_top hp)
      exact chain_certificate _ ⟨hs.bot_common, hline T, h₃, h₄, Up.refl _ _, Up.refl _ _,
        trivial⟩ (by simp)
    | direct S T =>
      rw [Motif.inverse_direct_history g t kind U' G J H hJ hp]
      have h₃ : Up g.pairing (g.xMiddle (t T)) (g.yOut (t S)) := up_mid g (hf.direct hp)
      exact chain_certificate _ ⟨hs.bot_common, hline T, h₃, hs.out_full S, trivial⟩ (by simp)
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.center i))
    rw [Motif.inverse_center_history, ← g.full_eq_top]
    have h₁ := hs.bot_common
    have h₂ := hs.common_full
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge, Up.edge_rev]
  · exact Fin.elim0 i

/-- Renaming the inverse bank names gives the physical middle-stage certificate. -/
theorem mixer_opposite_certificate (hf : InverseSteps g.current t kind U')
    (i : Circuit.Role n a c 0) :
    PathCertificate g.pairing (input g t i) (output g t i)
      (history (Motif.opposite g t kind U' G J H) i) := by
  obtain ⟨i, rfl⟩ := (Circuit.exchangeRoles n a c 0).surjective i
  rw [Motif.opposite_history]
  have he : input g t (Circuit.exchangeRoles n a c 0 i) = inverseInput g t i := by
    rcases i with i | i | i <;> rfl
  rw [he]
  exact mixer_inverse_certificate g t kind U' G J H hJ hout hs hf i

end LocalCertificates

section Fit
variable {h : ℕ} {n a M : ℕ}

/-- The enclosure inclusions of every rectangle with certified growth, for both
orientations, over the binary current factor. -/
structure EnclosureFit (t : Fin n → (Fin h → ZMod 2)) (kind : Fin a → Kind n M)
    (U U' : Fin M → Submodule (ZMod 2) (Fin h → ZMod 2)) : Prop where
  input_line : ∀ {p k S}, kind p = .input k S → Up (Labels.binary h) ((ZMod 2) ∙ t S) (U k)
  input_top : ∀ {p k S}, kind p = .input k S → Up (Labels.binary h) (U k) ⊤
  output_bot : ∀ {p k T}, kind p = .output k T → Up (Labels.binary h) ⊥ (U k)
  output_compl : ∀ {p k T}, kind p = .output k T →
    Up (Labels.binary h) (U k) ((Labels.binary h).orthogonal ((ZMod 2) ∙ t T))
  inverse_input_bot : ∀ {p k S}, kind p = .input k S → Up (Labels.binary h) ⊥ (U' k)
  inverse_input_compl : ∀ {p k S}, kind p = .input k S →
    Up (Labels.binary h) (U' k) ((Labels.binary h).orthogonal ((ZMod 2) ∙ t S))
  inverse_output_line : ∀ {p k T}, kind p = .output k T →
    Up (Labels.binary h) ((ZMod 2) ∙ t T) (U' k)
  inverse_output_top : ∀ {p k T}, kind p = .output k T → Up (Labels.binary h) (U' k) ⊤

theorem line_up (S : Finset (Fin h)) (hs : S.card = 3) :
    Up (Labels.binary h) ⊥ ((ZMod 2) ∙ Labels.indicator S) := by
  right
  refine ⟨bot_le, ?_⟩
  rw [MotifResiduals.residual_bot]
  exact line_unit _ _ (by rw [Labels.binary_self S hs]; exact one_ne_zero)

theorem neighbor_up (S T : Finset (Fin h)) (hs : S.card = 3) (ht : T.card = 3)
    (hneigh : Even (S ∩ T).card) (hh : 6 < h) :
    Up (Labels.binary h) ((ZMod 2) ∙ Labels.indicator S)
      ((Labels.binary h).orthogonal ((ZMod 2) ∙ Labels.indicator T)) := by
  have hxy : Labels.binary h (Labels.indicator S) (Labels.indicator T) = 0 :=
    Labels.binary_neighbors S T hneigh
  obtain ⟨x, hx⟩ := NeighborResidual.pair_complement_unit S T hs ht hh
  have hle : (ZMod 2) ∙ Labels.indicator S ≤
      (Labels.binary h).orthogonal ((ZMod 2) ∙ Labels.indicator T) := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hyx : Labels.binary h (Labels.indicator T) (Labels.indicator S) = 0 :=
      (Labels.form_symm 0 _ _).trans hxy
    simp [map_smul, LinearMap.smul_apply, hyx]
  right
  refine ⟨hle, ?_⟩
  · refine ⟨⟨x, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩, hx⟩
    · intro w hw
      exact x.property w (Submodule.mem_sup_right hw)
    · intro w hw
      exact x.property w (Submodule.mem_sup_left hw)

end Fit

section Stages
variable {h : ℕ} {B A C R : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R] [Nontrivial R] {n a c M : ℕ}
  (S : B → Finset (Fin h)) (hS : ∀ b, (S b).card = 3) (hh : 6 < h)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (kind : Fin a → Kind n M) (U U' : Fin M → Submodule (ZMod 2) (Fin h → ZMod 2))
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)
  (hfit : EnclosureFit (vectors S ∘ eB) kind U U')
  (hdirect : ∀ {p i j}, kind p = .direct i j → Even (S (eB i) ∩ S (eB j)).card)

local notation "cube" => GlobalProjectionRank.cubeForm (Labels.binary h)
local notation "mixInvocation" => Mixer.Labels.invocation (Labels.binary h) binarySymm
  Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
include hS hh hfit hdirect in
theorem forward_steps : ForwardSteps (Labels.binary h) (vectors S ∘ eB) kind U where
  line i := line_up _ (hS (eB i))
  input_line hp := hfit.input_line hp
  input_top hp := hfit.input_top hp
  output_bot hp := hfit.output_bot hp
  output_compl hp := hfit.output_compl hp
  direct {_ i j} hp := neighbor_up _ _ (hS (eB i)) (hS (eB j)) (hdirect hp) hh

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
include hS hh hfit hdirect in
theorem inverse_steps : InverseSteps (Labels.binary h) (vectors S ∘ eB) kind U' where
  line i := line_up _ (hS (eB i))
  input_bot hp := hfit.inverse_input_bot hp
  input_compl hp := hfit.inverse_input_compl hp
  output_line hp := hfit.inverse_output_line hp
  output_top hp := hfit.inverse_output_top hp
  direct {_ i j} hp := neighbor_up _ _ (hS (eB j)) (hS (eB i))
    (by rw [Finset.inter_comm]; exact hdirect hp) hh

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R]
  [Nontrivial R] in
include hS hh in
theorem empty_first_steps :
    LocalSteps (StageLabels.firstGeometry (Labels.binary h) binarySymm Labels.binary_nondegenerate)
      (vectors S ∘ eB) (Fin.elim0 : Fin 0 → Fin n) Fin.elim0 :=
  first_steps S hS hh eB Fin.elim0 Fin.elim0 (fun p => Fin.elim0 p)

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R]
  [Nontrivial R] in
include hS hh in
theorem empty_second_steps (q : B × B) :
    LocalSteps (StageLabels.secondGeometry (Labels.binary h) binarySymm Labels.binary_nondegenerate
      (vectors S q.1) (binaryNorm S hS q.1)) (vectors S ∘ eB) (Fin.elim0 : Fin 0 → Fin n)
      Fin.elim0 :=
  second_steps S hS hh eB Fin.elim0 Fin.elim0 (fun p => Fin.elim0 p) q

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R]
  [Nontrivial R] in
include hS hh in
theorem empty_third_steps (q : B × B) :
    LocalSteps (StageLabels.thirdGeometry (Labels.binary h) binarySymm Labels.binary_nondegenerate
      (vectors S q.1) (vectors S q.2) (binaryNorm S hS q.1) (binaryNorm S hS q.2))
      (vectors S ∘ eB) (Fin.elim0 : Fin 0 → Fin n) Fin.elim0 :=
  third_steps S hS hh eB Fin.elim0 Fin.elim0 (fun p => Fin.elim0 p) q

omit [Nontrivial R] in
/-- Every physical register outside a mixer invocation keeps its label. -/
theorem mixer_invocation_final_outside (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C →
      Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (k : GlobalCircuit.World B A C)
    (hk : ∀ i, GlobalCircuit.localEmbedding eB eA eC j q i ≠ k) :
    finalLabels current (mixInvocation j q) k = current k := by
  fin_cases j <;> simp [Mixer.Labels.invocation] <;> apply finalLabels_place_outside <;> exact hk

omit [Nontrivial R] in
theorem mixer_partial_final_outside (j : Fin 3) (qs : List (B × B))
    (current : GlobalCircuit.World B A C →
      Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (k : GlobalCircuit.World B A C)
    (hk : ∀ q ∈ qs, ∀ i, GlobalCircuit.localEmbedding eB eA eC j q i ≠ k) :
    finalLabels current (qs.flatMap (mixInvocation j)) k = current k := by
  induction qs generalizing current with
  | nil => rfl
  | cons q qs ih =>
    rw [List.flatMap_cons, finalLabels_append,
      ih _ (fun q' hq' => hk q' (by simp [hq']))]
    exact mixer_invocation_final_outside S hS eB eA eC kind U U' G J H j q current k
      (hk q (by simp))

include hh hJ hout hfit hdirect in
/-- Each placed mixer invocation has certified edges and certified output gaps,
for an already certified input gap. -/
theorem mixer_invocation_certificate (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C →
      Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ i, Up cube (current (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i)) :
    (∀ p ∈ RankTrace.edges current (updates (mixInvocation j q)), Edge cube p.1 p.2) ∧
    (∀ i, Up cube (finalLabels current (mixInvocation j q)
        (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationOutput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i)) := by
  have hf := forward_steps S hS hh eB kind U U' hfit hdirect
  have hi := inverse_steps S hS hh eB kind U U' hfit hdirect
  fin_cases j
  · simp only [Mixer.Labels.invocation, invocationInput, invocationOutput] at hcur ⊢
    have hc := mixer_forward_certificate _ (vectors S ∘ eB) kind U G J H hJ hout
      (empty_first_steps S hS hh eB) hf
    constructor
    · exact placed_edges _ _ _ _ (fun _ _ => firstLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
    · exact placed_finish _ _ _ _ (fun _ _ => firstLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
  · simp only [Mixer.Labels.invocation, invocationInput, invocationOutput] at hcur ⊢
    have hc := mixer_opposite_certificate _ (vectors S ∘ eB) kind U' G J H hJ hout
      (empty_second_steps S hS hh eB q) hi
    constructor
    · exact placed_edges _ _ _ _ (fun _ _ => secondLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
    · exact placed_finish _ _ _ _ (fun _ _ => secondLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
  · simp only [Mixer.Labels.invocation, invocationInput, invocationOutput] at hcur ⊢
    have hc := mixer_forward_certificate _ (vectors S ∘ eB) kind U G J H hJ hout
      (empty_third_steps S hS hh eB q) hf
    constructor
    · exact placed_edges _ _ _ _ (fun _ _ => thirdLabel_up _ q)
        _ _ current hcur _ hc
    · exact placed_finish _ _ _ _ (fun _ _ => thirdLabel_up _ q)
        _ _ current hcur _ hc

include hh hJ hout hfit hdirect in
/-- Disjoint placements preserve each mixer invocation's certificate while the
other fixed-coordinate keys execute. -/
theorem mixer_partial_edges (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C →
      Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ q ∈ qs, ∀ i, Up cube (current (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i)) :
    ∀ p ∈ RankTrace.edges current (updates (qs.flatMap (mixInvocation j))),
      Edge cube p.1 p.2 := by
  induction qs generalizing current with
  | nil => simp [updates, RankTrace.edges]
  | cons q qs ih =>
    have hnodup := List.nodup_cons.mp hq
    have hrest : ∀ q' ∈ qs, ∀ i, Up cube
        (finalLabels current (mixInvocation j q) (GlobalCircuit.localEmbedding eB eA eC j q' i))
        (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm
          Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q' i) := by
      intro q' hq' i
      rw [mixer_invocation_final_outside S hS eB eA eC kind U U' G J H j q current _]
      · exact hcur q' (by simp [hq']) i
      · intro i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    intro p hp
    rw [List.flatMap_cons, updates_append, RankTrace.edges_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact (mixer_invocation_certificate S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect
        j q current (hcur q (by simp))).1 p hp
    · rw [← finalLabels_trace] at hp
      exact ih hnodup.2 _ hrest p hp

include hh hJ hout hfit hdirect in
theorem mixer_partial_finish (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C →
      Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ q ∈ qs, ∀ i, Up cube (current (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i))
    (q : B × B) (hmem : q ∈ qs) (i : Circuit.Role n a c 0) :
    Up cube (finalLabels current (qs.flatMap (mixInvocation j))
        (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationOutput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i) := by
  induction qs generalizing current with
  | nil => simp at hmem
  | cons q' qs ih =>
    have hnodup := List.nodup_cons.mp hq
    rw [List.flatMap_cons, finalLabels_append]
    by_cases he : q = q'
    · subst q'
      rw [mixer_partial_final_outside S hS eB eA eC kind U U' G J H j qs _ _]
      · exact (mixer_invocation_certificate S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect
          j q current (hcur q (by simp))).2 i
      · intro q' hq' i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    · apply ih hnodup.2 _ _ ((List.mem_cons.mp hmem).resolve_left he)
      intro q'' hq'' i'
      rw [mixer_invocation_final_outside S hS eB eA eC kind U U' G J H j q' current _]
      · exact hcur q'' (by simp [hq'']) i'
      · intro i''
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q''; exact hnodup.1 hq'') i'' i'

include hh hJ hout hfit hdirect in
/-- Complete coverage and output-gap propagation for a physical mixer stage. -/
theorem mixer_stage_certificate (j : Fin 3)
    (current : GlobalCircuit.World B A C →
      Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ k, Up cube (current k) (profileInput (Labels.binary h) binarySymm
      Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j k)) :
    (∀ p ∈ RankTrace.edges current (updates (Mixer.Labels.stage (Labels.binary h) binarySymm
      Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H j)),
      Edge cube p.1 p.2) ∧
    (∀ k, Up cube (finalLabels current (Mixer.Labels.stage (Labels.binary h) binarySymm
        Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H j) k)
      (profileOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
        (binaryNorm S hS) j k)) := by
  have hi : ∀ q ∈ GlobalCircuit.keys eB, ∀ i,
      Up cube (current (GlobalCircuit.localEmbedding eB eA eC j q i))
        (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm
          Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q i) := by
    intro q _ i
    rw [← profileInput_local (Labels.binary h) binarySymm Labels.binary_nondegenerate
      (vectors S) (binaryNorm S hS) eB eA eC j q i]
    exact hcur _
  constructor
  · exact mixer_partial_edges S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect
      j _ (GlobalCircuit.keys_nodup eB) current hi
  · intro k
    by_cases hk : ∃ q i, GlobalCircuit.localEmbedding eB eA eC j q i = k
    · obtain ⟨q, i, rfl⟩ := hk
      exact (mixer_partial_finish S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect
        j _ (GlobalCircuit.keys_nodup eB) current hi q (GlobalCircuit.mem_keys eB q) i).trans _
        (invocationOutput_up_profile S hS hh eB eA eC j q i)
    · rw [Mixer.Labels.stage, mixer_partial_final_outside S hS eB eA eC kind U U' G J H j _
        current k]
      · exact (hcur k).trans _ (profileInput_up_output S hS hh eB (Fin.elim0 : Fin 0 → Fin n)
          Fin.elim0 (fun p => Fin.elim0 p) j k)
      · intro q _ i he
        exact hk ⟨q, i, he⟩

include hh hJ hout hfit hdirect in
/-- All three mixer stages have certified edges, and their final labels keep
certified gaps to the prescribed sinks. -/
theorem mixer_program_certificate :
    (∀ p ∈ RankTrace.edges (source (A := A) (C := C) (vectors S))
      (updates (Mixer.Labels.program (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H)), Edge cube p.1 p.2) ∧
    (∀ k, Up cube (finalLabels (source (vectors S))
        (Mixer.Labels.program (Labels.binary h) binarySymm Labels.binary_nondegenerate
          (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H) k)
      (sink (Labels.binary h) (vectors S) k)) := by
  have h₀ := mixer_stage_certificate S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect 0
    (source (vectors S)) (fun k => by rw [profile_zero_source])
  have hi₁ : ∀ k, Up cube (finalLabels (source (vectors S))
      (Mixer.Labels.stage (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
        (binaryNorm S hS) eB eA eC kind U U' G J H 0) k)
      (profileInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
        (binaryNorm S hS) 1 k) := by
    intro k
    rw [← profile_zero_one]
    exact h₀.2 k
  have h₁ := mixer_stage_certificate S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect 1 _ hi₁
  have hi₂ : ∀ k, Up cube (finalLabels (finalLabels (source (vectors S))
      (Mixer.Labels.stage (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
        (binaryNorm S hS) eB eA eC kind U U' G J H 0))
      (Mixer.Labels.stage (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
        (binaryNorm S hS) eB eA eC kind U U' G J H 1) k)
      (profileInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
        (binaryNorm S hS) 2 k) := by
    intro k
    rw [← profile_one_two]
    exact h₁.2 k
  have h₂ := mixer_stage_certificate S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect 2 _ hi₂
  constructor
  · intro p hp
    simp only [Mixer.Labels.program, updates_append, RankTrace.edges_append,
      RankTrace.finish_append, ← finalLabels_trace, List.mem_append, or_assoc] at hp
    rcases hp with hp | hp | hp
    · exact h₀.1 p hp
    · exact h₁.1 p hp
    · exact h₂.1 p hp
  · intro k
    rw [← profile_two_sink (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S)
      (binaryNorm S hS)]
    simpa only [Mixer.Labels.program, finalLabels_append] using h₂.2 k

include hh hJ hout hfit hdirect in
/-- Every edge of the complete mixer network trace, including the final sink
alignment, has a certified norm-one residual direction. -/
theorem mixer_network_edges (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ RankTrace.edges (source (vectors S))
      (networkUpdates wires (sink (Labels.binary h) (vectors S))
        (Mixer.Labels.program (Labels.binary h) binarySymm Labels.binary_nondegenerate
          (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H)), Edge cube p.1 p.2 := by
  obtain ⟨hc, hf⟩ := mixer_program_certificate S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact hc p hp
  · apply edges_endpoints_rel (Edge cube) (Edge.refl _) _ _ wires _ p hp
    intro k _
    rw [← finalLabels_trace]
    exact Or.inl (hf k)

include hh hJ hout hfit hdirect in
/-- Every edge of the complete mixer network trace whose labels are
nondegenerate has a norm-one residual vector, oriented by its inclusion. -/
theorem mixer_network_residuals (wires : List (GlobalCircuit.World B A C))
    (hnd : ∀ p ∈ RankTrace.edges (source (vectors S))
      (networkUpdates wires (sink (Labels.binary h) (vectors S))
        (Mixer.Labels.program (Labels.binary h) binarySymm Labels.binary_nondegenerate
          (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H)),
      ((GlobalProjectionRank.cubeForm (Labels.binary h)).restrict p.1).Nondegenerate ∧
        ((GlobalProjectionRank.cubeForm (Labels.binary h)).restrict p.2).Nondegenerate) :
    ∀ p ∈ RankTrace.edges (source (vectors S))
      (networkUpdates wires (sink (Labels.binary h) (vectors S))
        (Mixer.Labels.program (Labels.binary h) binarySymm Labels.binary_nondegenerate
          (vectors S) (binaryNorm S hS) eB eA eC kind U U' G J H)),
      (p.1 ≤ p.2 ∧ Good cube (ProjectionRank.residual cube p.1 p.2)) ∨
      (p.2 ≤ p.1 ∧ Good cube (ProjectionRank.residual cube p.2 p.1)) := by
  intro p hp
  rcases mixer_network_edges S hS hh eB eA eC kind U U' G J H hJ hout hfit hdirect wires p hp
    with he | he
  · exact Or.inl ⟨he.le _, he.good _ (hnd p hp).1⟩
  · exact Or.inr ⟨he.le _, he.good _ (hnd p hp).2⟩

end Stages

end IntegerMultBounds.Networks.Mixer.Residuals
