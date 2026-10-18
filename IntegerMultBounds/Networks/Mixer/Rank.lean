module

public import IntegerMultBounds.Networks.GlobalRankStages
public import IntegerMultBounds.Networks.GlobalLabelsNondegenerate
public import IntegerMultBounds.Networks.Mixer.Labels

/-! Rank accounting for the physical three-stage mixer network: nondegeneracy of
every placed label, and loss, comparability and final-label bounds for each
placed invocation. The placement and stage-transport lemmas of the motif without
mixers apply unchanged; only the local motif lemmas differ. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Rank

open GroupedFrames GlobalLabels LabeledMotif GlobalRank StageLabels Scalar
open Module
open scoped TensorProduct

section Fit
variable {K F B : Type*} [Field K] [AddCommGroup F] [Module K F] {n a M : ℕ}

/-- Label inclusions of the rectangle enclosures, stated in the current form `D`. -/
structure Fits (D : LinearMap.BilinForm K F) (t : B → F) (eB : Fin n ≃ B)
    (kind : Fin a → Kind n M) (U U' : Fin M → Submodule K F) : Prop where
  forward_input : ∀ {p k S}, kind p = .input k S → K ∙ t (eB S) ≤ U k
  forward_output : ∀ {p k T}, kind p = .output k T → U k ≤ D.orthogonal (K ∙ t (eB T))
  direct_orth : ∀ {p S T}, kind p = .direct S T → D (t (eB S)) (t (eB T)) = 0
  inverse_input : ∀ {p k S}, kind p = .input k S → U' k ≤ D.orthogonal (K ∙ t (eB S))
  inverse_output : ∀ {p k T}, kind p = .output k T → K ∙ t (eB T) ≤ U' k

variable {E : Type*} [AddCommGroup E] [Module K E] {D : LinearMap.BilinForm K F}
  {t : B → F} {eB : Fin n ≃ B} {kind : Fin a → Kind n M} {U U' : Fin M → Submodule K F}

theorem Fits.forward (hf : Fits D t eB kind U U') (g : MotifLabels.Geometry K E F)
    (hg : g.current = D) : Motif.ForwardFit g (t ∘ eB) kind U where
  input_le hp := hf.forward_input hp
  output_le hp := by rw [hg]; exact hf.forward_output hp
  direct_orth hp := by rw [hg]; exact hf.direct_orth hp

theorem Fits.inverse (hf : Fits D t eB kind U U') (hs : D.IsSymm)
    (g : MotifLabels.Geometry K E F) (hg : g.current = D) : Motif.InverseFit g (t ∘ eB) kind U' where
  input_le hp := by rw [hg]; exact hf.inverse_input hp
  output_le hp := hf.inverse_output hp
  direct_orth hp := by
    rw [hg]
    change D (t (eB _)) (t (eB _)) = 0
    rw [hs.eq]
    exact hf.direct_orth hp

end Fit

section Nondegenerate
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R]
  {n a c M : ℕ}
variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (kind : Fin a → Kind n M) (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (hU : ∀ k, (D.restrict (U k)).Nondegenerate) (hU' : ∀ k, (D.restrict (U' k)).Nondegenerate)

include hU hU' in
omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- Every placed group of a mixer invocation carries a nondegenerate cube subspace. -/
theorem invocation_nondegenerate (j : Fin 3) (q : B × B)
    (v : Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R)
    (hv : v ∈ Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict v.label).Nondegenerate := by
  unfold Labels.invocation at hv
  split_ifs at hv with hj0 hj1
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact firstLabel_nondegenerate D t ht q w.label
      (Motif.forward_nondegenerate (firstGeometry D hs hn) (t ∘ eB) kind U G J H
        (fun i => ht (eB i)) hU w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact secondLabel_nondegenerate D t ht q w.label
      (Motif.opposite_nondegenerate (secondGeometry D hs hn (t q.1) (ht q.1))
        (t ∘ eB) kind U' G J H (fun i => ht (eB i)) hU' w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact thirdLabel_nondegenerate D q w.label
      (Motif.forward_nondegenerate
        (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
        (t ∘ eB) kind U G J H (fun i => ht (eB i)) hU w hw)

include hU hU' in
omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem program_nondegenerate
    (v : Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R)
    (hv : v ∈ Labels.program D hs hn t ht eB eA eC kind U U' G J H) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict v.label).Nondegenerate := by
  have hstage (j : Fin 3) (hv : v ∈ Labels.stage D hs hn t ht eB eA eC kind U U' G J H j) :
      ((TensorSubspace.form D (TensorSubspace.form D D)).restrict v.label).Nondegenerate := by
    obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hv
    exact invocation_nondegenerate D hs hn t ht eB eA eC kind U U' G J H hU hU' j q v hq
  simp only [Labels.program, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · exact hstage 0 hv
  · exact hstage 1 hv
  · exact hstage 2 hv

end Nondegenerate

section LocalInputs
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ}
variable (g : MotifLabels.Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Every forward label seen by a wire contains that wire's input. -/
theorem forward_input_le_history (i : Circuit.Role n a c s) (V : Submodule K (E ⊗[K] F))
    (hV : V ∈ history (Motif.forward g t kind U G J H) i) : input g t i ≤ V := by
  rcases i with j | j | j
  · change V ∈ history _ (Circuit.x j) at hV
    rw [Motif.forward_x_history] at hV
    change g.xIn (t j) ≤ V
    have h₁ := g.xIn_le_middle (t j)
    have h₂ := h₁.trans (g.middle_le_full (t j))
    split_ifs at hV <;> simp_all <;> aesop
  · change V ∈ history _ (Circuit.y j) at hV
    rw [Motif.forward_y_history] at hV
    change g.yIn (t j) ≤ V
    have h₁ := g.yIn_le_common (t j)
    have h₂ := h₁.trans (g.common_le_yOut (t j))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hV
    aesop
  · exact bot_le

theorem inverse_input_le_history (i : Circuit.Role n a c s) (V : Submodule K (E ⊗[K] F))
    (hV : V ∈ history (Motif.inverse g t kind U' G J H) i) : inverseInput g t i ≤ V := by
  rcases i with j | j | j
  · change V ∈ history _ (Circuit.x j) at hV
    rw [Motif.inverse_x_history] at hV
    change g.yIn (t j) ≤ V
    have h₁ := g.yIn_le_common (t j)
    have h₂ := h₁.trans (g.common_le_yOut (t j))
    split_ifs at hV <;> simp_all <;> aesop
  · change V ∈ history _ (Circuit.y j) at hV
    rw [Motif.inverse_y_history] at hV
    change g.xIn (t j) ≤ V
    have h₁ := g.xIn_le_middle (t j)
    have h₂ := h₁.trans (g.middle_le_full (t j))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hV
    aesop
  · exact bot_le

theorem opposite_input_le_history (i : Circuit.Role n a c s) (V : Submodule K (E ⊗[K] F))
    (hV : V ∈ history (Motif.opposite g t kind U' G J H) i) : input g t i ≤ V := by
  obtain ⟨i, rfl⟩ := (Circuit.exchangeRoles n a c s).surjective i
  rw [Motif.opposite_history] at hV
  have hi : input g t (Circuit.exchangeRoles n a c s i) = inverseInput g t i := by
    rcases i with j | j | j <;> rfl
  rw [hi]
  exact inverse_input_le_history g t kind U' G J H i V hV

end LocalInputs

section Invocations
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R] [Nontrivial R] {n a c M : ℕ}
variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (kind : Fin a → Kind n M) (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)
  (hfit : Fits D t eB kind U U')

variable [Fintype B] [Fintype A] [Fintype C]

include hJ hout hfit in
/-- A placed mixer invocation loses at most one current-factor dimension per
central register, even after sparse earlier stages leave smaller labels. -/
theorem invocation_loss_le (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput D hs hn t ht eB j q i) :
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V)
      current (updates (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q)) ≤
      c * finrank K F := by
  fin_cases j
  · simp [Labels.invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    calc
      _ ≤ RankTrace.loss (fun V : Submodule K (K ⊗[K] F) => finrank K V)
          (input (firstGeometry D hs hn) (t ∘ eB))
          (updates (Motif.forward (firstGeometry D hs hn) (t ∘ eB) kind U G J H)) := by
        apply loss_place_le (GlobalCircuit.localEmbedding eB eA eC 0 q) (firstLabel t q)
          _ _ (firstLabel_finrank D t ht q)
        intro i
        have hd := Submodule.finrank_mono (hcur i)
        rwa [firstLabel_finrank D t ht q] at hd
      _ ≤ _ := Motif.forward_loss_le (firstGeometry D hs hn) (t ∘ eB) kind U G J H hJ hout
        (hfit.forward _ rfl)
  · simp [Labels.invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    calc
      _ ≤ RankTrace.loss (fun V : Submodule K (F ⊗[K] F) => finrank K V)
          (input (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB))
          (updates (Motif.opposite (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB)
            kind U' G J H)) := by
        apply loss_place_le (GlobalCircuit.localEmbedding eB eA eC 1 q) (secondLabel t q)
          _ _ (secondLabel_finrank D t ht q)
        intro i
        have hd := Submodule.finrank_mono (hcur i)
        rwa [secondLabel_finrank D t ht q] at hd
      _ ≤ _ := Motif.opposite_loss_le (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB)
        kind U' G J H hJ hout (hfit.inverse hs _ rfl)
  · simp [Labels.invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    calc
      _ ≤ RankTrace.loss (fun V : Submodule K ((F ⊗[K] F) ⊗[K] F) => finrank K V)
          (input (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB))
          (updates (Motif.forward (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
            (t ∘ eB) kind U G J H)) := by
        apply loss_place_le (GlobalCircuit.localEmbedding eB eA eC 2 q)
          (thirdLabel (K := K) (F := F) q) _ _ (thirdLabel_finrank (K := K) (F := F) q)
        intro i
        have hd := Submodule.finrank_mono (hcur i)
        rwa [thirdLabel_finrank (K := K) (F := F) q] at hd
      _ ≤ _ := Motif.forward_loss_le (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
        (t ∘ eB) kind U G J H hJ hout (hfit.forward _ rfl)

omit [Fintype B] [Fintype A] [Fintype C] in
include hJ hout hfit in
/-- Every placed edge of a mixer invocation is comparable. -/
theorem invocation_comparable (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput D hs hn t ht eB j q i) :
    ∀ p ∈ RankTrace.edges current
      (updates (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  fin_cases j
  · simp [Labels.invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    apply comparable_place_le (GlobalCircuit.localEmbedding eB eA eC 0 q) (firstLabel t q)
      (firstLabel_mono t q) (input (firstGeometry D hs hn) (t ∘ eB)) current hcur
    · exact forward_input_le_history (firstGeometry D hs hn) (t ∘ eB) kind U G J H
    · exact Motif.forward_histories_comparable (firstGeometry D hs hn) (t ∘ eB) kind U G J H
        hJ hout (hfit.forward _ rfl)
  · simp [Labels.invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    apply comparable_place_le (GlobalCircuit.localEmbedding eB eA eC 1 q) (secondLabel t q)
      (secondLabel_mono t q) (input (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB))
      current hcur
    · exact opposite_input_le_history (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) kind U'
        G J H
    · exact Motif.opposite_histories_comparable (secondGeometry D hs hn (t q.1) (ht q.1))
        (t ∘ eB) kind U' G J H hJ hout (hfit.inverse hs _ rfl)
  · simp [Labels.invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    apply comparable_place_le (GlobalCircuit.localEmbedding eB eA eC 2 q)
      (thirdLabel (K := K) (F := F) q) (thirdLabel_mono (K := K) (F := F) q)
      (input (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB)) current hcur
    · exact forward_input_le_history (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
        (t ∘ eB) kind U G J H
    · exact Motif.forward_histories_comparable
        (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) kind U G J H
        hJ hout (hfit.forward _ rfl)

omit [Fintype B] [Fintype A] [Fintype C] in
theorem invocation_final_le_zero (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC 0 q i) ≤
      invocationInput D hs hn t ht eB 0 q i) (i : Circuit.Role n a c 0) :
    finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H 0 q)
      (GlobalCircuit.localEmbedding eB eA eC 0 q i) ≤ invocationOutput D hs hn t ht eB 0 q i := by
  rw [Labels.invocation, if_pos rfl, invocationOutput, if_pos rfl]
  refine finalLabels_place_le _ _ (firstLabel_mono t q) _ _ current (fun i => ?_) _
    (Motif.forward_final_le_output _ _ kind U G J H) i
  have h := hcur i
  rwa [invocationInput, if_pos rfl] at h

omit [Fintype B] [Fintype A] [Fintype C] in
theorem invocation_final_le_one (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC 1 q i) ≤
      invocationInput D hs hn t ht eB 1 q i) (i : Circuit.Role n a c 0) :
    finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H 1 q)
      (GlobalCircuit.localEmbedding eB eA eC 1 q i) ≤ invocationOutput D hs hn t ht eB 1 q i := by
  rw [Labels.invocation, if_neg (by decide), if_pos rfl, invocationOutput, if_neg (by decide),
    if_pos rfl]
  refine finalLabels_place_le _ _ (secondLabel_mono t q) _ _ current (fun i => ?_) _
    (Motif.opposite_final_le_output _ _ kind U' G J H) i
  have h := hcur i
  rwa [invocationInput, if_neg (by decide), if_pos rfl] at h

omit [Fintype B] [Fintype A] [Fintype C] in
theorem invocation_final_le_two (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC 2 q i) ≤
      invocationInput D hs hn t ht eB 2 q i) (i : Circuit.Role n a c 0) :
    finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H 2 q)
      (GlobalCircuit.localEmbedding eB eA eC 2 q i) ≤ invocationOutput D hs hn t ht eB 2 q i := by
  rw [Labels.invocation, if_neg (by decide), if_neg (by decide), invocationOutput,
    if_neg (by decide), if_neg (by decide)]
  refine finalLabels_place_le _ _ (thirdLabel_mono (K := K) (F := F) q) _ _ current
    (fun i => ?_) _ (Motif.forward_final_le_output _ _ kind U G J H) i
  have h := hcur i
  rwa [invocationInput, if_neg (by decide), if_neg (by decide)] at h

omit [Fintype B] [Fintype A] [Fintype C] in
/-- The completed local output bounds the placed labels after a mixer invocation. -/
theorem invocation_final_le (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput D hs hn t ht eB j q i) (i : Circuit.Role n a c 0) :
    finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q)
      (GlobalCircuit.localEmbedding eB eA eC j q i) ≤ invocationOutput D hs hn t ht eB j q i := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by fin_cases j <;> simp) with rfl | rfl | rfl
  · exact invocation_final_le_zero D hs hn t ht eB eA eC kind U U' G J H q current hcur i
  · exact invocation_final_le_one D hs hn t ht eB eA eC kind U U' G J H q current hcur i
  · exact invocation_final_le_two D hs hn t ht eB eA eC kind U U' G J H q current hcur i

omit [Nontrivial R] [Fintype B] [Fintype A] [Fintype C] in
/-- Registers outside a mixer invocation keep their labels. -/
theorem invocation_final_outside (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (k : GlobalCircuit.World B A C)
    (hk : ∀ i, GlobalCircuit.localEmbedding eB eA eC j q i ≠ k) :
    finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q) k =
      current k := by
  fin_cases j <;> simp [Labels.invocation] <;> apply finalLabels_place_outside <;> exact hk

end Invocations

end IntegerMultBounds.Networks.Mixer.Rank
