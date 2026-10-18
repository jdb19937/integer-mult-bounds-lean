module

public import IntegerMultBounds.Networks.Mixer.RankStages
public import IntegerMultBounds.Networks.Mixer.Fits25
public import IntegerMultBounds.Networks.Mixer.Budget
public import IntegerMultBounds.Networks.BinaryRankFactors

/-! The size-25 mixer network as a complex supplier. Its projection-rank total is
at most `149516060359500000` on `9569028100000` wires, giving branching exponent
`1 - 25/10^10`; every edge of its label trace is nondegenerate and has an
orthonormal residual, so a single finite family of kernel directions realizes all
of its edge operators for every column count. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Supplier25

open ComplexRank25 (triples vector form_symm vector_self)
open Instance25 GlobalBinaryResiduals
open Module

/-- The side roles as a definition rather than an abbreviation, so instance
unification of host register types does not unfold the rectangle plan. -/
def SideRole := Side

instance : Fintype SideRole := inferInstanceAs (Fintype Side)
instance : DecidableEq SideRole := inferInstanceAs (DecidableEq Side)

/-- The local side-bank enumeration with physical side-role names. -/
noncomputable def sideRoles : Fin a25 ≃ SideRole := sideEquiv

theorem sideRole_card : Fintype.card SideRole = 601404 := side_card

/-- The physical wire roles of the mixer network. -/
abbrev Wire := GlobalCircuit.World (NeighborCounts.Triple 25) SideRole (Fin 26)

theorem world_card (B A C : Type*) [Fintype B] [Fintype A] [Fintype C] :
    Fintype.card (GlobalCircuit.World B A C) =
      2 * Fintype.card B ^ 3 + 3 * Fintype.card B ^ 2 * (Fintype.card A + Fintype.card C) := by
  simp only [GlobalCircuit.World, GlobalCircuit.Address, GlobalCircuit.Invocation,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

section Generic
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [Fintype B] [Fintype A] [Fintype C]
  [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [Nontrivial R] [DecidableEq R]
  {n a c M : ℕ}

/-- The rank bound in terms of the bank sizes. -/
theorem rank_le_indices (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
    (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
    (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (kind : Fin a → Scalar.Kind n M) (U U' : Fin M → Submodule K F)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
    (hout : ∀ k, ∃ p, (kind p).outRect = some k)
    (hU : ∀ k, (D.restrict (U k)).Nondegenerate) (hU' : ∀ k, (D.restrict (U' k)).Nondegenerate)
    (hfit : Rank.Fits D t eB kind U U') (wires : List (GlobalCircuit.World B A C))
    (hall : ∀ i, i ∈ wires) :
    Rank.rankSum D hs hn t ht eB eA eC kind U U' G J H wires ≤
      (2 * n ^ 3 + 3 * n ^ 2 * (a + c)) * finrank K F ^ 3 + 6 * n ^ 2 * c * finrank K F -
        2 * n ^ 3 := by
  have h := Rank.rank_le_dimensions D hs hn t ht eB eA eC kind U U' G J H hJ hout hU hU' hfit
    wires hall
  have hB : Fintype.card B = n := by rw [← Fintype.card_congr eB, Fintype.card_fin]
  have hA : Fintype.card A = a := by rw [← Fintype.card_congr eA, Fintype.card_fin]
  have hC : Fintype.card C = c := by rw [← Fintype.card_congr eC, Fintype.card_fin]
  rw [world_card, hB, hA, hC] at h
  omega

end Generic

noncomputable def gather := Circuit.complexGather (fun i => (triples i).val)
noncomputable def scatter := Circuit.complexScatter (fun i => (triples i).val)

/-- The labeled physical mixer network. -/
noncomputable def program :=
  Mixer.Labels.program (Labels.binary 25) form_symm Labels.binary_nondegenerate vector vector_self
    triples sideRoles (Equiv.refl (Fin 26)) kind Fits25.U Fits25.U' gather Fits25.J scatter

theorem program_groups : program.map GroupedFrames.Vertex.group =
    Global.program triples sideRoles (Equiv.refl (Fin 26)) kind gather Fits25.J scatter :=
  Mixer.Labels.program_groups _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Every physical wire appears once in the terminal-alignment list. -/
noncomputable def wires : List Wire := List.ofFn (Fintype.equivFin Wire).symm

theorem wires_complete (i : Wire) : i ∈ wires := by
  apply List.mem_ofFn.mpr
  exact ⟨(Fintype.equivFin _) i, (Fintype.equivFin _).symm_apply_apply i⟩

theorem fits : Rank.Fits (Labels.binary 25) vector triples kind Fits25.U Fits25.U' where
  forward_input hp := Fits25.input_le hp
  forward_output hp := Fits25.output_le hp
  direct_orth hp := Fits25.direct_orth hp
  inverse_input hp := Fits25.inverse_input_le hp
  inverse_output hp := Fits25.inverse_output_le hp

/-- The label trace of the mixer network, including the final sinks. -/
noncomputable def updates :=
  Rank.trace (Labels.binary 25) form_symm Labels.binary_nondegenerate vector vector_self
    triples sideRoles (Equiv.refl (Fin 26)) kind Fits25.U Fits25.U' gather Fits25.J scatter wires

noncomputable def rankSum : ℕ :=
  Rank.rankSum (Labels.binary 25) form_symm Labels.binary_nondegenerate vector vector_self
    triples sideRoles (Equiv.refl (Fin 26)) kind Fits25.U Fits25.U' gather Fits25.J scatter wires

theorem triple_card25 : Fintype.card (NeighborCounts.Triple 25) = 2300 := by
  rw [NeighborCounts.triple_card]
  decide

theorem wire_card : Fintype.card Wire = 9569028100000 := by
  rw [world_card, triple_card25, sideRole_card, Fintype.card_fin]
  norm_num

theorem budget_value (a f : ℕ) (ha : a = 601404) (hf : f = 25) :
    (2 * 2300 ^ 3 + 3 * 2300 ^ 2 * (a + 26)) * f ^ 3 + 6 * 2300 ^ 2 * 26 * f - 2 * 2300 ^ 3 =
      149516060359500000 := by
  subst ha hf
  norm_num

/-- The rank total of the mixer network. -/
theorem rank_budget : rankSum ≤ 149516060359500000 := by
  have h := rank_le_indices (Labels.binary 25) form_symm Labels.binary_nondegenerate
    vector vector_self triples sideRoles (Equiv.refl (Fin 26)) kind Fits25.U Fits25.U' gather
    Fits25.J scatter Fits25.support Fits25.out_exists Fits25.U_nondegenerate
    Fits25.U'_nondegenerate fits wires wires_complete
  calc rankSum ≤ _ := h
    _ = 149516060359500000 := budget_value _ _ a25_eq (by simp)

theorem branching_bound : (rankSum : ℝ) / 9569028100000 < (15625 : ℝ) ^ Budget.sigma := by
  have hr : (rankSum : ℝ) ≤ 149516060359500000 := by exact_mod_cast rank_budget
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hr (by norm_num)) Budget.branching_bound

/-! ### Edge interfaces -/

abbrev Label := Submodule (ZMod 2) (Labels.Cube (ZMod 2) 25)
abbrev form := GlobalProjectionRank.cubeForm (Labels.binary 25)
abbrev formSymm : form.IsSymm := GlobalProjectionRank.cube_symm (Labels.binary 25) form_symm
abbrev coordinateSymm : (Labels.binary (25 ^ 3)).IsSymm := ⟨Labels.form_symm 0⟩

noncomputable def edges : List (Label × Label) :=
  RankTrace.edges (GlobalLabels.source vector) updates

theorem edges_nondegenerate : ∀ p ∈ edges,
    (form.restrict p.1).Nondegenerate ∧
      (form.restrict p.2).Nondegenerate :=
  ProjectionTrace.edges_predicate (fun U : Label => (form.restrict U).Nondegenerate)
    (GlobalLabels.source vector) updates
    (GlobalProjectionRank.source_nondegenerate (Labels.binary 25) vector vector_self)
    (Rank.trace_nondegenerate (Labels.binary 25) form_symm Labels.binary_nondegenerate vector
      vector_self triples sideRoles (Equiv.refl (Fin 26)) kind Fits25.U Fits25.U' gather Fits25.J
      scatter Fits25.U_nondegenerate Fits25.U'_nondegenerate wires)

theorem rank_sum_eq : (edges.map (fun p => ProjectionTrace.edgeRank form
    formSymm p.1 p.2)).sum = rankSum := rfl

theorem edges_residuals : ∀ p ∈ edges,
    (p.1 ≤ p.2 ∧ BinaryMotifResiduals.Good form
      (ProjectionRank.residual form p.1 p.2)) ∨
    (p.2 ≤ p.1 ∧ BinaryMotifResiduals.Good form
      (ProjectionRank.residual form p.2 p.1)) :=
  Residuals.mixer_network_residuals (fun T : NeighborCounts.Triple 25 => T.val)
    (fun T => T.property) (by norm_num) triples sideRoles (Equiv.refl (Fin 26)) kind Fits25.U
    Fits25.U' gather Fits25.J scatter Fits25.support Fits25.out_exists Fits25.enclosureFit
    (fun hp => Fits25.direct_even hp) wires edges_nondegenerate

/-- Each list realizes its corresponding physical edge's coordinate-label operator,
simultaneously for every number of columns. -/
def Realizes (factors : List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3)))) : Prop :=
  List.Forall₂ (fun p gs =>
    (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
    ∀ k, BinaryRankFactors.edgeOperator coordinateSymm k
      (LabelTransport.label (TensorCoordinates.coordinates 25) p.1)
      (LabelTransport.label (TensorCoordinates.coordinates 25) p.2) =
        (gs.map (BinaryColumns.vectorFactor k)).prod) edges factors

theorem exists_uniform_factors :
    ∃ factors : List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3))),
      Realizes factors ∧ (factors.map List.length).sum = rankSum := by
  obtain ⟨factors, hop, hlen⟩ := BinaryRankFactors.exists_uniform_list_transport_factors
    form formSymm coordinateSymm
    (TensorCoordinates.coordinates 25) (TensorCoordinates.coordinates_isometry 25) edges
    edges_nondegenerate edges_residuals
  exact ⟨factors, hop, hlen.trans rank_sum_eq⟩

/-- The edge factors meet the mixer network's budget and branching exponent. -/
theorem exists_uniform_factor_budget :
    ∃ factors : List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3))),
      Realizes factors ∧ (factors.map List.length).sum ≤ 149516060359500000 ∧
      ((factors.map List.length).sum : ℝ) / 9569028100000 < (15625 : ℝ) ^ Budget.sigma := by
  obtain ⟨factors, hop, hlen⟩ := exists_uniform_factors
  exact ⟨factors, hop, hlen ▸ rank_budget, hlen ▸ branching_bound⟩

end IntegerMultBounds.Networks.Mixer.Supplier25
