module

public import IntegerMultBounds.Networks.GlobalProjectionRank
public import IntegerMultBounds.Networks.Mixer.Rank

/-! Rank accounting for the whole mixer network: aggregation over the disjoint
invocations of each stage, the three stage boundaries, and the resulting
projection-rank bound. The stage profiles are those of the network without
mixers; only the per-invocation bounds come from the mixer motif. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Rank

open GroupedFrames GlobalLabels LabeledMotif GlobalRank StageLabels Scalar
open Module
open scoped TensorProduct

section Stage
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

omit [Nontrivial R] in
theorem partial_final_outside (j : Fin 3) (qs : List (B × B))
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (k : GlobalCircuit.World B A C)
    (hk : ∀ q ∈ qs, ∀ i, GlobalCircuit.localEmbedding eB eA eC j q i ≠ k) :
    finalLabels current (qs.flatMap (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j))
      k = current k := by
  induction qs generalizing current with
  | nil => rfl
  | cons q qs ih =>
    rw [List.flatMap_cons, finalLabels_append,
      ih _ (fun q' hq' => hk q' (by simp [hq']))]
    exact invocation_final_outside D hs hn t ht eB eA eC kind U U' G J H j q current k
      (hk q (by simp))

variable [Fintype B] [Fintype A] [Fintype C]

include hJ hout hfit in
theorem partial_loss_le (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ q ∈ qs, ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput (a := a) (c := c) D hs hn t ht eB j q i) :
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V) current
      (updates (qs.flatMap (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j))) ≤
      qs.length * (c * finrank K F) := by
  induction qs generalizing current with
  | nil => simp [updates, RankTrace.loss, RankTrace.edges]
  | cons q qs ih =>
    have hnodup := List.nodup_cons.mp hq
    have hrest : ∀ q' ∈ qs, ∀ i,
        finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q)
          (GlobalCircuit.localEmbedding eB eA eC j q' i) ≤
          invocationInput (a := a) (c := c) D hs hn t ht eB j q' i := by
      intro q' hq' i
      rw [invocation_final_outside D hs hn t ht eB eA eC kind U U' G J H j q current _]
      · exact hcur q' (by simp [hq']) i
      · intro i'
        exact localEmbedding_disjoint eB eA eC j
          (by intro he; subst q'; exact hnodup.1 hq') i' i
    have hfirst := invocation_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit
      j q current (hcur q (by simp))
    have htail := ih hnodup.2 _ hrest
    rw [List.flatMap_cons, updates_append, loss_append, ← finalLabels_trace]
    simp only [List.length_cons, Nat.add_mul, one_mul]
    omega

omit [Fintype B] [Fintype A] [Fintype C] in
include hJ hout hfit in
theorem partial_comparable (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ q ∈ qs, ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput (a := a) (c := c) D hs hn t ht eB j q i) :
    ∀ p ∈ RankTrace.edges current
      (updates (qs.flatMap (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j))),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  induction qs generalizing current with
  | nil => simp [updates, RankTrace.edges]
  | cons q qs ih =>
    have hnodup := List.nodup_cons.mp hq
    have hrest : ∀ q' ∈ qs, ∀ i,
        finalLabels current (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j q)
          (GlobalCircuit.localEmbedding eB eA eC j q' i) ≤
          invocationInput (a := a) (c := c) D hs hn t ht eB j q' i := by
      intro q' hq' i
      rw [invocation_final_outside D hs hn t ht eB eA eC kind U U' G J H j q current _]
      · exact hcur q' (by simp [hq']) i
      · intro i'
        exact localEmbedding_disjoint eB eA eC j
          (by intro he; subst q'; exact hnodup.1 hq') i' i
    intro p hp
    rw [List.flatMap_cons, updates_append, RankTrace.edges_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact invocation_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit
        j q current (hcur q (by simp)) p hp
    · rw [← finalLabels_trace] at hp
      exact ih hnodup.2 _ hrest p hp

omit [Fintype B] [Fintype A] [Fintype C] in
theorem partial_final_le (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ q ∈ qs, ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput (a := a) (c := c) D hs hn t ht eB j q i) (q : B × B) (hmem : q ∈ qs)
    (i : Circuit.Role n a c 0) :
    finalLabels current (qs.flatMap (Labels.invocation D hs hn t ht eB eA eC kind U U' G J H j))
      (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationOutput (a := a) (c := c) D hs hn t ht eB j q i := by
  induction qs generalizing current with
  | nil => simp at hmem
  | cons q' qs ih =>
    have hnodup := List.nodup_cons.mp hq
    rw [List.flatMap_cons, finalLabels_append]
    by_cases he : q = q'
    · subst q'
      rw [partial_final_outside D hs hn t ht eB eA eC kind U U' G J H j qs _ _]
      · exact invocation_final_le D hs hn t ht eB eA eC kind U U' G J H j q current
          (hcur q (by simp)) i
      · intro q' hq' i'
        exact localEmbedding_disjoint eB eA eC j
          (by intro he; subst q'; exact hnodup.1 hq') i' i
    · apply ih hnodup.2 _ _ ((List.mem_cons.mp hmem).resolve_left he)
      intro q'' hq'' i'
      rw [invocation_final_outside D hs hn t ht eB eA eC kind U U' G J H j q' current _]
      · exact hcur q'' (by simp [hq'']) i'
      · intro i''
        exact localEmbedding_disjoint eB eA eC j
          (by intro he; subst q''; exact hnodup.1 hq'') i'' i'

include hJ hout hfit in
theorem stage_loss_le (j : Fin 3)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ k, current k ≤ profileInput D hs hn t ht j k) :
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V) current
      (updates (Labels.stage D hs hn t ht eB eA eC kind U U' G J H j)) ≤
      n * n * (c * finrank K F) := by
  rw [Labels.stage, ← GlobalCircuit.keys_length eB]
  apply partial_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit j _
    (GlobalCircuit.keys_nodup eB)
  intro q _ i
  rw [← profileInput_local D hs hn t ht eB eA eC j q i]
  exact hcur _

omit [Fintype B] [Fintype A] [Fintype C] in
include hJ hout hfit in
theorem stage_comparable (j : Fin 3)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ k, current k ≤ profileInput D hs hn t ht j k) :
    ∀ p ∈ RankTrace.edges current (updates (Labels.stage D hs hn t ht eB eA eC kind U U' G J H j)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  apply partial_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit j _
    (GlobalCircuit.keys_nodup eB)
  intro q _ i
  rw [← profileInput_local D hs hn t ht eB eA eC j q i]
  exact hcur _

omit [Fintype B] [Fintype A] [Fintype C] in
theorem stage_final_le (j : Fin 3)
    (current : GlobalCircuit.World B A C → Submodule K (Ambient K F))
    (hcur : ∀ k, current k ≤ profileInput D hs hn t ht j k) (k : GlobalCircuit.World B A C) :
    finalLabels current (Labels.stage D hs hn t ht eB eA eC kind U U' G J H j) k ≤
      profileOutput D hs hn t ht j k := by
  by_cases hk : ∃ q i, GlobalCircuit.localEmbedding eB eA eC j q i = k
  · obtain ⟨q, i, rfl⟩ := hk
    apply (partial_final_le D hs hn t ht eB eA eC kind U U' G J H j _
      (GlobalCircuit.keys_nodup eB) current ?_ q (GlobalCircuit.mem_keys eB q) i).trans
      (invocationOutput_le_profile D hs hn t ht eB eA eC j q i)
    intro q' _ i'
    rw [← profileInput_local D hs hn t ht eB eA eC j q' i']
    exact hcur _
  · rw [Labels.stage, partial_final_outside D hs hn t ht eB eA eC kind U U' G J H j _ current k]
    · exact (hcur k).trans (profileInput_le_output D hs hn t ht j k)
    · intro q _ i he
      exact hk ⟨q, i, he⟩

/-- The labels after the first stage. -/
def afterFirst : GlobalCircuit.World B A C → Submodule K (Ambient K F) :=
  finalLabels (source t) (Labels.stage D hs hn t ht eB eA eC kind U U' G J H 0)

/-- The labels after the first two stages. -/
def afterSecond : GlobalCircuit.World B A C → Submodule K (Ambient K F) :=
  finalLabels (afterFirst D hs hn t ht eB eA eC kind U U' G J H)
    (Labels.stage D hs hn t ht eB eA eC kind U U' G J H 1)

omit [Fintype B] [Fintype A] [Fintype C] in
theorem afterFirst_le_profile (k : GlobalCircuit.World B A C) :
    afterFirst D hs hn t ht eB eA eC kind U U' G J H k ≤ profileInput D hs hn t ht 1 k := by
  rw [← profile_zero_one]
  exact stage_final_le D hs hn t ht eB eA eC kind U U' G J H 0 (source t)
    (source_le_profile D hs hn t ht) k

omit [Fintype B] [Fintype A] [Fintype C] in
theorem afterSecond_le_profile (k : GlobalCircuit.World B A C) :
    afterSecond D hs hn t ht eB eA eC kind U U' G J H k ≤ profileInput D hs hn t ht 2 k := by
  rw [← profile_one_two]
  exact stage_final_le D hs hn t ht eB eA eC kind U U' G J H 1 _
    (afterFirst_le_profile D hs hn t ht eB eA eC kind U U' G J H) k

omit [Fintype B] [Fintype A] [Fintype C] in
/-- The labeled mixer network respects its terminal output subspaces. -/
theorem program_final_le_sink (k : GlobalCircuit.World B A C) :
    finalLabels (source t) (Labels.program D hs hn t ht eB eA eC kind U U' G J H) k ≤
      sink D t k := by
  rw [Labels.program, finalLabels_append, finalLabels_append, ← profile_two_sink D hs hn t ht]
  exact stage_final_le D hs hn t ht eB eA eC kind U U' G J H 2 _
    (afterSecond_le_profile D hs hn t ht eB eA eC kind U U' G J H) k

include hJ hout hfit in
/-- Global loss: three stages of `n²` disjoint invocations, each losing at most
`c · dim F`. -/
theorem program_loss_le :
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V)
      (source (A := A) (C := C) t)
      (updates (Labels.program D hs hn t ht eB eA eC kind U U' G J H)) ≤
      3 * n ^ 2 * c * finrank K F := by
  have h₀ := stage_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit 0 (source t)
    (source_le_profile D hs hn t ht)
  have h₁ := stage_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit 1 _
    (afterFirst_le_profile D hs hn t ht eB eA eC kind U U' G J H)
  have h₂ := stage_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit 2 _
    (afterSecond_le_profile D hs hn t ht eB eA eC kind U U' G J H)
  simp only [Labels.program, updates_append, loss_append, RankTrace.finish_append,
    ← finalLabels_trace]
  dsimp [afterFirst, afterSecond] at h₁ h₂
  calc
    _ ≤ 3 * (n * n * (c * finrank K F)) := by omega
    _ = _ := by ring

omit [Fintype B] [Fintype A] [Fintype C] in
include hJ hout hfit in
theorem program_comparable :
    ∀ p ∈ RankTrace.edges (source (A := A) (C := C) t)
      (updates (Labels.program D hs hn t ht eB eA eC kind U U' G J H)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  have h₀ := stage_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit 0 (source t)
    (source_le_profile D hs hn t ht)
  have h₁ := stage_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit 1 _
    (afterFirst_le_profile D hs hn t ht eB eA eC kind U U' G J H)
  have h₂ := stage_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit 2 _
    (afterSecond_le_profile D hs hn t ht eB eA eC kind U U' G J H)
  dsimp [afterFirst, afterSecond] at h₁ h₂
  intro p hp
  simp only [Labels.program, updates_append, RankTrace.edges_append, RankTrace.finish_append,
    ← finalLabels_trace, List.mem_append, or_assoc] at hp
  rcases hp with hp | hp | hp
  · exact h₀ p hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem network_loss_eq (wires : List (GlobalCircuit.World B A C)) :
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V) (source t)
      (networkUpdates wires (sink D t) (Labels.program D hs hn t ht eB eA eC kind U U' G J H)) =
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V) (source t)
      (updates (Labels.program D hs hn t ht eB eA eC kind U U' G J H)) := by
  rw [networkUpdates, loss_append, loss_align]
  have hz : ∀ k : GlobalCircuit.World B A C,
      (fun V : Submodule K (Ambient K F) => finrank K V)
        (RankTrace.finish (source t)
          (updates (Labels.program D hs hn t ht eB eA eC kind U U' G J H)) k) -
        finrank K (sink D t k) = 0 := by
    intro k
    rw [← finalLabels_trace]
    exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono
      (program_final_le_sink D hs hn t ht eB eA eC kind U U' G J H k))
  simp [hz]

include hJ hout hfit in
theorem network_loss_le (wires : List (GlobalCircuit.World B A C)) :
    RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V) (source t)
      (networkUpdates wires (sink D t) (Labels.program D hs hn t ht eB eA eC kind U U' G J H)) ≤
      3 * n ^ 2 * c * finrank K F := by
  rw [network_loss_eq]
  exact program_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit

omit [Fintype B] [Fintype A] [Fintype C] in
include hJ hout hfit in
theorem network_comparable (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ RankTrace.edges (source t)
      (networkUpdates wires (sink D t) (Labels.program D hs hn t ht eB eA eC kind U U' G J H)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact program_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit p hp
  · apply edges_endpoints_rel (fun V W : Submodule K (Ambient K F) => V ≤ W ∨ W ≤ V)
      (fun _ => Or.inl le_rfl) _ _ wires _ p hp
    intro k _
    rw [← finalLabels_trace]
    exact Or.inl (program_final_le_sink D hs hn t ht eB eA eC kind U U' G J H k)

end Stage

section Projection
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [Fintype B] [Fintype A] [Fintype C]
  [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [Nontrivial R] [DecidableEq R]
  {n a c M : ℕ}
  (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (kind : Fin a → Kind n M) (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- The update list of all grouped gates and final sinks of the mixer network. -/
def trace (wires : List (GlobalCircuit.World B A C)) :=
  networkUpdates wires (sink D t) (Labels.program D hs hn t ht eB eA eC kind U U' G J H)

omit [Fintype B] [Fintype A] [Fintype C] [DecidableEq B] [DecidableEq A]
  [DecidableEq C] [Nontrivial R] in
/-- Every label of the trace is nondegenerate. -/
theorem trace_nondegenerate (hU : ∀ k, (D.restrict (U k)).Nondegenerate)
    (hU' : ∀ k, (D.restrict (U' k)).Nondegenerate) (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ trace D hs hn t ht eB eA eC kind U U' G J H wires,
      ((GlobalProjectionRank.cubeForm D).restrict p.2).Nondegenerate := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨v, hv, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact program_nondegenerate D hs hn t ht eB eA eC kind U U' G J H hU hU' v hv
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact GlobalProjectionRank.sink_nondegenerate D hs hn t ht i

/-- The sum of the projection-difference ranks of all trace edges. -/
noncomputable def rankSum (wires : List (GlobalCircuit.World B A C)) : ℕ :=
  ((RankTrace.edges (source t) (trace D hs hn t ht eB eA eC kind U U' G J H wires)).map
    (fun p => ProjectionTrace.edgeRank (GlobalProjectionRank.cubeForm D)
      (GlobalProjectionRank.cube_symm D hs) p.1 p.2)).sum

omit [Fintype B] [Fintype A] [Fintype C] [Nontrivial R] in
/-- Sink alignment ends at the prescribed output profile. -/
theorem trace_final (wires : List (GlobalCircuit.World B A C)) (hall : ∀ i, i ∈ wires) :
    RankTrace.finish (source t) (trace D hs hn t ht eB eA eC kind U U' G J H wires) = sink D t :=
  network_trace_final wires hall (source t) (sink D t) _

variable (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)
  (hU : ∀ k, (D.restrict (U k)).Nondegenerate) (hU' : ∀ k, (D.restrict (U' k)).Nondegenerate)
  (hfit : Fits D t eB kind U U')
include hJ hout hU hU' hfit

/-- Projection ranks balance the source and sink dimensions with twice the loss. -/
theorem rank_balance (wires : List (GlobalCircuit.World B A C)) (hall : ∀ i, i ∈ wires) :
    rankSum D hs hn t ht eB eA eC kind U U' G J H wires +
        RankTrace.total (fun V : Submodule K (Ambient K F) => finrank K V)
          (source (A := A) (C := C) t) =
      RankTrace.total (fun V : Submodule K (Ambient K F) => finrank K V)
          (sink (A := A) (C := C) D t) +
        2 * RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V)
          (source t) (trace D hs hn t ht eB eA eC kind U U' G J H wires) := by
  have hb := ProjectionTrace.rank_balance (GlobalProjectionRank.cubeForm D)
    (GlobalProjectionRank.cube_symm D hs) (source t)
    (trace D hs hn t ht eB eA eC kind U U' G J H wires)
    (GlobalProjectionRank.source_nondegenerate D t ht)
    (trace_nondegenerate D hs hn t ht eB eA eC kind U U' G J H hU hU' wires)
    (network_comparable D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit wires)
  rw [trace_final D hs hn t ht eB eA eC kind U U' G J H wires hall] at hb
  exact hb

/-- The rank balance with the terminal dimensions evaluated. -/
theorem rank_balance_dimensions (wires : List (GlobalCircuit.World B A C))
    (hall : ∀ i, i ∈ wires) :
    rankSum D hs hn t ht eB eA eC kind U U' G J H wires + Fintype.card B ^ 3 +
        Fintype.card B ^ 3 =
      Fintype.card (GlobalCircuit.World B A C) * (finrank K F) ^ 3 +
        2 * RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V)
          (source t) (trace D hs hn t ht eB eA eC kind U U' G J H wires) := by
  have hb := rank_balance D hs hn t ht eB eA eC kind U U' G J H hJ hout hU hU' hfit wires hall
  rw [NetworkBudget.source_total D t ht] at hb
  have he := NetworkBudget.sink_total (A := A) (C := C) D hn t ht
  omega

/-- The global projection-rank bound of the mixer network. -/
theorem rank_le_dimensions (wires : List (GlobalCircuit.World B A C)) (hall : ∀ i, i ∈ wires) :
    rankSum D hs hn t ht eB eA eC kind U U' G J H wires + 2 * Fintype.card B ^ 3 ≤
      Fintype.card (GlobalCircuit.World B A C) * (finrank K F) ^ 3 +
        6 * n ^ 2 * c * finrank K F := by
  have hb := rank_balance_dimensions D hs hn t ht eB eA eC kind U U' G J H hJ hout hU hU' hfit
    wires hall
  have hl := network_loss_le D hs hn t ht eB eA eC kind U U' G J H hJ hout hfit wires
  change RankTrace.loss (fun V : Submodule K (Ambient K F) => finrank K V)
    (source t) (trace D hs hn t ht eB eA eC kind U U' G J H wires) ≤ _ at hl
  have hm : 6 * n ^ 2 * c * finrank K F = 2 * (3 * n ^ 2 * c * finrank K F) := by ring
  rw [hm]
  omega

end Projection

end IntegerMultBounds.Networks.Mixer.Rank
