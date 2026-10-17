module

public import IntegerMultBounds.Networks.PairedBasePruning
public import IntegerMultBounds.Networks.PairedStarPresence
import IntegerMultBounds.Networks.PairedIndexedPruning
import IntegerMultBounds.Networks.PairedBlockCorrect
import IntegerMultBounds.Networks.PairedLevelTools

/-! Stars at the last vertex. The last coarse vertex of every level is the
fine vertex `48` alone, so each level's edge atom to it is the star from `48`
to the fine set of the other end: the groups, then dyadic blocks of width four,
eight and sixteen. Three base single exclusions add the unions of two of the
three sixteen-blocks. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedHubStars

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect PairedLevelBound
open PairedBasePruning PairedStarPresence PairedLevelTools

open PairedInitialGraph (Input)

/-- The star from vertex `48` to the leaves `X`. -/
def star48 (X : Finset ℕ) : Finset Input := X.image (fun x => (min 48 x, max 48 x))

/-- Every stored input pair is increasing. -/
def Ordered (nodes : List (Node Input)) : Prop := ∀ t ∈ nodes.map Node.support, ∀ z ∈ t, z.1 < z.2

theorem ordered_prefix {a b : List (Node Input)} (he : Extends a b) (h : Ordered b) : Ordered a :=
  fun t ht => h t (stored_extends he ht)

/-- The edge atom from `u` to the last vertex `w` of a typed level. -/
theorem atom_star (nodes : List (Node Input)) (w : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (wp : ℕ → Bool) (F : ℕ → Finset ℕ) (h : LevelInput nodes (w + 1) edges weights wp)
    (ht : Typed nodes (w + 1) edges weights F) (hlast : F w = {48}) (u : ℕ) (hu : u < w)
    (hF : ∀ x ∈ F u, x < 48) (ho : Ordered nodes) :
    refSupport nodes (lookup edges (u, w)) = star48 (F u) ∧ Stored nodes (star48 (F u)) := by
  obtain ⟨i, hi, hlt⟩ := edge_lookup nodes (w + 1) edges weights wp h u w (by omega) (by omega) (by omega)
  have hl : lookup edges (u, w) = some i := by
    simpa [edgeLookup, min_eq_left hu.le, max_eq_right hu.le] using hi
  have hs : refSupport nodes (lookup edges (u, w)) ∈ nodes.map Node.support := by
    rw [hl, refSupport_some _ _ hlt]; exact List.mem_map_of_mem (List.getElem_mem hlt)
  have hty := ht.edge u w hu (by omega)
  rw [hlast] at hty
  have heq : refSupport nodes (lookup edges (u, w)) = star48 (F u) := by
    ext z
    simp only [star48, Finset.mem_image]
    constructor
    · intro hz
      have hord := ho _ hs z hz
      rcases hty.cross z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Finset.mem_singleton] at h2
        have h48 := hF _ h1
        refine ⟨z.1, h1, ?_⟩
        apply Prod.ext <;> simp <;> omega
      · rw [Finset.mem_singleton] at h1
        have h48 := hF _ h2
        omega
    · rintro ⟨x, hx, rfl⟩
      have hx48 := hF x hx
      obtain ⟨z, hz, hzx⟩ := hty.cover x (Finset.mem_union_left _ hx)
      have hord := ho _ hs z hz
      rcases hty.cross z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Finset.mem_singleton] at h2
        have hz' : z = (min 48 x, max 48 x) := by
          apply Prod.ext <;> simp <;> omega
        rw [← hz']; exact hz
      · rw [Finset.mem_singleton] at h1
        have := hF _ h2
        omega
  exact ⟨heq, heq ▸ hs⟩

theorem block_extends (nodes : List (Node Input)) (n : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (wp : ℕ → Bool) (h : LevelInput nodes n edges weights wp) :
    Extends nodes (block nodes (List.range n) edges weights).nodes :=
  (PairedBlockCorrect.block_correct _ _ _ _ h.ready).extension

/-- All edge atoms of a level to its last vertex are stored in the block. -/
theorem level_atoms (nodes : List (Node Input)) (w : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (wp : ℕ → Bool) (F : ℕ → Finset ℕ) (h : LevelInput nodes (w + 1) edges weights wp)
    (ht : Typed nodes (w + 1) edges weights F) (hlast : F w = {48})
    (hF : ∀ u < w, ∀ x ∈ F u, x < 48)
    (ho : Ordered (block nodes (List.range (w + 1)) edges weights).nodes) :
    ∀ u < w, Stored (block nodes (List.range (w + 1)) edges weights).nodes (star48 (F u)) := by
  intro u hu
  have he := block_extends nodes (w + 1) edges weights wp h
  exact stored_extends he (atom_star nodes w edges weights wp F h ht hlast u hu (hF u hu)
    (ordered_prefix he ho)).2

/-- One level passes any monotone fact of its coarse level up. -/
theorem hub_level (m : ℕ) (hm : 2 ≤ m) (top : Bool) (F : ℕ → Finset ℕ) (Pc : List (Node Input) → Prop)
    (hmono : ∀ a b, Extends a b → Pc a → Pc b)
    (hc : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
      LevelInput nodes (m + 1) edges weights (fun i => decide (i < m)) →
      Typed nodes (m + 1) edges weights (coarseF m F) →
      Ordered (block nodes (List.range (m + 1)) edges weights).nodes →
      Pc (block nodes (List.range (m + 1)) edges weights).nodes)
    (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable)
    (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (ht : Typed nodes (2 * m + 1) edges weights F)
    (ho : Ordered (block nodes (List.range (2 * m + 1)) edges weights).nodes) :
    Pc (block nodes (List.range (2 * m + 1)) edges weights).nodes := by
  rw [block_large _ _ _ _ (by simp; omega)] at ho ⊢
  dsimp only at ho ⊢
  have hlen : (PairGrouping.groups (List.range (2 * m + 1))).length = m + 1 := oddGroups_length m
  rw [hlen] at ho ⊢
  exact hmono _ _ (reconstruct_extends _ _ _ _)
    (hc _ _ _ (coarse_input m top nodes edges weights h) (typed_coarse m top nodes edges weights F h ht)
      (ordered_prefix (reconstruct_extends _ _ _ _) ho))

/-! ### Fine sets along the chain -/

def F1 : ℕ → Finset ℕ := coarseF 24 F0
def F2 : ℕ → Finset ℕ := coarseF 12 F1
def F3 : ℕ → Finset ℕ := coarseF 6 F2

theorem F1_spec : ∀ k ≤ 24, ∀ x, x ∈ F1 k ↔ x < 49 ∧ x / 2 = k := by
  have h1 : ∀ k ≤ 24, ∀ x ∈ F1 k, x < 49 := by decide +kernel
  have h2 : ∀ x < 49, ∀ k ≤ 24, x ∈ F1 k ↔ x / 2 = k := by decide +kernel
  intro k hk x
  constructor
  · intro hx; have := h1 k hk x hx; exact ⟨this, (h2 x this k hk).mp hx⟩
  · rintro ⟨hx, he⟩; exact (h2 x hx k hk).mpr he

theorem F2_spec : ∀ k ≤ 12, ∀ x, x ∈ F2 k ↔ x < 49 ∧ x / 4 = k := by
  have h1 : ∀ k ≤ 12, ∀ x ∈ F2 k, x < 49 := by decide +kernel
  have h2 : ∀ x < 49, ∀ k ≤ 12, x ∈ F2 k ↔ x / 4 = k := by decide +kernel
  intro k hk x
  constructor
  · intro hx; have := h1 k hk x hx; exact ⟨this, (h2 x this k hk).mp hx⟩
  · rintro ⟨hx, he⟩; exact (h2 x hx k hk).mpr he

theorem F3_spec : ∀ k ≤ 6, ∀ x, x ∈ F3 k ↔ x < 49 ∧ x / 8 = k := by
  have h1 : ∀ k ≤ 6, ∀ x ∈ F3 k, x < 49 := by decide +kernel
  have h2 : ∀ x < 49, ∀ k ≤ 6, x ∈ F3 k ↔ x / 8 = k := by decide +kernel
  intro k hk x
  constructor
  · intro hx; have := h1 k hk x hx; exact ⟨this, (h2 x this k hk).mp hx⟩
  · rintro ⟨hx, he⟩; exact (h2 x hx k hk).mpr he

theorem F4_spec' : ∀ k ≤ 3, ∀ x, x ∈ F4 k ↔ x < 49 ∧ x / 16 = k := by
  intro k hk x
  constructor
  · intro hx
    have := F4_sub k (by omega) x hx
    exact ⟨this, (F4_spec x this k (by omega)).mp hx⟩
  · rintro ⟨hx, he⟩; exact (F4_spec x hx k (by omega)).mpr he

theorem last_eq (F : ℕ → Finset ℕ) (w s : ℕ) (hs : ∀ x, x ∈ F w ↔ x < 49 ∧ x / s = w)
    (hw : 48 / s = w) (h47 : 47 / s < w) : F w = {48} := by
  ext x
  rw [hs, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, he⟩
    by_contra hne
    have : x ≤ 47 := by omega
    have := Nat.div_le_div_right (c := s) this
    omega
  · rintro rfl; exact ⟨by omega, hw⟩

theorem low_of (F : ℕ → Finset ℕ) (w s : ℕ) (hs : ∀ u < w, ∀ x, x ∈ F u ↔ x < 49 ∧ x / s = u)
    (hw : 48 / s = w) : ∀ u < w, ∀ x ∈ F u, x < 48 := by
  intro u hu x hx
  obtain ⟨h1, h2⟩ := (hs u hu x).mp hx
  by_contra hc
  have : x = 48 := by omega
  subst this
  omega

/-! ### The base block -/

def P4 (out : List (Node Input)) : Prop :=
  (∀ u < 3, Stored out (star48 (F4 u))) ∧ Stored out (star48 (F4 0 ∪ F4 1)) ∧
    Stored out (star48 (F4 0 ∪ F4 2)) ∧ Stored out (star48 (F4 1 ∪ F4 2))

theorem P4_mono (a b : List (Node Input)) (he : Extends a b) (h : P4 a) : P4 b :=
  ⟨fun u hu => stored_extends he (h.1 u hu), stored_extends he h.2.1, stored_extends he h.2.2.1,
    stored_extends he h.2.2.2⟩

def A6 : Finset (Fin 9) := {2, 4}
def A7 : Finset (Fin 9) := {2, 5}
def A8 : Finset (Fin 9) := {4, 5}

theorem abstract_hub : ∀ A ∈ [A6, A7, A8],
    A ∈ (baseBlock PairedBaseBound.atoms (List.range 4) PairedBaseBound.edges
      PairedBaseBound.weights).nodes.map Node.support := by decide +kernel

theorem hub_4 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes (3 + 1) edges weights (fun i => decide (i < 3)) →
    Typed nodes (3 + 1) edges weights F4 →
    Ordered (block nodes (List.range (3 + 1)) edges weights).nodes →
    P4 (block nodes (List.range (3 + 1)) edges weights).nodes := by
  intro real er wr h ht ho
  have hlast := last_eq F4 3 16 (F4_spec' 3 (le_refl _)) (by decide) (by decide)
  have hlow := low_of F4 3 16 (fun u hu => F4_spec' u (by omega)) (by decide)
  have hatoms := level_atoms real 3 er wr _ F4 h ht hlast hlow ho
  have he := block_extends real (3 + 1) er wr _ h
  have hor := ordered_prefix he ho
  obtain ⟨-, -, e2, -, e4, e5⟩ := edgePair_val
  have g2 : g real er wr 2 = star48 (F4 0) := by
    rw [g_edge h 2 (by decide), e2]
    exact (atom_star real 3 er wr _ F4 h ht hlast 0 (by decide) (hlow 0 (by decide)) hor).1
  have g4 : g real er wr 4 = star48 (F4 1) := by
    rw [g_edge h 4 (by decide), e4]
    exact (atom_star real 3 er wr _ F4 h ht hlast 1 (by decide) (hlow 1 (by decide)) hor).1
  have g5 : g real er wr 5 = star48 (F4 2) := by
    rw [g_edge h 5 (by decide), e5]
    exact (atom_star real 3 er wr _ F4 h ht hlast 2 (by decide) (hlow 2 (by decide)) hor).1
  have hstep := PairedBaseBound.base_step real er wr h.edge_keys
    (by
      intro e he
      have hs := h.edge_present e he
      have hv := h.ready.refsValid e.2 (List.mem_append_left _ (List.mem_map_of_mem he))
      cases he2 : e.2 with
      | none => rw [he2] at hs; simp at hs
      | some i => rw [he2] at hv; exact ⟨i, rfl, hv⟩)
    h.weight_keys
    (by
      intro w hw hw3
      have hs := h.weight_present w hw
      have hv := h.ready.refsValid w.2 (List.mem_append_right _ (List.mem_map_of_mem hw))
      cases hw2 : w.2 with
      | none => rw [hw2] at hs; simp at hs; omega
      | some i => rw [hw2] at hv; exact ⟨i, rfl, hv⟩)
    (by
      intro w hw hw3
      have hs := h.weight_present w hw
      cases hw2 : w.2 with
      | none => rfl
      | some i => rw [hw2] at hs; simp at hs; omega)
  have hmem : ∀ A ∈ [A6, A7, A8], img real er wr A ∈
      (block real (List.range (3 + 1)) er wr).nodes.map Node.support := by
    intro A hA
    rw [block_small _ _ _ _ (by simp)]
    exact hstep.covers A (abstract_hub A hA)
  have i6 : img real er wr A6 = star48 (F4 0 ∪ F4 1) := by
    simp only [img, A6, Finset.biUnion_insert, Finset.singleton_biUnion, star48, Finset.image_union]
    rw [show ((2 : Fin 9) : ℕ) = 2 from rfl, show ((4 : Fin 9) : ℕ) = 4 from rfl, g2, g4]; rfl
  have i7 : img real er wr A7 = star48 (F4 0 ∪ F4 2) := by
    simp only [img, A7, Finset.biUnion_insert, Finset.singleton_biUnion, star48, Finset.image_union]
    rw [show ((2 : Fin 9) : ℕ) = 2 from rfl, show ((5 : Fin 9) : ℕ) = 5 from rfl, g2, g5]; rfl
  have i8 : img real er wr A8 = star48 (F4 1 ∪ F4 2) := by
    simp only [img, A8, Finset.biUnion_insert, Finset.singleton_biUnion, star48, Finset.image_union]
    rw [show ((4 : Fin 9) : ℕ) = 4 from rfl, show ((5 : Fin 9) : ℕ) = 5 from rfl, g4, g5]; rfl
  refine ⟨hatoms, ?_, ?_, ?_⟩
  · rw [← i6]; exact hmem A6 (by simp)
  · rw [← i7]; exact hmem A7 (by simp)
  · rw [← i8]; exact hmem A8 (by simp)

/-! ### The chain of levels -/

def P7 (out : List (Node Input)) : Prop := (∀ u < 6, Stored out (star48 (F3 u))) ∧ P4 out
def P13 (out : List (Node Input)) : Prop := (∀ u < 12, Stored out (star48 (F2 u))) ∧ P7 out
def P25 (out : List (Node Input)) : Prop := (∀ u < 24, Stored out (star48 (F1 u))) ∧ P13 out

theorem P7_mono (a b : List (Node Input)) (he : Extends a b) (h : P7 a) : P7 b :=
  ⟨fun u hu => stored_extends he (h.1 u hu), P4_mono a b he h.2⟩
theorem P13_mono (a b : List (Node Input)) (he : Extends a b) (h : P13 a) : P13 b :=
  ⟨fun u hu => stored_extends he (h.1 u hu), P7_mono a b he h.2⟩
theorem P25_mono (a b : List (Node Input)) (he : Extends a b) (h : P25 a) : P25 b :=
  ⟨fun u hu => stored_extends he (h.1 u hu), P13_mono a b he h.2⟩

theorem hub_7 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes (6 + 1) edges weights (fun i => decide (i < 6)) →
    Typed nodes (6 + 1) edges weights F3 →
    Ordered (block nodes (List.range (6 + 1)) edges weights).nodes →
    P7 (block nodes (List.range (6 + 1)) edges weights).nodes := by
  intro nodes edges weights h ht ho
  have hlast := last_eq F3 6 8 (F3_spec 6 (le_refl _)) (by decide) (by decide)
  have hlow := low_of F3 6 8 (fun u hu => F3_spec u (by omega)) (by decide)
  refine ⟨level_atoms nodes 6 edges weights _ F3 h ht hlast hlow ho, ?_⟩
  have h' : LevelInput nodes (2 * 3 + 1) edges weights (pattern 3 false) := by
    rw [PairedLevelBound.pattern_inner]; exact h
  exact hub_level 3 (by decide) false F3 P4 P4_mono (fun n e w h ht ho => hub_4 n e w h ht ho)
    nodes edges weights h' ht ho

theorem hub_13 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes (12 + 1) edges weights (fun i => decide (i < 12)) →
    Typed nodes (12 + 1) edges weights F2 →
    Ordered (block nodes (List.range (12 + 1)) edges weights).nodes →
    P13 (block nodes (List.range (12 + 1)) edges weights).nodes := by
  intro nodes edges weights h ht ho
  have hlast := last_eq F2 12 4 (F2_spec 12 (le_refl _)) (by decide) (by decide)
  have hlow := low_of F2 12 4 (fun u hu => F2_spec u (by omega)) (by decide)
  refine ⟨level_atoms nodes 12 edges weights _ F2 h ht hlast hlow ho, ?_⟩
  have h' : LevelInput nodes (2 * 6 + 1) edges weights (pattern 6 false) := by
    rw [PairedLevelBound.pattern_inner]; exact h
  exact hub_level 6 (by decide) false F2 P7 P7_mono (fun n e w h ht ho => hub_7 n e w h ht ho)
    nodes edges weights h' ht ho

theorem hub_25 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes (24 + 1) edges weights (fun i => decide (i < 24)) →
    Typed nodes (24 + 1) edges weights F1 →
    Ordered (block nodes (List.range (24 + 1)) edges weights).nodes →
    P25 (block nodes (List.range (24 + 1)) edges weights).nodes := by
  intro nodes edges weights h ht ho
  have hlast := last_eq F1 24 2 (F1_spec 24 (le_refl _)) (by decide) (by decide)
  have hlow := low_of F1 24 2 (fun u hu => F1_spec u (by omega)) (by decide)
  refine ⟨level_atoms nodes 24 edges weights _ F1 h ht hlast hlow ho, ?_⟩
  have h' : LevelInput nodes (2 * 12 + 1) edges weights (pattern 12 false) := by
    rw [PairedLevelBound.pattern_inner]; exact h
  exact hub_level 12 (by decide) false F1 P13 P13_mono (fun n e w h ht ho => hub_13 n e w h ht ho)
    nodes edges weights h' ht ho

/-- Every stored support of the final local circuit consists of increasing pairs. -/
theorem circuit_ordered : Ordered (PairedInitialGraph.circuit (List.range 49)).nodes := by
  intro t ht z hz
  rw [← PairedIndexedPruning.circuit_nodes_map, List.map_map] at ht
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp ht
  simp only [Function.comp_apply, PairedRename.node, Finset.mem_map] at hz
  obtain ⟨i, -, rfl⟩ := hz
  have hp := PairMask.pairAt_mem 49 i
  rw [PairedTopPruning.pairs_range_mem] at hp
  exact hp.1

theorem hub_range (n : ℕ) (hn : 2 * 24 + 1 = n) (ho : Ordered (PairedInitialGraph.circuit (List.range n)).nodes) :
    P25 (PairedInitialGraph.circuit (List.range n)).nodes := by
  subst hn
  have hin : LevelInput (PairedInitialGraph.nodes (List.range (2 * 24 + 1))) (2 * 24 + 1)
      (PairedInitialGraph.edges (List.range (2 * 24 + 1)))
      (PairedInitialGraph.weights (List.range (2 * 24 + 1))) (pattern 24 true) := by
    refine ⟨PairedInitialGraph.graphReady _ List.pairwise_lt_range, ?_, ?_, ?_, ?_⟩
    · simp [PairedInitialGraph.edges, List.map_map, Function.comp_def]
    · simp [PairedInitialGraph.weights, List.map_map, Function.comp_def]
    · intro e he
      simp only [PairedInitialGraph.edges, List.mem_map] at he
      obtain ⟨p, -, rfl⟩ := he
      rfl
    · intro w hw
      simp only [PairedInitialGraph.weights, List.mem_map] at hw
      obtain ⟨a, -, rfl⟩ := hw
      simp [pattern]
  exact hub_level 24 (by decide) true F0 P25 P25_mono (fun n e w h ht ho => hub_25 n e w h ht ho)
    _ _ _ hin typed_top ho

/-- All stars at vertex `48` that the duplicate count uses are stored. -/
theorem hub_49 : P25 (PairedInitialGraph.circuit (List.range 49)).nodes :=
  hub_range 49 rfl circuit_ordered

end IntegerMultBounds.Networks.PairedHubStars
