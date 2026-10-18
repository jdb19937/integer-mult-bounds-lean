module

public import IntegerMultBounds.Networks.PairedTopPruning
public import IntegerMultBounds.Networks.PairedBaseBound
import IntegerMultBounds.Networks.PairedLevelTools
import IntegerMultBounds.Networks.PairedSingleBudget
import IntegerMultBounds.Networks.DisjointPruningBudget
import IntegerMultBounds.Networks.DAGValueTransfer
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient

/-! Fine-vertex types of the recursive graph atoms. An edge atom between two
coarse vertices only joins their fine vertex sets and touches all of them; a
weight atom stays inside its fine set. These types survive every contraction,
so the base atoms are known well enough to show that five base sums fit in no
requested output. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedBasePruning

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect DAGAllocator
open PairedLevelTools PairedLevelBound PairedPartition PairedCoarseSupport SupportInterpretation
open PairedCoarseCorrect

open PairedInitialGraph (Input)

structure EdgeTyped (s : Finset Input) (A B : Finset ℕ) : Prop where
  cross : ∀ z ∈ s, (z.1 ∈ A ∧ z.2 ∈ B) ∨ (z.1 ∈ B ∧ z.2 ∈ A)
  cover : ∀ x ∈ A ∪ B, ∃ z ∈ s, z.1 = x ∨ z.2 = x

structure WeightTyped (s : Finset Input) (A : Finset ℕ) : Prop where
  inside : ∀ z ∈ s, z.1 ∈ A ∧ z.2 ∈ A
  cover : 2 ≤ A.card → ∀ x ∈ A, ∃ z ∈ s, z.1 = x ∨ z.2 = x

/-- Every atom of a level graph has its fine type. -/
structure Typed (nodes : List (Node Input)) (n : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (F : ℕ → Finset ℕ) : Prop where
  edge : ∀ u v, u < v → v < n → EdgeTyped (refSupport nodes (lookup edges (u, v))) (F u) (F v)
  weight : ∀ u, u < n → WeightTyped (refSupport nodes (lookup weights u)) (F u)
  nonempty : ∀ u, u < n → (F u).Nonempty

/-- Fine vertex sets of the coarse vertices. -/
def coarseF (m : ℕ) (F : ℕ → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (groupSet (List.range (2 * m + 1)) i).biUnion F

theorem groupSet_mem (m i a : ℕ) :
    a ∈ groupSet (List.range (2 * m + 1)) i ↔ a ≤ 2 * m ∧ a / 2 = i := by
  simp only [groupSet, List.mem_toFinset]
  exact PairedTopPruning.mem_groupAt m i a

theorem mem_coarseF (m : ℕ) (F : ℕ → Finset ℕ) (i x : ℕ) :
    x ∈ coarseF m F i ↔ ∃ a, a ≤ 2 * m ∧ a / 2 = i ∧ x ∈ F a := by
  simp only [coarseF, Finset.mem_biUnion, groupSet_mem]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, hx⟩; exact ⟨a, h1, h2, hx⟩
  · rintro ⟨a, h1, h2, hx⟩; exact ⟨a, ⟨h1, h2⟩, hx⟩

theorem mem_edge_cell (m i j : ℕ) (s : Source ℕ) :
    s ∈ cell (atomDomain (List.range (2 * m + 1))) (List.range (2 * m + 1)) (.edge i j) ↔
      ∃ u v, s = .edge u v ∧ u < v ∧ v ≤ 2 * m ∧
        ((u / 2 = i ∧ v / 2 = j) ∨ (v / 2 = i ∧ u / 2 = j)) := by
  cases s with
  | vertex a => simp [cell, bridge]
  | edge u v =>
    simp only [cell, bridge, Finset.mem_filter, edge_mem_domain, decide_eq_true_eq,
      groupSet_mem, PairedTopPruning.pairs_range_mem, Source.edge.injEq]
    constructor
    · rintro ⟨⟨huv, hv⟩, h⟩; exact ⟨u, v, ⟨rfl, rfl⟩, huv, by omega, by omega⟩
    · rintro ⟨u', v', ⟨rfl, rfl⟩, huv, hv, h⟩; exact ⟨⟨huv, by omega⟩, by omega⟩

theorem mem_vertex_cell (m i : ℕ) (s : Source ℕ) :
    s ∈ cell (atomDomain (List.range (2 * m + 1))) (List.range (2 * m + 1)) (.vertex i) ↔
      (∃ a, s = .vertex a ∧ a ≤ 2 * m ∧ a / 2 = i) ∨
        (∃ u v, s = .edge u v ∧ u < v ∧ v ≤ 2 * m ∧ u / 2 = i ∧ v / 2 = i) := by
  cases s with
  | vertex a =>
    simp only [cell, mem_confined, vertex_mem_domain, endpoints, Finset.singleton_subset_iff,
      groupSet_mem, List.mem_range, Source.vertex.injEq, reduceCtorEq, false_and, exists_false,
      or_false]
    constructor
    · rintro ⟨-, h⟩; exact ⟨a, rfl, h⟩
    · rintro ⟨a', rfl, h⟩; exact ⟨by omega, h⟩
  | edge u v =>
    simp only [cell, mem_confined, edge_mem_domain, endpoints, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, groupSet_mem, PairedTopPruning.pairs_range_mem,
      reduceCtorEq, false_and, exists_false, Source.edge.injEq, false_or]
    constructor
    · rintro ⟨⟨huv, hv⟩, h1, h2⟩; exact ⟨u, v, ⟨rfl, rfl⟩, huv, by omega, h1.2, h2.2⟩
    · rintro ⟨u', v', ⟨rfl, rfl⟩, huv, hv, h1, h2⟩; exact ⟨⟨huv, by omega⟩, ⟨by omega, h1⟩, ⟨hv, h2⟩⟩

/-- Fine types survive one contraction. -/
theorem typed_coarse (m : ℕ) (top : Bool) (nodes : List (Node Input)) (edges : EdgeTable)
    (weights : WeightTable) (F : ℕ → Finset ℕ)
    (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (ht : Typed nodes (2 * m + 1) edges weights F) :
    Typed (coarseWeights (coarseEdges nodes (oddGroups m) edges).1 (oddGroups m) edges weights).1
      (m + 1) (coarseEdges nodes (oddGroups m) edges).2
      (coarseWeights (coarseEdges nodes (oddGroups m) edges).1 (oddGroups m) edges weights).2
      (coarseF m F) := by
  have hs := coarse_cell_specs h.ready
  simp only [oddGroups_length] at hs
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hj
    have hp : (i, j) ∈ pairs (List.range (m + 1)) := by
      rw [PairedTopPruning.pairs_range_mem]; omega
    have hr := (tableSpec_lookup _ _ _ _ hs.2.2.1 (i, j) hp).2
    rw [hr]
    simp only [coarseSupport]
    constructor
    · intro z hz
      obtain ⟨s, hs', hz⟩ := (mem_interpret _ _ _).mp hz
      obtain ⟨u, v, rfl, huv, hv, hc⟩ := (mem_edge_cell m i j s).mp hs'
      simp only [atomSupport, atomRef_edge] at hz
      have hc' := (ht.edge u v huv (by omega)).cross z hz
      simp only [mem_coarseF]
      rcases hc with ⟨hu, hv'⟩ | ⟨hv', hu⟩ <;> rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨⟨u, by omega, hu, h1⟩, ⟨v, hv, hv', h2⟩⟩
      · exact Or.inr ⟨⟨v, hv, hv', h1⟩, ⟨u, by omega, hu, h2⟩⟩
      · exact Or.inr ⟨⟨u, by omega, hu, h1⟩, ⟨v, hv, hv', h2⟩⟩
      · exact Or.inl ⟨⟨v, hv, hv', h1⟩, ⟨u, by omega, hu, h2⟩⟩
    · intro x hx
      -- a fine vertex of one group, joined to some vertex of the other group
      obtain ⟨a, b, ha, hb, hab, hxa⟩ : ∃ a b, a ≤ 2 * m ∧ b ≤ 2 * m ∧
          ((a / 2 = i ∧ b / 2 = j) ∨ (a / 2 = j ∧ b / 2 = i)) ∧ x ∈ F a := by
        rcases Finset.mem_union.mp hx with hx | hx <;>
          obtain ⟨a, ha, hai, hxa⟩ := (mem_coarseF m F _ x).mp hx
        · exact ⟨a, if j < m then 2 * j else 2 * m, ha, by split_ifs <;> omega,
            Or.inl ⟨hai, by split_ifs <;> omega⟩, hxa⟩
        · exact ⟨a, 2 * i, ha, by omega, Or.inr ⟨hai, by omega⟩, hxa⟩
      have hne : a ≠ b := by omega
      let u := min a b
      let v := max a b
      have hmem : Source.edge u v ∈ cell (atomDomain (List.range (2 * m + 1)))
          (List.range (2 * m + 1)) (.edge i j) :=
        (mem_edge_cell m i j _).mpr ⟨u, v, rfl, by omega, by omega, by omega⟩
      obtain ⟨z, hz, hzx⟩ := (ht.edge u v (by omega) (by omega)).cover x (by
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · simp [u, v, min_eq_left hlt.le, max_eq_right hlt.le, hxa]
        · simp [u, v, min_eq_right hlt.le, max_eq_left hlt.le, hxa])
      exact ⟨z, (mem_interpret _ _ _).mpr ⟨_, hmem, by simpa [atomSupport] using hz⟩, hzx⟩
  · intro i hi
    have hr := (tableSpec_lookup _ _ _ _ hs.2.2.2 i (List.mem_range.mpr hi)).2
    rw [hr]
    simp only [coarseSupport]
    constructor
    · intro z hz
      obtain ⟨s, hs', hz⟩ := (mem_interpret _ _ _).mp hz
      simp only [mem_coarseF]
      rcases (mem_vertex_cell m i s).mp hs' with ⟨a, rfl, ha, hai⟩ | ⟨u, v, rfl, huv, hv, hu, hv'⟩
      · simp only [atomSupport, atomRef_vertex] at hz
        have hi' := (ht.weight a (by omega)).inside z hz
        exact ⟨⟨a, ha, hai, hi'.1⟩, ⟨a, ha, hai, hi'.2⟩⟩
      · simp only [atomSupport, atomRef_edge] at hz
        rcases (ht.edge u v huv (by omega)).cross z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨⟨u, by omega, hu, h1⟩, ⟨v, hv, hv', h2⟩⟩
        · exact ⟨⟨v, hv, hv', h1⟩, ⟨u, by omega, hu, h2⟩⟩
    · intro hcard x hx
      obtain ⟨a, ha, hai, hxa⟩ := (mem_coarseF m F i x).mp hx
      by_cases him : i < m
      · have hmem : Source.edge (2 * i) (2 * i + 1) ∈ cell (atomDomain (List.range (2 * m + 1)))
            (List.range (2 * m + 1)) (.vertex i) :=
          (mem_vertex_cell m i _).mpr (Or.inr ⟨2 * i, 2 * i + 1, rfl, by omega, by omega, by omega,
            by omega⟩)
        obtain ⟨z, hz, hzx⟩ := (ht.edge (2 * i) (2 * i + 1) (by omega) (by omega)).cover x (by
          rcases (show a = 2 * i ∨ a = 2 * i + 1 by omega) with rfl | rfl <;> simp [hxa])
        exact ⟨z, (mem_interpret _ _ _).mpr ⟨_, hmem, by simpa [atomSupport] using hz⟩, hzx⟩
      · have him' : i = m := by omega
        have ha' : a = 2 * m := by omega
        subst ha'
        have hF : coarseF m F i = F (2 * m) := by
          ext y
          rw [mem_coarseF]
          constructor
          · rintro ⟨b, hb, hbi, hy⟩
            have : b = 2 * m := by omega
            subst this; exact hy
          · intro hy; exact ⟨2 * m, le_refl _, by omega, hy⟩
        rw [hF] at hcard
        have hmem : Source.vertex (2 * m) ∈ cell (atomDomain (List.range (2 * m + 1)))
            (List.range (2 * m + 1)) (.vertex i) :=
          (mem_vertex_cell m i _).mpr (Or.inl ⟨2 * m, rfl, le_refl _, by omega⟩)
        obtain ⟨z, hz, hzx⟩ := (ht.weight (2 * m) (by omega)).cover hcard x hxa
        exact ⟨z, (mem_interpret _ _ _).mpr ⟨_, hmem, by simpa [atomSupport] using hz⟩, hzx⟩
  · intro i hi
    by_cases him : i < m
    · obtain ⟨y, hy⟩ := ht.nonempty (2 * i) (by omega)
      exact ⟨y, (mem_coarseF m F i y).mpr ⟨2 * i, by omega, by omega, hy⟩⟩
    · obtain ⟨y, hy⟩ := ht.nonempty (2 * m) (by omega)
      exact ⟨y, (mem_coarseF m F i y).mpr ⟨2 * m, le_refl _, by omega, hy⟩⟩

/-! ### Fine sets along the 49-vertex chain -/

def F0 : ℕ → Finset ℕ := fun v => {v}
def F4 : ℕ → Finset ℕ := coarseF 3 (coarseF 6 (coarseF 12 (coarseF 24 F0)))

/-- The base vertices: three blocks of sixteen and the last vertex alone. -/
theorem F4_spec : ∀ x < 49, ∀ k < 4, x ∈ F4 k ↔ x / 16 = k := by decide +kernel

theorem F4_sub : ∀ k < 4, ∀ x ∈ F4 k, x < 49 := by decide +kernel

/-- The top-level graph: each edge input joins its two endpoints. -/
theorem typed_top :
    Typed (PairedInitialGraph.nodes (List.range 49)) 49 (PairedInitialGraph.edges (List.range 49))
      (PairedInitialGraph.weights (List.range 49)) F0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv hv
    have hp : (u, v) ∈ pairs (List.range 49) := by rw [PairedTopPruning.pairs_range_mem]; omega
    rw [(tableSpec_lookup _ _ _ _ (PairedInitialGraph.edges_spec (List.range 49)) _ hp).2]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      simp [F0]
    · intro x hx
      simp only [F0, Finset.mem_union, Finset.mem_singleton] at hx
      exact ⟨(u, v), Finset.mem_singleton_self _, by simp only; omega⟩
  · intro u _
    rw [PairedTopPruning.weight_none 24 u]
    refine ⟨by simp [refSupport], ?_⟩
    intro hc
    simp [F0] at hc
  · intro u _
    simp [F0]

/-! ### The base atoms -/

section Base

variable (real : List (Node Input)) (er : EdgeTable) (wr : WeightTable)

/-- Endpoints of the `k`th base edge. -/
def edgePair (k : ℕ) : ℕ × ℕ := (pairs (List.range 4))[k]?.getD (0, 0)

theorem edgePair_spec : ∀ k < 6, (edgePair k).1 < (edgePair k).2 ∧ (edgePair k).2 < 4 ∧
    (pairs (List.range 4))[k]? = some (edgePair k) := by decide

/-- Support of base atom `k`. -/
def g (k : ℕ) : Finset Input := refSupport real (PairedBaseBound.atomRef er wr k)

variable {real er wr}

theorem atomRef_eq (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (k : ℕ) (hk : k < 9) :
    PairedBaseBound.atomRef er wr k = (graphRefs er wr)[k]'(by
      have h1 := congrArg List.length h.edge_keys
      have h2 := congrArg List.length h.weight_keys
      have h6 : (pairs (List.range 4)).length = 6 := by decide
      simp only [List.length_map, List.length_range] at h1 h2
      simp [graphRefs]; omega) := by
  have h1 := congrArg List.length h.edge_keys
  have h6 : (pairs (List.range 4)).length = 6 := by decide
  simp only [List.length_map] at h1
  simp only [PairedBaseBound.atomRef, graphRefs]
  split_ifs with hk6
  · rw [List.getElem_append_left (by simp; omega)]
    simp [List.getElem?_eq_getElem (show k < er.length by omega)]
  · rw [List.getElem_append_right (by simp; omega)]
    have h2 := congrArg List.length h.weight_keys
    simp only [List.length_map, List.length_range] at h2
    simp [List.getElem?_eq_getElem (show k - 6 < wr.length by omega), h1, h6]

theorem g_edge (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (k : ℕ) (hk : k < 6) :
    g real er wr k = refSupport real (lookup er (edgePair k)) := by
  obtain ⟨-, -, hp⟩ := edgePair_spec k hk
  have h1 := congrArg List.length h.edge_keys
  simp only [List.length_map] at h1
  have hkl : k < er.length := by
    have h6 : (pairs (List.range 4)).length = 6 := by decide
    omega
  have hkey : er[k].1 = edgePair k := by
    have hm := congrArg (fun l : List (ℕ × ℕ) => l[k]?) h.edge_keys
    simp only [List.getElem?_map, List.getElem?_eq_getElem hkl, Option.map_some, hp] at hm
    exact Option.some.inj hm
  have hl : lookup er (edgePair k) = er[k].2 := by
    rw [← hkey]
    apply lookup_entry _ (by rw [h.edge_keys]; exact pairs_nodup _ List.pairwise_lt_range)
    exact List.getElem_mem hkl
  simp only [g, PairedBaseBound.atomRef, hk, ↓reduceIte, List.getElem?_eq_getElem hkl,
    Option.map_some, Option.getD_some, hl]

theorem g_weight (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (u : ℕ) (hu : u < 3) :
    g real er wr (6 + u) = refSupport real (lookup wr u) := by
  have h2 := congrArg List.length h.weight_keys
  simp only [List.length_map, List.length_range] at h2
  have hul : u < wr.length := by omega
  have hkey : wr[u].1 = u := by
    have hm := congrArg (fun l : List ℕ => l[u]?) h.weight_keys
    simp only [List.getElem?_map, List.getElem?_eq_getElem hul, Option.map_some,
      List.getElem?_range (show u < 4 by omega)] at hm
    exact Option.some.inj hm
  have hl : lookup wr u = wr[u].2 := by
    conv_lhs => rw [← hkey]
    apply lookup_entry _ (by rw [h.weight_keys]; exact List.nodup_range)
    exact List.getElem_mem hul
  simp only [g, PairedBaseBound.atomRef, show ¬ 6 + u < 6 by omega, ↓reduceIte,
    show 6 + u - 6 = u by omega, List.getElem?_eq_getElem hul, Option.map_some,
    Option.getD_some, hl]

theorem F4_card (k : ℕ) (hk : k < 3) : 2 ≤ (F4 k).card := by
  interval_cases k <;> decide +kernel

theorem g_edge_typed (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (k : ℕ) (hk : k < 6) :
    EdgeTyped (g real er wr k) (F4 (edgePair k).1) (F4 (edgePair k).2) := by
  obtain ⟨h1, h2, -⟩ := edgePair_spec k hk
  rw [g_edge h k hk]
  exact ht.edge _ _ h1 h2

theorem g_weight_typed (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (u : ℕ) (hu : u < 3) : WeightTyped (g real er wr (6 + u)) (F4 u) := by
  rw [g_weight h u hu]
  exact ht.weight u (by omega)

theorem g_nonempty (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (k : ℕ) (hk : k < 9) : (g real er wr k).Nonempty := by
  by_cases hk6 : k < 6
  · obtain ⟨x, hx⟩ := ht.nonempty (edgePair k).1 (by have := edgePair_spec k hk6; omega)
    obtain ⟨z, hz, -⟩ := (g_edge_typed h ht k hk6).cover x (Finset.mem_union_left _ hx)
    exact ⟨z, hz⟩
  · obtain ⟨x, hx⟩ := ht.nonempty (k - 6) (by omega)
    have hw := g_weight_typed h ht (k - 6) (by omega)
    rw [show 6 + (k - 6) = k by omega] at hw
    obtain ⟨z, hz, -⟩ := hw.cover (F4_card _ (by omega)) x hx
    exact ⟨z, hz⟩

theorem g_disjoint (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (k k' : ℕ) (hk : k < 9)
    (hk' : k' < 9) (hne : k ≠ k') : Disjoint (g real er wr k) (g real er wr k') := by
  have hd := List.pairwise_iff_getElem.mp h.ready.disjoint
  have hlen : 9 ≤ (graphRefs er wr).length := by
    have h1 := congrArg List.length h.edge_keys
    have h2 := congrArg List.length h.weight_keys
    have h6 : (pairs (List.range 4)).length = 6 := by decide
    simp only [List.length_map, List.length_range] at h1 h2
    simp [graphRefs]; omega
  simp only [g, atomRef_eq h k hk, atomRef_eq h k' hk']
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hd k k' (by omega) (by omega) hlt
  · exact (hd k' k (by omega) (by omega) hlt).symm

theorem edgePair_val : edgePair 0 = (0, 1) ∧ edgePair 1 = (0, 2) ∧ edgePair 2 = (0, 3) ∧
    edgePair 3 = (1, 2) ∧ edgePair 4 = (1, 3) ∧ edgePair 5 = (2, 3) := by decide

theorem F4_iff (x k : ℕ) (hx : x < 49) (hk : k < 4) : x ∈ F4 k ↔ x / 16 = k := F4_spec x hx k hk

theorem edge_shape (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (k : ℕ) (hk : k < 6) (z : Input) (hz : z ∈ g real er wr k) :
    z.1 < 49 ∧ z.2 < 49 ∧ ((z.1 / 16 = (edgePair k).1 ∧ z.2 / 16 = (edgePair k).2) ∨
      (z.1 / 16 = (edgePair k).2 ∧ z.2 / 16 = (edgePair k).1)) := by
  obtain ⟨h1, h2, -⟩ := edgePair_spec k hk
  rcases (g_edge_typed h ht k hk).cross z hz with ⟨a, b⟩ | ⟨a, b⟩
  · have ha := F4_sub _ (by omega) _ a
    have hb := F4_sub _ (by omega) _ b
    exact ⟨ha, hb, Or.inl ⟨(F4_iff _ _ ha (by omega)).mp a, (F4_iff _ _ hb (by omega)).mp b⟩⟩
  · have ha := F4_sub _ (by omega) _ a
    have hb := F4_sub _ (by omega) _ b
    exact ⟨ha, hb, Or.inr ⟨(F4_iff _ _ ha (by omega)).mp a, (F4_iff _ _ hb (by omega)).mp b⟩⟩

theorem edge_cover (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (k : ℕ) (hk : k < 6) (x : ℕ) (hx : x < 49)
    (hxk : x / 16 = (edgePair k).1 ∨ x / 16 = (edgePair k).2) :
    ∃ z ∈ g real er wr k, z.1 = x ∨ z.2 = x := by
  obtain ⟨h1, h2, -⟩ := edgePair_spec k hk
  apply (g_edge_typed h ht k hk).cover x
  rcases hxk with hxk | hxk
  · exact Finset.mem_union_left _ ((F4_iff _ _ hx (by omega)).mpr hxk)
  · exact Finset.mem_union_right _ ((F4_iff _ _ hx (by omega)).mpr hxk)

theorem weight_shape (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (u : ℕ) (hu : u < 3) (z : Input) (hz : z ∈ g real er wr (6 + u)) :
    z.1 < 49 ∧ z.2 < 49 ∧ z.1 / 16 = u ∧ z.2 / 16 = u := by
  obtain ⟨a, b⟩ := (g_weight_typed h ht u hu).inside z hz
  have ha := F4_sub _ (by omega) _ a
  have hb := F4_sub _ (by omega) _ b
  exact ⟨ha, hb, (F4_iff _ _ ha (by omega)).mp a, (F4_iff _ _ hb (by omega)).mp b⟩

theorem weight_cover (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (u : ℕ) (hu : u < 3) (x : ℕ) (hx : x < 49) (hxu : x / 16 = u) :
    ∃ z ∈ g real er wr (6 + u), z.1 = x ∨ z.2 = x :=
  (g_weight_typed h ht u hu).cover (F4_card u hu) x ((F4_iff _ _ hx (by omega)).mpr hxu)

/-- Images of abstract atom sets. -/
def img (real : List (Node Input)) (er : EdgeTable) (wr : WeightTable) (A : Finset (Fin 9)) :
    Finset Input := A.biUnion (fun k => g real er wr k.val)

theorem img_inj (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (A B : Finset (Fin 9)) (he : img real er wr A = img real er wr B) : A = B := by
  have key : ∀ A B : Finset (Fin 9), img real er wr A = img real er wr B → A ⊆ B := by
    intro A B he k hk
    obtain ⟨z, hz⟩ := g_nonempty h ht k.val k.isLt
    have hzA : z ∈ img real er wr A := Finset.mem_biUnion.mpr ⟨k, hk, hz⟩
    rw [he] at hzA
    obtain ⟨k', hk', hz'⟩ := Finset.mem_biUnion.mp hzA
    by_contra hkB
    have hne : k.val ≠ k'.val := fun e => hkB (Fin.ext e ▸ hk')
    exact Finset.disjoint_left.mp (g_disjoint h k.val k'.val k.isLt k'.isLt hne) hz hz'
  exact Finset.Subset.antisymm (key A B he) (key B A he.symm)

/-- The pair-exclusion output support for the pair `p`. -/
def R (p : ℕ × ℕ) : Finset Input :=
  (pairs (List.range 49)).toFinset.filter (fun q => q.1 ∉ [p.1, p.2] ∧ q.2 ∉ [p.1, p.2])

/-- A support that is a dead addition distinct from every other credited one. -/
structure Good (s : Finset Input) : Prop where
  two : 2 ≤ s.card
  obstructed : ∀ p ∈ pairs (List.range 49), ¬ s ⊆ R p
  not_single : ∀ b < 49, s ≠ PairedInitialGraph.singleSupport (List.range 49) b
  not_strip : ∀ a < 48, s ≠ PairedTopPruning.S 24 (a / 2, a)

theorem obstructed_of_cover (s : Finset Input) (hcov : ∀ x < 48, ∃ z ∈ s, z.1 = x ∨ z.2 = x) :
    ∀ p ∈ pairs (List.range 49), ¬ s ⊆ R p := by
  intro p hp hsub
  have hp' := (PairedTopPruning.pairs_range_mem 49 p.1 p.2).mp hp
  obtain ⟨z, hz, hzx⟩ := hcov p.1 (by omega)
  have hm := Finset.mem_filter.mp (hsub hz)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  omega

theorem single_mem (b y z : ℕ) (hyz : y < z) (hz : z < 49) (hy : y ≠ b) (hzb : z ≠ b) :
    (y, z) ∈ PairedInitialGraph.singleSupport (List.range 49) b := by
  simp only [PairedInitialGraph.singleSupport, Finset.mem_filter, List.mem_toFinset,
    PairedTopPruning.pairs_range_mem]
  omega

theorem not_single_of_touch (s : Finset Input) (b : ℕ) (hz : ∃ z ∈ s, z.1 = b ∨ z.2 = b) :
    s ≠ PairedInitialGraph.singleSupport (List.range 49) b := by
  intro he
  obtain ⟨z, hzs, hzb⟩ := hz
  rw [he] at hzs
  simp only [PairedInitialGraph.singleSupport, Finset.mem_filter] at hzs
  omega

theorem strip_touch48 (a : ℕ) (ha : a < 48) : ∃ z ∈ PairedTopPruning.S 24 (a / 2, a), z.2 = 48 := by
  have hp := PairedTopPruning.partner_facts (a / 2) a (by omega)
  refine ⟨_, (PairedTopPruning.mem_strip 24 (a / 2) a (by omega) (by omega) _).mpr
    ⟨48, by omega, by omega, rfl⟩, ?_⟩
  simp only
  omega

theorem strip_avoid (a : ℕ) (ha : a < 48) :
    ∀ z ∈ PairedTopPruning.S 24 (a / 2, a), z.1 ≠ a ∧ z.2 ≠ a := by
  intro z hz
  obtain ⟨x, -, hx, rfl⟩ := (PairedTopPruning.mem_strip 24 (a / 2) a (by omega) (by omega) _).mp hz
  have hp := PairedTopPruning.partner_facts (a / 2) a (by omega)
  simp only
  omega

theorem good_low (s : Finset Input) (htwo : 2 ≤ s.card) (hcov : ∀ x < 48, ∃ z ∈ s, z.1 = x ∨ z.2 = x)
    (hlow : ∀ z ∈ s, z.1 < 48 ∧ z.2 < 48) (y z : ℕ) (hyz : y < z) (hz : z < 48) (hm : (y, z) ∉ s) :
    Good s := by
  refine ⟨htwo, obstructed_of_cover s hcov, ?_, ?_⟩
  · intro b hb he
    by_cases h48 : b = 48
    · subst h48
      exact hm (he ▸ single_mem 48 y z hyz (by omega) (by omega) (by omega))
    · let c := if b = 0 then 1 else 0
      have hc := single_mem b c 48 (by simp only [c]; split_ifs <;> omega) (by omega)
        (by simp only [c]; split_ifs <;> omega) (by omega)
      rw [← he] at hc
      have := (hlow _ hc).2
      simp at this
  · intro a ha he
    obtain ⟨w, hw, hw48⟩ := strip_touch48 a ha
    rw [← he] at hw
    have := (hlow w hw).2
    omega

theorem good_star (s : Finset Input) (htwo : 2 ≤ s.card) (hcov : ∀ x < 48, ∃ z ∈ s, z.1 = x ∨ z.2 = x)
    (hstar : ∀ z ∈ s, z.1 = 48 ∨ z.2 = 48) : Good s := by
  refine ⟨htwo, obstructed_of_cover s hcov, ?_, ?_⟩
  · intro b hb he
    by_cases hb1 : b ≤ 1
    · have hc := single_mem b 2 3 (by omega) (by omega) (by omega) (by omega)
      rw [← he] at hc
      have := hstar _ hc
      simp at this
    · have hc := single_mem b 0 1 (by omega) (by omega) (by omega) (by omega)
      rw [← he] at hc
      have := hstar _ hc
      simp at this
  · intro a ha he
    obtain ⟨z, hz, hza⟩ := hcov a ha
    rw [he] at hz
    have := strip_avoid a ha z hz
    omega

theorem good_full (s : Finset Input) (htwo : 2 ≤ s.card) (hcov : ∀ x < 48, ∃ z ∈ s, z.1 = x ∨ z.2 = x)
    (h48 : ∃ z ∈ s, z.1 = 48 ∨ z.2 = 48) : Good s := by
  refine ⟨htwo, obstructed_of_cover s hcov, ?_, ?_⟩
  · intro b hb
    apply not_single_of_touch
    by_cases h : b < 48
    · exact hcov b h
    · have : b = 48 := by omega
      subst this; exact h48
  · intro a ha he
    obtain ⟨z, hz, hza⟩ := hcov a ha
    rw [he] at hz
    have := strip_avoid a ha z hz
    omega

theorem mem_img (A : Finset (Fin 9)) (k : Fin 9) (hk : k ∈ A) (z : Input)
    (hz : z ∈ g real er wr k.val) : z ∈ img real er wr A :=
  Finset.mem_biUnion.mpr ⟨k, hk, hz⟩

theorem two_of_atoms (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
    (A : Finset (Fin 9)) (k k' : Fin 9) (hk : k ∈ A) (hk' : k' ∈ A) (hne : k.val ≠ k'.val) :
    2 ≤ (img real er wr A).card := by
  obtain ⟨z, hz⟩ := g_nonempty h ht k.val k.isLt
  obtain ⟨z', hz'⟩ := g_nonempty h ht k'.val k'.isLt
  apply Finset.one_lt_card.mpr
  refine ⟨z, mem_img A k hk z hz, z', mem_img A k' hk' z' hz', ?_⟩
  rintro rfl
  exact Finset.disjoint_left.mp (g_disjoint h k.val k'.val k.isLt k'.isLt hne) hz hz'

def A1 : Finset (Fin 9) := {1, 3}
def A2 : Finset (Fin 9) := {0, 1, 3}
def A3 : Finset (Fin 9) := {6, 7, 8}
def A4 : Finset (Fin 9) := {2, 4, 5}
def A5 : Finset (Fin 9) := Finset.univ

section Five

variable (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4)
include h ht

theorem cover_edge (k : ℕ) (hk : k < 6) (x : ℕ) (hx : x < 49)
    (hxk : x / 16 = (edgePair k).1 ∨ x / 16 = (edgePair k).2) :
    ∃ z ∈ g real er wr k, z.1 = x ∨ z.2 = x := edge_cover h ht k hk x hx hxk

theorem good1 : Good (img real er wr A1) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := edgePair_val
  apply good_low _ (two_of_atoms h ht A1 1 3 (by decide) (by decide) (by decide))
  · intro x hx
    have hv : x / 16 < 3 := by omega
    by_cases h1 : x / 16 = 1
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 3 (by omega) x (by omega) (by rw [e3]; omega)
      exact ⟨z, mem_img A1 3 (by decide) z hz, hzx⟩
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 1 (by omega) x (by omega) (by rw [e1]; omega)
      exact ⟨z, mem_img A1 1 (by decide) z hz, hzx⟩
  · intro z hz
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
    have hk' : k.val = 1 ∨ k.val = 3 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3⟩ := edge_shape h ht _ (by omega) z hz <;> simp only [e1, e3] at h3 <;> omega
  · exact (by omega : 0 < 16)
  · exact (by omega : 16 < 48)
  · intro hm
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hm
    have hk' : k.val = 1 ∨ k.val = 3 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3⟩ := edge_shape h ht _ (by omega) _ hz <;> simp only [e1, e3] at h3 <;> omega

theorem good2 : Good (img real er wr A2) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := edgePair_val
  apply good_low _ (two_of_atoms h ht A2 1 3 (by decide) (by decide) (by decide))
  · intro x hx
    by_cases h1 : x / 16 = 1
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 3 (by omega) x (by omega) (by rw [e3]; omega)
      exact ⟨z, mem_img A2 3 (by decide) z hz, hzx⟩
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 1 (by omega) x (by omega) (by rw [e1]; omega)
      exact ⟨z, mem_img A2 1 (by decide) z hz, hzx⟩
  · intro z hz
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
    have hk' : k.val = 0 ∨ k.val = 1 ∨ k.val = 3 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3⟩ := edge_shape h ht _ (by omega) z hz <;> simp only [e0, e1, e3] at h3 <;> omega
  · exact (by omega : 0 < 1)
  · exact (by omega : 1 < 48)
  · intro hm
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hm
    have hk' : k.val = 0 ∨ k.val = 1 ∨ k.val = 3 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3⟩ := edge_shape h ht _ (by omega) _ hz <;> simp only [e0, e1, e3] at h3 <;> omega

theorem good3 : Good (img real er wr A3) := by
  apply good_low _ (two_of_atoms h ht A3 6 7 (by decide) (by decide) (by decide))
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := weight_cover h ht (x / 16) (by omega) x (by omega) rfl
    have hmem : (⟨6 + x / 16, by omega⟩ : Fin 9) ∈ A3 := by
      simp only [A3, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    exact ⟨z, mem_img A3 _ hmem z hz, hzx⟩
  · intro z hz
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
    have hk' : k.val = 6 + 0 ∨ k.val = 6 + 1 ∨ k.val = 6 + 2 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3, h4⟩ := weight_shape h ht _ (by omega) z hz <;> omega
  · exact (by omega : 0 < 16)
  · exact (by omega : 16 < 48)
  · intro hm
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hm
    have hk' : k.val = 6 + 0 ∨ k.val = 6 + 1 ∨ k.val = 6 + 2 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3, h4⟩ := weight_shape h ht _ (by omega) _ hz <;> simp at h3 h4

theorem good4 : Good (img real er wr A4) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := edgePair_val
  apply good_star _ (two_of_atoms h ht A4 2 4 (by decide) (by decide) (by decide))
  · intro x hx
    by_cases h0 : x / 16 = 0
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 2 (by omega) x (by omega) (by rw [e2]; omega)
      exact ⟨z, mem_img A4 2 (by decide) z hz, hzx⟩
    · by_cases h1 : x / 16 = 1
      · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 4 (by omega) x (by omega) (by rw [e4]; omega)
        exact ⟨z, mem_img A4 4 (by decide) z hz, hzx⟩
      · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 5 (by omega) x (by omega) (by rw [e5]; omega)
        exact ⟨z, mem_img A4 5 (by decide) z hz, hzx⟩
  · intro z hz
    obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
    have hk' : k.val = 2 ∨ k.val = 4 ∨ k.val = 5 := by fin_cases hk <;> simp
    rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hz <;>
      obtain ⟨h1, h2, h3⟩ := edge_shape h ht _ (by omega) z hz <;> simp only [e2, e4, e5] at h3 <;> omega

theorem good5 : Good (img real er wr A5) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := edgePair_val
  apply good_full _ (two_of_atoms h ht A5 0 1 (by decide) (by decide) (by decide))
  · intro x hx
    by_cases h2 : x / 16 = 2
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 1 (by omega) x (by omega) (by rw [e1]; omega)
      exact ⟨z, mem_img A5 1 (by decide) z hz, hzx⟩
    · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 0 (by omega) x (by omega) (by rw [e0]; omega)
      exact ⟨z, mem_img A5 0 (by decide) z hz, hzx⟩
  · obtain ⟨z, hz, hzx⟩ := edge_cover h ht 2 (by omega) 48 (by omega) (by rw [e2]; decide)
    exact ⟨z, mem_img A5 2 (by decide) z hz, hzx⟩

end Five

end Base

/-! ### Five dead base sums survive to the top -/

/-- Five stored supports, each a dead addition distinct from the other credits. -/
def DeadSupports (nodes : List (Node Input)) : Prop :=
  ∃ T : Finset (Finset Input), T.card = 5 ∧ ∀ s ∈ T, s ∈ nodes.map Node.support ∧ Good s

theorem deadSupports_extends {nodes larger : List (Node Input)} (he : Extends nodes larger)
    (h : DeadSupports nodes) : DeadSupports larger := by
  obtain ⟨T, hT, hs⟩ := h
  exact ⟨T, hT, fun s hm => ⟨PairedLevelBound.mem_supports_extends he (hs s hm).1, (hs s hm).2⟩⟩

theorem abstract_mem : ∀ A ∈ [A1, A2, A3, A4, A5],
    A ∈ (baseBlock PairedBaseBound.atoms (List.range 4) PairedBaseBound.edges
      PairedBaseBound.weights).nodes.map Node.support := by decide +kernel

theorem five_distinct : ({A1, A2, A3, A4, A5} : Finset (Finset (Fin 9))).card = 5 := by decide

theorem base_dead (real : List (Node Input)) (er : EdgeTable) (wr : WeightTable)
    (h : LevelInput real 4 er wr (fun i => decide (i < 3))) (ht : Typed real 4 er wr F4) :
    DeadSupports (block real (List.range 4) er wr).nodes := by
  rw [block_small _ _ _ _ (by simp)]
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
  have hmem : ∀ A ∈ [A1, A2, A3, A4, A5], img real er wr A ∈
      (baseBlock real (List.range 4) er wr).nodes.map Node.support :=
    fun A hA => hstep.covers A (abstract_mem A hA)
  refine ⟨({A1, A2, A3, A4, A5} : Finset (Finset (Fin 9))).image (img real er wr), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (fun A _ B _ he => img_inj h ht A B he), five_distinct]
  · intro t ht'
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hmem _ (by simp), good1 h ht⟩
    · exact ⟨hmem _ (by simp), good2 h ht⟩
    · exact ⟨hmem _ (by simp), good3 h ht⟩
    · exact ⟨hmem _ (by simp), good4 h ht⟩
    · exact ⟨hmem _ (by simp), good5 h ht⟩

theorem reconstruct_extends (groups : List (List ℕ)) (edges : EdgeTable) (weights : WeightTable)
    (coarse : BlockResult Input) :
    Extends coarse.nodes (reconstruct groups edges weights coarse).nodes := by
  unfold reconstruct
  exact extends_trans (mapBuild_extends _ (fun ns ia => buildStrip_extends _ _ _ _ _) _ _)
    (extends_trans (buildSingles_extends _ _ _ _) (buildCrossPairs_extends _ _ _ _ _))

/-- One level passes the coarse level's dead supports up. -/
theorem dead_level (m : ℕ) (hm : 2 ≤ m) (top : Bool) (F : ℕ → Finset ℕ)
    (hc : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
      LevelInput nodes (m + 1) edges weights (fun i => decide (i < m)) →
      Typed nodes (m + 1) edges weights (coarseF m F) →
      DeadSupports (block nodes (List.range (m + 1)) edges weights).nodes)
    (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable)
    (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (ht : Typed nodes (2 * m + 1) edges weights F) :
    DeadSupports (block nodes (List.range (2 * m + 1)) edges weights).nodes := by
  rw [block_large _ _ _ _ (by simp; omega)]
  dsimp only
  have hlen : (PairGrouping.groups (List.range (2 * m + 1))).length = m + 1 := oddGroups_length m
  rw [hlen]
  exact deadSupports_extends (reconstruct_extends _ _ _ _)
    (hc _ _ _ (coarse_input m top nodes edges weights h) (typed_coarse m top nodes edges weights F h ht))

theorem dead_7 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes 7 edges weights (fun i => decide (i < 6)) →
    Typed nodes 7 edges weights (coarseF 6 (coarseF 12 (coarseF 24 F0))) →
    DeadSupports (block nodes (List.range 7) edges weights).nodes := by
  intro nodes edges weights h ht
  have h' : LevelInput nodes (2 * 3 + 1) edges weights (pattern 3 false) := by
    rw [PairedLevelBound.pattern_inner]; exact h
  exact dead_level 3 (by norm_num) false _ (fun n e w h' ht' => base_dead n e w h' ht') nodes edges weights h' ht

theorem dead_13 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes 13 edges weights (fun i => decide (i < 12)) →
    Typed nodes 13 edges weights (coarseF 12 (coarseF 24 F0)) →
    DeadSupports (block nodes (List.range 13) edges weights).nodes := by
  intro nodes edges weights h ht
  have h' : LevelInput nodes (2 * 6 + 1) edges weights (pattern 6 false) := by
    rw [PairedLevelBound.pattern_inner]; exact h
  exact dead_level 6 (by norm_num) false _ dead_7 nodes edges weights h' ht

theorem dead_25 : ∀ (nodes : List (Node Input)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes 25 edges weights (fun i => decide (i < 24)) →
    Typed nodes 25 edges weights (coarseF 24 F0) →
    DeadSupports (block nodes (List.range 25) edges weights).nodes := by
  intro nodes edges weights h ht
  have h' : LevelInput nodes (2 * 12 + 1) edges weights (pattern 12 false) := by
    rw [PairedLevelBound.pattern_inner]; exact h
  exact dead_level 12 (by norm_num) false _ dead_13 nodes edges weights h' ht

theorem dead_range (n : ℕ) (hn : 2 * 24 + 1 = n) :
    DeadSupports (PairedInitialGraph.circuit (List.range n)).nodes := by
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
  exact dead_level 24 (by norm_num) true F0 dead_25 _ _ _ hin typed_top

theorem dead_49 : DeadSupports (PairedInitialGraph.circuit (List.range 49)).nodes :=
  dead_range 49 rfl

/-! ### The sharp live count -/

open DAGSupportTrace in
/-- Five distinct stored supports give five distinct node identifiers. -/
theorem dead_finset (N : List (Node Input)) (h : DeadSupports N) :
    ∃ D : Finset ℕ, D.card = 5 ∧ ∀ k ∈ D, ∃ hk : k < N.length, Good N[k].support := by
  classical
  obtain ⟨T, hT, hTs⟩ := h
  have hex : ∀ s ∈ T, ∃ k, ∃ hk : k < N.length, N[k].support = s := by
    intro s hs
    obtain ⟨node, hn, rfl⟩ := List.mem_map.mp (hTs s hs).1
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hn
    exact ⟨k, hk, rfl⟩
  let idx : Finset Input → ℕ := fun s => if hs : s ∈ T then Classical.choose (hex s hs) else 0
  have hidx : ∀ s ∈ T, ∃ hk : idx s < N.length, N[idx s].support = s := by
    intro s hs
    simp only [idx, dite_eq_left_of_eq_true (eq_true hs)]
    exact Classical.choose_spec (hex s hs)
  have key : ∀ i j (hi : i < N.length) (hj : j < N.length), i = j → N[i].support = N[j].support := by
    intro i j hi hj he; subst he; rfl
  refine ⟨T.image idx, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hT]
    intro s hs s' hs' he
    obtain ⟨h1, e1⟩ := hidx s hs
    obtain ⟨h2, e2⟩ := hidx s' hs'
    rw [← e1, ← e2]
    exact key _ _ h1 h2 he
  · intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨h1, e1⟩ := hidx s hs
    refine ⟨h1, ?_⟩
    rw [e1]
    exact (hTs s hs).2


open DAGSupportTrace in
/-- The top strip support, stated for a symbolic half-size so that no
concrete circuit is ever compared by unfolding. -/
theorem strip_support (m : ℕ) (hm : 2 ≤ m) (a : ℕ) (ha : a < 2 * m) :
    nodeSupport (PairedInitialGraph.circuit (List.range (2 * m + 1))).nodes
      (PairedTopPruning.totalIndex m a) = PairedTopPruning.S m (a / 2, a) :=
  (PairedTopPruning.total_index_spec m a hm ha).2.2

open DisjointPruning DAGAdditionIds PairedInitialGraph in
theorem dead_not_marked (m : ℕ) (hm : 2 ≤ m) : ∀ k ∈ PairedTopPruning.dead m,
    k ∉ mark (circuit (List.range (2 * m + 1))).nodes (outputRefs (List.range (2 * m + 1))).toFinset :=
  PairedTopPruning.dead_not_marked m hm

open DAGAdditionIds in
theorem dead_additions (m : ℕ) (hm : 2 ≤ m) :
    PairedTopPruning.dead m ⊆ additionIds (PairedInitialGraph.circuit (List.range (2 * m + 1))).nodes :=
  PairedTopPruning.dead_additions m hm

theorem dead_disjoint (m : ℕ) (hm : 2 ≤ m) :
    Disjoint (PairedInitialGraph.singleRefs (List.range (2 * m + 1))) (PairedTopPruning.dead m) :=
  PairedTopPruning.dead_disjoint m hm

open DAGSupportTrace in
theorem not_strip_of_good (N : List (Node Input)) (k : ℕ) (hb : k < N.length)
    (hg : Good N[k].support) (a : ℕ) (ha : a < 48)
    (hsup : nodeSupport N k = PairedTopPruning.S 24 (a / 2, a)) : False := by
  rw [nodeSupport_get N k hb] at hsup
  exact hg.not_strip a ha hsup

theorem range_toFinset_card (n : ℕ) : (List.range n).toFinset.card = n := by
  rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]

open DAGAdditionIds in
/-- A good support has at least two inputs, so its node is an addition. -/
theorem good_additionId (N : List (Node Input)) (hv : Valid N) (k : ℕ) (hb : k < N.length)
    (hg : Good N[k].support) : k ∈ additionIds N := by
  have hnode := DAGValueTransfer.validFrom_get [] N hv k hb
  cases hkind : N[k].kind with
  | input p =>
    have heq : N[k].support = {p} := by simpa only [Node.Valid, hkind] using hnode
    have hc := hg.two
    rw [heq, Finset.card_singleton] at hc
    omega
  | add l r => exact (mem_additionIds _ _).mpr ⟨_, List.getElem?_eq_getElem hb, l, r, hkind⟩

open DisjointPruning DAGSupportTrace DAGAdditionIds PairedInitialGraph in
theorem live_le_range (n : ℕ) (hn : 2 * 24 + 1 = n) :
    additionCountFrom 0 (mark (PairedInitialGraph.circuit (List.range n)).nodes
        (outputRefs (List.range n)).toFinset) (PairedInitialGraph.circuit (List.range n)).nodes +
      (n + 48 + 5) ≤ additionCount (PairedInitialGraph.circuit (List.range n)).nodes := by
  have hdead := dead_range n hn
  subst hn
  obtain ⟨D, hDcard, hgood⟩ := dead_finset _ hdead
  let N := (PairedInitialGraph.circuit (List.range (2 * 24 + 1))).nodes
  have hv : Valid N := (PairedInitialGraph.circuit_correct _ List.pairwise_lt_range).valid
  have hDadd : D ⊆ additionIds N := fun k hk =>
    good_additionId N hv k (hgood k hk).1 (hgood k hk).2
  have hDdead : ∀ k ∈ D, k ∉ mark N (outputRefs (List.range (2 * 24 + 1))).toFinset := by
    intro k hk
    obtain ⟨hb, hg⟩ := hgood k hk
    apply not_marked_of_support _ hv
    intro r hr
    obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hr)
    have hpair := (circuit_pair_support (List.range (2 * 24 + 1)) List.pairwise_lt_range p hp).2
    rw [he] at hpair
    change nodeSupport N r = _ at hpair
    rw [nodeSupport_get N k hb, hpair]
    exact hg.obstructed p hp
  have hDsingle : Disjoint (singleRefs (List.range (2 * 24 + 1))) D := by
    apply Finset.disjoint_left.mpr
    intro k hs hk
    obtain ⟨hb, hg⟩ := hgood k hk
    obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hs)
    have hspec := (circuit_single_support (List.range (2 * 24 + 1)) List.pairwise_lt_range c hc).2
    rw [he, refSupport_some _ _ hb] at hspec
    exact hg.not_single c (List.mem_range.mp hc) hspec
  have hDstrip : Disjoint (PairedTopPruning.dead 24) D := by
    apply Finset.disjoint_left.mpr
    intro k hs hk
    obtain ⟨hb, hg⟩ := hgood k hk
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hs
    have ha' := Finset.mem_range.mp ha
    have hsup := strip_support 24 (by norm_num) a ha'
    rw [he] at hsup
    exact not_strip_of_good _ k hb hg a (by omega) hsup
  have hcard : 4 ≤ (List.range (2 * 24 + 1)).toFinset.card :=
    le_of_le_of_eq (by norm_num) (range_toFinset_card _).symm
  let all := singleRefs (List.range (2 * 24 + 1)) ∪ PairedTopPruning.dead 24 ∪ D
  have hactive : Disjoint (mark N (outputRefs (List.range (2 * 24 + 1))).toFinset) all := by
    apply Finset.disjoint_left.mpr
    intro i hi hmem
    rcases Finset.mem_union.mp hmem with hmem | hD
    · rcases Finset.mem_union.mp hmem with hsingle | hother
      · obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
        exact single_output_not_marked _ List.pairwise_lt_range (by omega) a ha i he hi
      · exact dead_not_marked 24 (by norm_num) i hother hi
    · exact hDdead i hD hi
  have hsub : all ⊆ additionIds N :=
    Finset.union_subset (Finset.union_subset
      (singleRefs_subset_additionIds _ List.pairwise_lt_range hcard)
      (dead_additions 24 (by norm_num))) hDadd
  have hcount := additionCountFrom_eq_card N all hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDsingle, hDstrip⟩),
    Finset.card_union_of_disjoint (dead_disjoint 24 (by norm_num)),
    singleRefs_card _ List.pairwise_lt_range (by omega), PairedTopPruning.dead_card 24 (by norm_num),
    hDcard, List.length_range] at hcount
  have h := additionCountFrom_add_le 0 N _ _ hactive
  rw [hcount] at h
  show additionCountFrom 0 (mark N (outputRefs (List.range (2 * 24 + 1))).toFinset) N +
    (2 * 24 + 1 + 48 + 5) ≤ additionCount N
  omega

/-- The 49-vertex local circuit has at most 9,813 live additions: the sharp
local count, proved without generated circuits or concrete evaluation. -/
theorem live_le_49 :
    DisjointPruning.additionCountFrom 0 (DisjointPruning.mark (PairedInitialGraph.circuit (List.range 49)).nodes
      (PairedInitialGraph.outputRefs (List.range 49)).toFinset)
      (PairedInitialGraph.circuit (List.range 49)).nodes ≤ 9813 := by
  have h := live_le_range 49 rfl
  have hc := PairedLevelBound.circuit_additions_le
  omega

end IntegerMultBounds.Networks.PairedBasePruning
