module

public import IntegerMultBounds.Networks.PairedLevelBound
import IntegerMultBounds.Networks.PairedSingleBudget
import IntegerMultBounds.Networks.PairedLevelTools
public import IntegerMultBounds.Networks.PairedPruning
import IntegerMultBounds.Networks.DisjointPruningBudget
import IntegerMultBounds.Networks.DAGValueTransfer
public import IntegerMultBounds.Networks.DAGAdditionIds
import IntegerMultBounds.Networks.PairedBlockCorrect
import IntegerMultBounds.Networks.PairedReconstructionKeys
import IntegerMultBounds.Networks.PairedCoarseQuery
import IntegerMultBounds.Networks.PairedStripSupport
public import IntegerMultBounds.Networks.PairedStripCorrect
import IntegerMultBounds.Networks.DisjointExclusion
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient

/-! Dead strip totals at the top level. With zero vertex weights, the total
of the strip at `a` is every edge from its partner to the other groups. That
touches every vertex except `a`, so it fits inside no pair-exclusion output,
and it is never an ancestor of a requested output. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedTopPruning

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect DAGAllocator
open PairedLevelTools PairedLevelBound

abbrev P (m : ℕ) := List.range (2 * m + 1)

/-- The coarse call of the top level. -/
def coarse (m : ℕ) : BlockResult PairedInitialGraph.Input :=
  let ce := coarseEdges (PairedInitialGraph.nodes (P m)) (oddGroups m) (PairedInitialGraph.edges (P m))
  let cw := coarseWeights ce.1 (oddGroups m) (PairedInitialGraph.edges (P m)) (PairedInitialGraph.weights (P m))
  block cw.1 (List.range (oddGroups m).length) ce.2 cw.2

/-- The top-level strips. -/
def strips (m : ℕ) : List (Node PairedInitialGraph.Input) × List Strip :=
  buildStrips (coarse m).nodes (oddGroups m) (PairedInitialGraph.edges (P m)) (PairedInitialGraph.weights (P m))

theorem circuit_eq (m : ℕ) (hm : 2 ≤ m) :
    PairedInitialGraph.circuit (P m) = reconstruct (oddGroups m) (PairedInitialGraph.edges (P m))
      (PairedInitialGraph.weights (P m)) (coarse m) := by
  rw [PairedInitialGraph.circuit, block_large _ _ _ _ (by simp; omega)]
  rfl

theorem strips_extends (m : ℕ) (hm : 2 ≤ m) :
    Extends (strips m).1 (PairedInitialGraph.circuit (P m)).nodes := by
  rw [circuit_eq m hm]
  exact extends_trans (buildSingles_extends _ _ _ _) (buildCrossPairs_extends _ _ _ _ _)

/-- The strip total of every member, in the final circuit. -/
theorem strip_total_spec (m : ℕ) (hm : 2 ≤ m) (ia : ℕ × ℕ) (hia : ia ∈ members (oddGroups m)) :
    RefSpec
      (supports (PairedInitialGraph.nodes (P m))
        (stripQueries (oddGroups m) (PairedInitialGraph.edges (P m)) (PairedInitialGraph.weights (P m)) ia).flatten)
      (PairedInitialGraph.circuit (P m)).nodes (stripLookup (strips m).2 ia.2).total := by
  have hg := PairedInitialGraph.graphReady (P m) List.pairwise_lt_range
  have hc := PairedBlockCorrect.block_correct _ _ _ _ (PairedCoarseCorrect.coarseGraph_ready hg)
  have hr := PairedCoarseQuery.recursive_correct hg (coarse m) hc
  have hb := buildStrips_built (coarse m).nodes (oddGroups m) (PairedInitialGraph.edges (P m))
    (PairedInitialGraph.weights (P m)) hr.input.valid
    (fun ia _ => (PairedStripSupport.stripQueries_ready hr.input ia).1)
    (fun ia _ => (PairedStripSupport.stripQueries_ready hr.input ia).2)
  have hkeys : ((members (oddGroups m)).map Prod.snd).Nodup := by
    rw [PairedReconstructionKeys.members_groups]; exact List.nodup_range
  have hs := stripLookup_semantics _ _ _ _ _ _ _ hb.2.2 hkeys ia hia
  have ht := hs.2.1
  rw [DisjointExclusion.supports_extends hr.extension _
    (fun r hm' => (PairedStripSupport.stripQueries_ready hg ia).1 r hm')] at ht
  exact refSpec_extends (strips_extends m hm) ht

/-! ### The strip total's support -/

theorem mem_groupAt (m j x : ℕ) : x ∈ groupAt (oddGroups m) j ↔ x ≤ 2 * m ∧ x / 2 = j := by
  by_cases hj : j ≤ m
  · rcases groupAt_cases m j hj with ⟨hjm, hg⟩ | ⟨rfl, hg⟩ <;> rw [hg] <;> simp <;> omega
  · have hg : groupAt (oddGroups m) j = [] := by
      simp only [groupAt]
      rw [List.getElem?_eq_none (by rw [oddGroups_length]; omega)]
      rfl
    rw [hg]; simp; omega

/-- The partner of a pair-group member. -/
def partner (i a : ℕ) : ℕ := if a = 2 * i then 2 * i + 1 else 2 * i

theorem pairs_range_mem (n x y : ℕ) : (x, y) ∈ pairs (List.range n) ↔ x < y ∧ y < n := by
  rw [pairs_mem _ List.pairwise_lt_range]; simp; omega

theorem edge_support (m u x : ℕ) (hu : u < 2 * m + 1) (hx : x < 2 * m + 1) (hux : u ≠ x) :
    refSupport (PairedInitialGraph.nodes (P m)) (edgeLookup (PairedInitialGraph.edges (P m)) u x) =
      {(min u x, max u x)} := by
  have hp : (min u x, max u x) ∈ pairs (P m) := by rw [pairs_range_mem]; omega
  exact (tableSpec_lookup _ _ _ _ (PairedInitialGraph.edges_spec (P m)) _ hp).2

theorem weight_none (m a : ℕ) : lookup (PairedInitialGraph.weights (P m)) a = none := by
  apply lookup_zero
  intro e he
  simp only [PairedInitialGraph.weights, List.mem_map] at he
  obtain ⟨_, -, rfl⟩ := he
  rfl

/-- Strip total support: every edge from the partner to the other groups. -/
theorem mem_strip (m i a : ℕ) (hi : i < m) (ha : a = 2 * i ∨ a = 2 * i + 1) (z : ℕ × ℕ) :
    z ∈ supports (PairedInitialGraph.nodes (P m))
        (stripQueries (oddGroups m) (PairedInitialGraph.edges (P m))
          (PairedInitialGraph.weights (P m)) (i, a)).flatten ↔
      ∃ x, x ≤ 2 * m ∧ x / 2 ≠ i ∧ z = (min (partner i a) x, max (partner i a) x) := by
  have hrem : (groupAt (oddGroups m) i).filter (· != a) = [partner i a] := by
    rw [groupAt_lt m i hi]
    rcases ha with rfl | rfl <;> simp [partner]
  have hu : partner i a / 2 = i ∧ partner i a ≤ 2 * m := by
    simp only [partner]; split_ifs <;> omega
  simp only [stripQueries, hrem, List.map_cons, List.map_nil, List.flatten_cons, weight_none,
    supports_toFinset, Finset.mem_biUnion, List.mem_toFinset, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_flatten, List.mem_map, oddGroups_length]
  constructor
  · rintro ⟨r, hr, hz⟩
    rcases hr with rfl | ⟨q, ⟨j, hj, rfl⟩, hr⟩
    · simp [refSupport] at hz
    · rw [crossRefs_one] at hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      simp only [List.mem_filter, List.mem_range, bne_iff_ne] at hj
      have hx' := (mem_groupAt m j x).mp hx
      rw [edge_support m _ x (by omega) (by omega) (by omega)] at hz
      exact ⟨x, hx'.1, by omega, Finset.mem_singleton.mp hz⟩
  · rintro ⟨x, hx, hxi, rfl⟩
    refine ⟨edgeLookup (PairedInitialGraph.edges (P m)) (partner i a) x,
      Or.inr ⟨_, ⟨x / 2, ?_, rfl⟩, ?_⟩, ?_⟩
    · simp only [List.mem_filter, List.mem_range, bne_iff_ne]; omega
    · rw [crossRefs_one]
      exact List.mem_map_of_mem ((mem_groupAt m _ x).mpr ⟨hx, rfl⟩)
    · rw [edge_support m _ x (by omega) (by omega) (by omega)]
      exact Finset.mem_singleton_self _

abbrev S (m : ℕ) (ia : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  supports (PairedInitialGraph.nodes (P m))
    (stripQueries (oddGroups m) (PairedInitialGraph.edges (P m)) (PairedInitialGraph.weights (P m)) ia).flatten

theorem partner_facts (i a : ℕ) (_ha : a = 2 * i ∨ a = 2 * i + 1) :
    partner i a / 2 = i ∧ partner i a ≠ a := by
  simp only [partner]; split_ifs <;> omega

/-- A vertex in another group than `i`. -/
def far (i : ℕ) : ℕ := if i = 0 then 2 else 0

theorem far_facts (m i : ℕ) (hm : 2 ≤ m) : far i ≤ 2 * m ∧ far i / 2 ≠ i ∧
    far i + 1 ≤ 2 * m ∧ (far i + 1) / 2 ≠ i := by
  simp only [far]; split_ifs <;> omega

/-- No pair output contains a top strip total. -/
theorem strip_obstructed (m i a : ℕ) (hm : 2 ≤ m) (hi : i < m) (ha : a = 2 * i ∨ a = 2 * i + 1)
    (p : ℕ × ℕ) (hp : p ∈ pairs (P m)) :
    ¬ S m (i, a) ⊆ (pairs (P m)).toFinset.filter (fun q => q.1 ∉ [p.1, p.2] ∧ q.2 ∉ [p.1, p.2]) := by
  have hp' := (pairs_range_mem _ p.1 p.2).mp hp
  obtain ⟨hu2, hua⟩ := partner_facts i a ha
  obtain ⟨hf, hfi, -, -⟩ := far_facts m i hm
  intro hsub
  -- a vertex of the output pair other than `a`
  obtain ⟨c, hc, hca⟩ : ∃ c, (c = p.1 ∨ c = p.2) ∧ c ≠ a := by
    by_cases h : p.1 = a
    · exact ⟨p.2, Or.inr rfl, by omega⟩
    · exact ⟨p.1, Or.inl rfl, h⟩
  let x := if c = partner i a then far i else c
  have hx : x ≤ 2 * m ∧ x / 2 ≠ i := by
    simp only [x]; split_ifs with h
    · exact ⟨hf, hfi⟩
    · constructor
      · rcases hc with rfl | rfl <;> omega
      · intro hcd
        rcases ha with rfl | rfl <;> simp only [partner] at h <;> split_ifs at h <;> omega
  have hz := (mem_strip m i a hi ha _).mpr ⟨x, hx.1, hx.2, rfl⟩
  have hin := Finset.mem_filter.mp (hsub hz)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  simp only [x] at hin
  split_ifs at hin with h
  · rcases hc with rfl | rfl <;> omega
  · rcases hc with rfl | rfl <;> omega

theorem strip_two (m i a : ℕ) (hm : 2 ≤ m) (hi : i < m) (ha : a = 2 * i ∨ a = 2 * i + 1) :
    2 ≤ (S m (i, a)).card := by
  obtain ⟨hu2, -⟩ := partner_facts i a ha
  obtain ⟨h1, h2, h3, h4⟩ := far_facts m i hm
  apply Finset.one_lt_card.mpr
  refine ⟨_, (mem_strip m i a hi ha _).mpr ⟨far i, h1, h2, rfl⟩,
    _, (mem_strip m i a hi ha _).mpr ⟨far i + 1, h3, h4, rfl⟩, ?_⟩
  intro he
  simp only [Prod.mk.injEq] at he
  omega

/-- Different members have different strip totals. -/
theorem strip_injective (m : ℕ) (hm : 2 ≤ m) (i a j b : ℕ) (hi : i < m) (ha : a = 2 * i ∨ a = 2 * i + 1)
    (hj : j < m) (hb : b = 2 * j ∨ b = 2 * j + 1) (he : S m (i, a) = S m (j, b)) : a = b := by
  by_contra hab
  obtain ⟨hu2, hua⟩ := partner_facts i a ha
  obtain ⟨hv2, hvb⟩ := partner_facts j b hb
  obtain ⟨h1, h2, -, -⟩ := far_facts m j hm
  -- `S (j, b)` touches `a`; `S (i, a)` does not
  have htouch : ∃ z ∈ S m (j, b), z.1 = a ∨ z.2 = a := by
    by_cases hp : a = partner j b
    · exact ⟨_, (mem_strip m j b hj hb _).mpr ⟨far j, h1, h2, rfl⟩, by omega⟩
    · have hj' : a / 2 ≠ j := by
        intro h
        rcases hb with rfl | rfl <;> simp only [partner] at hp <;> split_ifs at hp <;> omega
      exact ⟨_, (mem_strip m j b hj hb _).mpr ⟨a, by omega, hj', rfl⟩, by omega⟩
  obtain ⟨z, hz, hza⟩ := htouch
  rw [← he] at hz
  obtain ⟨x, -, hx, rfl⟩ := (mem_strip m i a hi ha _).mp hz
  simp only at hza
  omega

/-- A top strip total is never a single-exclusion support. -/
theorem strip_ne_single (m i a b : ℕ) (hm : 2 ≤ m) (hi : i < m) (ha : a = 2 * i ∨ a = 2 * i + 1) :
    S m (i, a) ≠ PairedInitialGraph.singleSupport (P m) b := by
  intro he
  have hc : 2 ≤ (({0, 1, 2, 3} : Finset ℕ) \ {partner i a, b}).card := by
    have h1 := Finset.card_sdiff_add_card_inter ({0, 1, 2, 3} : Finset ℕ) {partner i a, b}
    have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := ({0, 1, 2, 3} : Finset ℕ))
      (s₂ := {partner i a, b}))
    have h3 := Finset.card_insert_le (partner i a) ({b} : Finset ℕ)
    have h4 : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
    simp only [Finset.card_singleton] at h3
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hy hz
  have hmem : (min y z, max y z) ∈ PairedInitialGraph.singleSupport (P m) b := by
    simp only [PairedInitialGraph.singleSupport, Finset.mem_filter, List.mem_toFinset, pairs_range_mem]
    omega
  rw [← he] at hmem
  obtain ⟨x, -, -, hx⟩ := (mem_strip m i a hi ha _).mp hmem
  simp only [Prod.mk.injEq] at hx
  omega

/-! ### The pruning credit -/

open DisjointPruning DAGSupportTrace DAGAdditionIds PairedInitialGraph

abbrev C (m : ℕ) := (PairedInitialGraph.circuit (P m)).nodes

/-- The stored node of the strip total at vertex `a`. -/
def totalIndex (m a : ℕ) : ℕ := ((stripLookup (strips m).2 a).total).getD 0

theorem member_of (m a : ℕ) (ha : a < 2 * m) : (a / 2, a) ∈ members (oddGroups m) := by
  simp only [members, List.mem_flatMap, List.mem_range, oddGroups_length, List.mem_map]
  refine ⟨a / 2, by omega, a, ?_, rfl⟩
  rw [groupAt_lt m (a / 2) (by omega)]
  simp; omega

theorem support_eq (m k : ℕ) (hk : k < (C m).length) :
    nodeSupport (C m) k = (C m)[k].support := nodeSupport_get _ k hk

theorem total_index_spec (m a : ℕ) (hm : 2 ≤ m) (ha : a < 2 * m) :
    (stripLookup (strips m).2 a).total = some (totalIndex m a) ∧ totalIndex m a < (C m).length ∧
      nodeSupport (C m) (totalIndex m a) = S m (a / 2, a) := by
  have hspec := strip_total_spec m hm (a / 2, a) (member_of m a ha)
  have htwo := strip_two m (a / 2) a hm (by omega) (by omega)
  cases ht : (stripLookup (strips m).2 a).total with
  | none =>
    rw [ht] at hspec
    have he := hspec.2
    simp only [refSupport] at he
    simp only [S] at htwo
    rw [← he] at htwo
    simp at htwo
  | some k =>
    rw [ht] at hspec
    have hk : totalIndex m a = k := by simp [totalIndex, ht]
    rw [hk]
    refine ⟨rfl, hspec.1, ?_⟩
    exact hspec.2

/-- The dead strip totals of the top level. -/
def dead (m : ℕ) : Finset ℕ := (Finset.range (2 * m)).image (totalIndex m)

theorem dead_card (m : ℕ) (hm : 2 ≤ m) : (dead m).card = 2 * m := by
  rw [dead, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb he
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h1 := (total_index_spec m a hm ha).2.2
  have h2 := (total_index_spec m b hm hb).2.2
  rw [show totalIndex m a = totalIndex m b from he, h2] at h1
  exact strip_injective m hm (b / 2) b (a / 2) a (by omega) (by omega) (by omega) (by omega) h1 |>.symm

theorem dead_additions (m : ℕ) (hm : 2 ≤ m) : dead m ⊆ additionIds (C m) := by
  intro k hk
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
  have ha' := Finset.mem_range.mp ha
  obtain ⟨-, hb, hs⟩ := total_index_spec m a hm ha'
  rw [support_eq m _ hb] at hs
  have hnode := DAGValueTransfer.validFrom_get [] (C m)
    (PairedInitialGraph.circuit_correct (P m) List.pairwise_lt_range).valid _ hb
  cases hkind : (C m)[totalIndex m a].kind with
  | input p =>
    have heq : (C m)[totalIndex m a].support = {p} := by simpa only [Node.Valid, hkind] using hnode
    have hc := strip_two m (a / 2) a hm (by omega) (by omega)
    rw [← hs, heq, Finset.card_singleton] at hc
    omega
  | add l r => exact (mem_additionIds _ _).mpr ⟨_, List.getElem?_eq_getElem hb, l, r, hkind⟩

theorem dead_not_marked (m : ℕ) (hm : 2 ≤ m) :
    ∀ k ∈ dead m, k ∉ mark (C m) (outputRefs (P m)).toFinset := by
  intro k hk
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
  have ha' := Finset.mem_range.mp ha
  obtain ⟨-, hb, hs⟩ := total_index_spec m a hm ha'
  apply not_marked_of_support _ (PairedInitialGraph.circuit_correct (P m) List.pairwise_lt_range).valid
  intro r hr
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hr)
  have hpair := (circuit_pair_support (P m) List.pairwise_lt_range p hp).2
  rw [he] at hpair
  change nodeSupport (C m) r = _ at hpair
  rw [hs, hpair]
  exact strip_obstructed m (a / 2) a hm (by omega) (by omega) p hp

theorem dead_disjoint (m : ℕ) (hm : 2 ≤ m) : Disjoint (singleRefs (P m)) (dead m) := by
  apply Finset.disjoint_left.mpr
  intro k hsingle hk
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
  have ha' := Finset.mem_range.mp ha
  obtain ⟨-, hb, hs⟩ := total_index_spec m a hm ha'
  rw [support_eq m _ hb] at hs
  obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
  have hspec := (circuit_single_support (P m) List.pairwise_lt_range c hc).2
  rw [he, refSupport_some _ _ hb] at hspec
  exact strip_ne_single m (a / 2) a c hm (by omega) (by omega) (hs.symm.trans hspec)

/-- Live additions of the local circuit, after both pruning credits. -/
theorem live_le (m : ℕ) (hm : 2 ≤ m) :
    additionCountFrom 0 (mark (C m) (outputRefs (P m)).toFinset) (C m) + ((2 * m + 1) + 2 * m) ≤
      additionCount (C m) := by
  have hcard : 4 ≤ (P m).toFinset.card := by
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]; omega
  have hactive : Disjoint (mark (C m) (outputRefs (P m)).toFinset) (singleRefs (P m) ∪ dead m) := by
    apply Finset.disjoint_left.mpr
    intro i hi hmem
    rcases Finset.mem_union.mp hmem with hsingle | hother
    · obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
      exact single_output_not_marked (P m) List.pairwise_lt_range (by omega) a ha i he hi
    · exact dead_not_marked m hm i hother hi
  have hcount := additionCountFrom_eq_card (C m) (singleRefs (P m) ∪ dead m)
    (Finset.union_subset (singleRefs_subset_additionIds (P m) List.pairwise_lt_range hcard)
      (dead_additions m hm))
  rw [Finset.card_union_of_disjoint (dead_disjoint m hm),
    singleRefs_card (P m) List.pairwise_lt_range (by omega), dead_card m hm, List.length_range] at hcount
  have h := additionCountFrom_add_le 0 (C m) _ _ hactive
  rw [hcount] at h
  exact h

theorem live_le_range (m n : ℕ) (hm : 2 ≤ m) (hn : 2 * m + 1 = n) :
    additionCountFrom 0 (mark (PairedInitialGraph.circuit (List.range n)).nodes
      (outputRefs (List.range n)).toFinset) (PairedInitialGraph.circuit (List.range n)).nodes +
      (n + 2 * m) ≤ additionCount (PairedInitialGraph.circuit (List.range n)).nodes := by
  subst hn
  exact live_le m hm

/-- The 49-vertex local circuit has at most 9,818 live additions. -/
theorem live_le_49 :
    additionCountFrom 0 (mark (PairedInitialGraph.circuit (List.range 49)).nodes
      (outputRefs (List.range 49)).toFinset) (PairedInitialGraph.circuit (List.range 49)).nodes ≤ 9818 := by
  have h := live_le_range 24 49 (by norm_num) (by norm_num)
  have hc := PairedLevelBound.circuit_additions_le
  omega

end IntegerMultBounds.Networks.PairedTopPruning
