module

public import IntegerMultBounds.Networks.PairedStarFamily
public import IntegerMultBounds.Networks.PairedIndexedPruning
import IntegerMultBounds.Networks.PairedSingleBudget
import IntegerMultBounds.Networks.DisjointPruningBudget
import IntegerMultBounds.Networks.DAGValueTransfer

/-! The 102 credited dead additions of the local circuit, and the nodes of
the counted stars. No counted star is a single exclusion, a top strip total or
one of the five dead base sums: each misses two vertices, while those touch
all but at most one. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarNodes

open DisjointCircuit DisjointBuilder PairedCircuit DisjointPruning DAGSupportTrace DAGAdditionIds
open PairedInitialGraph PairedStarCount PairedStarFamily PairedStarPresence PairedBasePruning

/-- The supports of the credited dead additions. -/
def Bad (s : Finset Input) : Prop :=
  (∃ b < 49, s = singleSupport (List.range 49) b) ∨ (∃ a < 48, s = PairedTopPruning.S 24 (a / 2, a)) ∨
    Good s

/-- Symbolic restatement of the strip total's node, to avoid comparing concrete circuits. -/
theorem total_index_explicit (m : ℕ) (hm : 2 ≤ m) (a : ℕ) (ha : a < 2 * m) :
    PairedTopPruning.totalIndex m a < (circuit (List.range (2 * m + 1))).nodes.length ∧
      nodeSupport (circuit (List.range (2 * m + 1))).nodes (PairedTopPruning.totalIndex m a) =
        PairedTopPruning.S m (a / 2, a) :=
  (PairedTopPruning.total_index_spec m a hm ha).2

theorem dead_range (n : ℕ) (hn : 2 * 24 + 1 = n) :
    ∃ all : Finset ℕ, all ⊆ additionIds (circuit (List.range n)).nodes ∧ all.card = 102 ∧
      Disjoint (mark (circuit (List.range n)).nodes (outputRefs (List.range n)).toFinset) all ∧
      ∀ k ∈ all, ∃ hk : k < (circuit (List.range n)).nodes.length,
        Bad (circuit (List.range n)).nodes[k].support := by
  have hdead := PairedBasePruning.dead_range n hn
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
    have hsup := strip_support 24 (by decide) a ha'
    rw [he] at hsup
    exact not_strip_of_good _ k hb hg a (by omega) hsup
  have hcard : 4 ≤ (List.range (2 * 24 + 1)).toFinset.card :=
    le_of_le_of_eq (by decide) (range_toFinset_card _).symm
  let all := singleRefs (List.range (2 * 24 + 1)) ∪ PairedTopPruning.dead 24 ∪ D
  refine ⟨all, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset (Finset.union_subset
      (singleRefs_subset_additionIds _ List.pairwise_lt_range hcard)
      (dead_additions 24 (by decide))) hDadd
  · rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDsingle, hDstrip⟩),
      Finset.card_union_of_disjoint (dead_disjoint 24 (by decide)),
      singleRefs_card _ List.pairwise_lt_range (by omega), PairedTopPruning.dead_card 24 (by decide),
      hDcard, List.length_range]
  · apply Finset.disjoint_left.mpr
    intro i hi hmem
    rcases Finset.mem_union.mp hmem with hmem | hD
    · rcases Finset.mem_union.mp hmem with hsingle | hother
      · obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
        exact single_output_not_marked _ List.pairwise_lt_range (by omega) a ha i he hi
      · exact dead_not_marked 24 (by decide) i hother hi
    · exact hDdead i hD hi
  · intro k hk
    rcases Finset.mem_union.mp hk with hk | hD
    · rcases Finset.mem_union.mp hk with hsingle | hother
      · obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
        have hspec := circuit_single_support (List.range (2 * 24 + 1)) List.pairwise_lt_range c hc
        rw [he] at hspec
        have hb : k < N.length := hspec.1
        refine ⟨hb, Or.inl ⟨c, List.mem_range.mp hc, ?_⟩⟩
        rw [← refSupport_some _ _ hb]
        exact hspec.2
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hother
        have ha' := Finset.mem_range.mp ha
        obtain ⟨hb, hs⟩ := total_index_explicit 24 (by decide) a ha'
        refine ⟨hb, Or.inr (Or.inl ⟨a, by omega, ?_⟩)⟩
        rw [← nodeSupport_get _ _ hb]
        exact hs
    · obtain ⟨hb, hg⟩ := hgood k hD
      exact ⟨hb, Or.inr (Or.inr hg)⟩

theorem dead_49 : ∃ all : Finset ℕ, all ⊆ additionIds (circuit (List.range 49)).nodes ∧ all.card = 102 ∧
    Disjoint (mark (circuit (List.range 49)).nodes (outputRefs (List.range 49)).toFinset) all ∧
    ∀ k ∈ all, ∃ hk : k < (circuit (List.range 49)).nodes.length,
      Bad (circuit (List.range 49)).nodes[k].support :=
  dead_range 49 rfl

/-! ### Counted stars are not dead -/

theorem strip_touch (a : ℕ) (ha : a < 48) (w : ℕ) (hw : w < 49) (hwa : w ≠ a) :
    ∃ z ∈ PairedTopPruning.S 24 (a / 2, a), z.1 = w ∨ z.2 = w := by
  obtain ⟨hu2, hua⟩ := PairedTopPruning.partner_facts (a / 2) a (by omega)
  by_cases hw2 : w / 2 = a / 2
  · have hwp : w = PairedTopPruning.partner (a / 2) a := by
      simp only [PairedTopPruning.partner] at hu2 hua ⊢; split_ifs at hu2 hua ⊢ <;> omega
    obtain ⟨h1, h2, -, -⟩ := PairedTopPruning.far_facts 24 (a / 2) (by decide)
    refine ⟨_, (PairedTopPruning.mem_strip 24 (a / 2) a (by omega) (by omega) _).mpr
      ⟨PairedTopPruning.far (a / 2), h1, h2, rfl⟩, ?_⟩
    simp only
    omega
  · refine ⟨_, (PairedTopPruning.mem_strip 24 (a / 2) a (by omega) (by omega) _).mpr
      ⟨w, by omega, hw2, rfl⟩, ?_⟩
    simp only
    omega

theorem star_touch (v : ℕ) (xs : List ℕ) (z : ℕ × ℕ) (hz : z ∈ star v xs) (w : ℕ)
    (hw : z.1 = w ∨ z.2 = w) : w = v ∨ w ∈ xs := by
  obtain ⟨x, hx, rfl⟩ := (mem_star v xs z).mp hz
  simp only at hw
  by_cases hvx : v ≤ x
  · rw [min_eq_left hvx, max_eq_right hvx] at hw
    rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hx
  · rw [min_eq_right (by omega), max_eq_left (by omega)] at hw
    rcases hw with rfl | rfl
    · exact Or.inr hx
    · exact Or.inl rfl

/-- A counted star misses two vertices. -/
theorem two_missed (v : ℕ) (hv : v < 49) (xs : List ℕ) (hx : xs ∈ fam v) :
    ∃ y z, y < z ∧ z < 49 ∧ y ≠ v ∧ y ∉ xs ∧ z ≠ v ∧ z ∉ xs := by
  obtain ⟨hs, hvx, hlt, h2, h46⟩ := fam_shape' v hv xs hx
  have hT : (insert v xs.toFinset).card ≤ 47 := by
    have := Finset.card_insert_le v xs.toFinset
    have := List.toFinset_card_le xs
    omega
  have hc : 1 < (Finset.range 49 \ insert v xs.toFinset).card := by
    have := Finset.le_card_sdiff (insert v xs.toFinset) (Finset.range 49)
    simp only [Finset.card_range] at this
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, List.mem_toFinset, not_or] at hy hz
  rcases Nat.lt_or_gt_of_ne hyz with h | h
  · exact ⟨y, z, h, hz.1, hy.2.1, hy.2.2, hz.2.1, hz.2.2⟩
  · exact ⟨z, y, h, hy.1, hz.2.1, hz.2.2, hy.2.1, hy.2.2⟩

theorem star_not_bad (v : ℕ) (hv : v < 49) (xs : List ℕ) (hx : xs ∈ fam v) : ¬ Bad (star v xs) := by
  obtain ⟨hs, hvx, hlt, h2, h46⟩ := fam_shape' v hv xs hx
  obtain ⟨y, z, hyz, hz, hyv, hyx, hzv, hzx⟩ := two_missed v hv xs hx
  rintro (⟨b, hb, he⟩ | ⟨a, ha, he⟩ | hg)
  · -- a single exclusion keeps an edge avoiding `v`
    have hc : 2 ≤ (({0, 1, 2, 3} : Finset ℕ) \ {v, b}).card := by
      have h1 := Finset.card_sdiff_add_card_inter ({0, 1, 2, 3} : Finset ℕ) {v, b}
      have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := ({0, 1, 2, 3} : Finset ℕ))
        (s₂ := {v, b}))
      have h3 := Finset.card_insert_le v ({b} : Finset ℕ)
      have h4 : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
      simp only [Finset.card_singleton] at h3
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hc
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hp hq
    have hmem := single_mem b (min p q) (max p q) (by omega) (by omega) (by omega) (by omega)
    rw [← he] at hmem
    have := star_touch v xs _ hmem v
    obtain ⟨x, -, hxe⟩ := (mem_star v xs _).mp hmem
    simp only [Prod.mk.injEq] at hxe
    omega
  · -- a strip total touches every vertex but `a`
    have hw : ∃ w, w < 49 ∧ w ≠ a ∧ w ≠ v ∧ w ∉ xs := by
      by_cases hya : y = a
      · exact ⟨z, hz, by omega, hzv, hzx⟩
      · exact ⟨y, by omega, hya, hyv, hyx⟩
    obtain ⟨w, hw49, hwa, hwv, hwx⟩ := hw
    obtain ⟨t, ht, htw⟩ := strip_touch a ha w hw49 hwa
    rw [← he] at ht
    rcases star_touch v xs t ht w htw with h | h
    · exact hwv h
    · exact hwx h
  · -- a dead base sum fits in no pair output, but the star avoids `y` and `z`
    apply hg.obstructed (y, z) ((PairedTopPruning.pairs_range_mem 49 y z).mpr ⟨hyz, hz⟩)
    intro t ht
    obtain ⟨x, hxm, rfl⟩ := (mem_star v xs t).mp ht
    have hx49 := hlt x hxm
    have hxv : x ≠ v := fun h => hvx (h ▸ hxm)
    have hxy : x ≠ y := fun h => hyx (h ▸ hxm)
    have hxz : x ≠ z := fun h => hzx (h ▸ hxm)
    simp only [R, Finset.mem_filter, List.mem_toFinset, PairedTopPruning.pairs_range_mem,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

end IntegerMultBounds.Networks.PairedStarNodes
