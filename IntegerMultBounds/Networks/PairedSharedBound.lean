module

public import IntegerMultBounds.Networks.PairedStarShared

/-! The 40,256 counted stars as duplicate witnesses of the fifty-copy family
over the local circuit less its credited dead additions, and the resulting
bound of 450,394 distinct supports for the pruned circuit used by replay. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarShared

open DisjointCircuit DisjointBuilder PairedCircuit DisjointPruning DAGAdditionIds
open PairedInitialGraph PairedStarCount PairedStarFamily PairedStarPresence PairedStarNodes
open SharedPointMatching

theorem val_succAbove (c : Fin 50) (w : Fin 49) : (c.succAbove w).val = sa c.val w.val := by
  unfold Fin.succAbove sa
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

open Classical in
/-- The matching leaf list at center `c` of copy `c'`. -/
noncomputable def partner (c c' : ℕ) (xs : List ℕ) : List ℕ :=
  if h : ∃ ys ∈ fam c, ∀ y, y ∈ xs.map (sa c) ↔ y ∈ ys.map (sa c') then Classical.choose h else []

theorem partner_spec (c c' : ℕ) (hc : c < c') (hc' : c' < 50) (xs : List ℕ) (hm : xs ∈ matched c c') :
    partner c c' xs ∈ fam c ∧ ∀ y, y ∈ xs.map (sa c) ↔ y ∈ (partner c c' xs).map (sa c') := by
  have h := (matched_spec c c' hc hc' xs hm).2
  simp only [partner, dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

/-- Counted triples `(c, c', xs)` with `c < c'`. -/
def triples : List (ℕ × ℕ × List ℕ) :=
  (List.range 50).flatMap fun c' => (List.range c').flatMap fun c => (matched c c').map fun xs => (c, c', xs)

theorem mem_triples (t : ℕ × ℕ × List ℕ) :
    t ∈ triples ↔ t.2.1 < 50 ∧ t.1 < t.2.1 ∧ t.2.2 ∈ matched t.1 t.2.1 := by
  obtain ⟨c, c', xs⟩ := t
  simp only [triples, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨d', hd', d, hd, ys, hys, rfl, rfl, rfl⟩
    exact ⟨hd', hd, hys⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨c', h1, c, h2, xs, h3, rfl, rfl, rfl⟩

theorem triples_nodup : triples.Nodup := by
  unfold triples
  apply List.nodup_flatMap.mpr
  refine ⟨fun c' hc' => ?_, ?_⟩
  · apply List.nodup_flatMap.mpr
    refine ⟨fun c hc => ?_, ?_⟩
    · have := List.mem_range.mp hc'
      exact (matched_nodup c c' (by omega)).map (fun a b he => by simpa using he)
    · apply List.nodup_range.imp_of_mem
      intro a b _ _ hab x hx hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, he⟩ := List.mem_map.mp hy
      exact hab (congrArg Prod.fst he).symm
  · apply List.nodup_range.imp_of_mem
    have hsnd : ∀ a, ∀ x ∈ (List.range a).flatMap (fun c => (matched c a).map fun xs => (c, a, xs)),
        x.2.1 = a := by
      intro a x hx
      simp only [List.mem_flatMap, List.mem_map] at hx
      obtain ⟨_, _, _, _, rfl⟩ := hx
      rfl
    intro a b _ _ hab x hx hy
    exact hab ((hsnd a x hx).symm.trans (hsnd b x hy))

theorem triples_length : 40256 ≤ triples.length := by
  have h := matched_total
  simp only [triples, List.length_flatMap, List.length_map] at h ⊢
  exact h

/-! ### The witness family -/

section Witness

variable (P : PairedLocalCircuit) (N : List (Node Input)) (all : Finset ℕ)

/-- Every copy keeps its actual additions except the credited dead ones. -/
def domain : Finset (CopyNode 50) := Finset.univ ×ˢ (additionIds P.nodes \ all)

theorem domain_sub (n : CopyNode 50) (hn : n ∈ domain P all) : n ∈ SharedPointLocalFamily.domain P := by
  simp only [domain, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_sdiff] at hn
  exact (SharedPointLocalFamily.mem_domain P n).mpr hn.1

def family : Family 50 where
  domain := domain P all
  support := SharedPointLocalFamily.support P
  nontrivial := fun n hn => SharedPointLocalFamily.support_nontrivial P n (domain_sub P all n hn)
  common := fun n hn => SharedPointLocalFamily.support_common P n (domain_sub P all n hn)
  unique := fun a ha b hb => SharedPointLocalFamily.support_unique P a (domain_sub P all a ha) b
    (domain_sub P all b hb)

def copy (c : ℕ) : Fin 50 := ⟨c % 50, Nat.mod_lt _ (by decide)⟩

/-- The two star nodes of a counted triple. -/
noncomputable def pairOf (t : ℕ × ℕ × List ℕ) : CopyNode 50 × CopyNode 50 :=
  ((copy t.1, idx N (t.2.1 - 1) t.2.2), (copy t.2.1, idx N t.1 (partner t.1 t.2.1 t.2.2)))

variable (hmap : P.nodes.map (PairedRename.node e49) = N) (hvN : Valid N)
  (hstore : ∀ v < 49, ∀ xs ∈ fam v, star v xs ∈ N.map Node.support)
  (hall : ∀ k ∈ all, ∃ hk : k < N.length, Bad N[k].support)

include hmap hvN hstore hall in
theorem node_mem (v : ℕ) (hv : v < 49) (xs : List ℕ) (hx : xs ∈ fam v) :
    idx N v xs ∈ additionIds P.nodes \ all := by
  refine Finset.mem_sdiff.mpr ⟨?_, fun hk => ?_⟩
  · rw [map_additionIds P N hmap]; exact idx_addition N hvN v hv xs hx (hstore v hv xs hx)
  · obtain ⟨hk', hb⟩ := hall _ hk
    have h := idx_get N v xs (hstore v hv xs hx)
    rw [List.getElem?_eq_getElem hk', Option.map_some] at h
    rw [Option.some.inj h] at hb
    exact star_not_bad v hv xs hx hb

theorem mem_lift (c : Fin 50) (v : Fin 49) (xs : List ℕ) (hxs : ∀ x ∈ xs, x < 49) (u : Fin 50) :
    u ∈ insert c ((insert v (Finset.univ.filter (fun w : Fin 49 => w.val ∈ xs))).image c.succAbove) ↔
      u.val = c.val ∨ u.val = sa c.val v.val ∨ u.val ∈ xs.map (sa c.val) := by
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_map, Fin.ext_iff]
  constructor
  · rintro (h | ⟨w, hw | hw, he⟩)
    · exact Or.inl h
    · right; left; rw [← he, val_succAbove, hw]
    · right; right; exact ⟨w.val, hw, by rw [← he, val_succAbove]⟩
  · rintro (h | h | ⟨x, hx, he⟩)
    · exact Or.inl h
    · right; exact ⟨v, Or.inl rfl, by rw [val_succAbove]; exact h.symm⟩
    · right; exact ⟨⟨x, hxs x hx⟩, Or.inr hx, by rw [val_succAbove]; exact he⟩

include hmap hvN hstore hall in
theorem pairOf_witness (t : ℕ × ℕ × List ℕ) (ht : t ∈ triples) : IsWitness (family P all) (pairOf N t) := by
  obtain ⟨c, c', xs⟩ := t
  obtain ⟨hc', hcc, hm⟩ := (mem_triples _).mp ht
  simp only at hc' hcc hm
  obtain ⟨hxs, -⟩ := matched_spec c c' hcc hc' xs hm
  obtain ⟨hys, hrel⟩ := partner_spec c c' hcc hc' xs hm
  have hv1 : c' - 1 < 49 := by omega
  have hv2 : c < 49 := by omega
  have ha := node_mem P N all hmap hvN hstore hall (c' - 1) hv1 xs hxs
  have hb := node_mem P N all hmap hvN hstore hall c hv2 _ hys
  have hca : (copy c).val = c := Nat.mod_eq_of_lt (by omega)
  have hcb : (copy c').val = c' := Nat.mod_eq_of_lt hc'
  obtain ⟨hcore1, hunion1⟩ := star_endpoints P N hmap (c' - 1) hv1 xs hxs _
    (idx_get N _ xs (hstore _ hv1 xs hxs))
  obtain ⟨hcore2, hunion2⟩ := star_endpoints P N hmap c hv2 _ hys _
    (idx_get N _ _ (hstore _ hv2 _ hys))
  have hdom : ∀ j ∈ additionIds P.nodes \ all, ∀ d : Fin 50, (d, j) ∈ SharedPointLocalFamily.domain P :=
    fun j hj d => (SharedPointLocalFamily.mem_domain P _).mpr (Finset.mem_sdiff.mp hj).1
  have hlt : (copy c) < (copy c') := by rw [Fin.lt_def, hca, hcb]; exact hcc
  have hw := SharedPointLocalFamily.witness_of_endpoints P (copy c, idx N (c' - 1) xs)
    (copy c', idx N c (partner c c' xs)) (hdom _ ha _) (hdom _ hb _) hlt
    (by dsimp only; rw [hcore1]; exact Finset.singleton_nonempty _)
    (by
      dsimp only
      rw [hcore1, hcore2]
      ext u
      simp only [Finset.mem_insert, Finset.image_singleton, Finset.mem_singleton, Fin.ext_iff,
        val_succAbove, hca, hcb, sa]
      split_ifs <;> omega)
    (by
      dsimp only
      rw [hunion1, hunion2]
      ext u
      rw [mem_lift _ _ _ (fam_shape' _ hv1 xs hxs).2.2.1, mem_lift _ _ _ (fam_shape' _ hv2 _ hys).2.2.1,
        hca, hcb, hrel]
      have e1 : sa c (c' - 1) = c' := by simp only [sa]; split_ifs <;> omega
      have e2 : sa c' c = c := by simp only [sa]; split_ifs; omega
      simp only [e1, e2]
      exact or_left_comm)
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, Finset.mem_product.mpr ⟨Finset.mem_univ _, hb⟩,
    hlt, hw.equal⟩

/-- The witness set: one pair of star nodes per counted triple. -/
noncomputable def witnesses : Finset (CopyNode 50 × CopyNode 50) := triples.toFinset.image (pairOf N)

include hstore in
theorem witnesses_card : 40256 ≤ (witnesses N).card := by
  rw [witnesses, Finset.card_image_of_injOn, List.toFinset_card_of_nodup triples_nodup]
  · exact triples_length
  · intro t1 h1 t2 h2 he
    obtain ⟨c1, c1', xs1⟩ := t1
    obtain ⟨c2, c2', xs2⟩ := t2
    obtain ⟨h1a, h1b, h1c⟩ := (mem_triples _).mp (List.mem_toFinset.mp h1)
    obtain ⟨h2a, h2b, h2c⟩ := (mem_triples _).mp (List.mem_toFinset.mp h2)
    simp only at h1a h1b h1c h2a h2b h2c
    simp only [pairOf, Prod.mk.injEq, copy, Fin.mk.injEq] at he
    obtain ⟨⟨hc, hi⟩, hc', -⟩ := he
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc hc'
    subst hc; subst hc'
    have hx1 := (matched_spec _ _ h1b h1a _ h1c).1
    have hx2 := (matched_spec _ _ h2b h2a _ h2c).1
    rw [idx_injective N _ (by omega) xs1 xs2 hx1 hx2 (hstore _ (by omega) _ hx1)
      (hstore _ (by omega) _ hx2) hi]

include hmap hvN hstore hall in
/-- At most 450,394 distinct supports over the fifty copies. -/
theorem image_bound (hcount : (additionIds P.nodes \ all).card ≤ 9813) :
    ((domain P all).image (SharedPointLocalFamily.support P)).card ≤ 450394 := by
  have h := h50_bound (family P all) (witnesses N)
    (fun pair hp => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      exact pairOf_witness P N all hmap hvN hstore hall t (List.mem_toFinset.mp ht))
    (by
      show (domain P all).card ≤ 50 * 9813
      rw [domain, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      omega)
    (witnesses_card N hstore)
  exact h

end Witness

/-! ### The pruned circuit -/

theorem pruned_subset (P : PairedLocalCircuit) (all : Finset ℕ) (hdis : Disjoint P.live all) :
    (SharedPointLocalFamily.domain P.pruned).image (SharedPointLocalFamily.support P.pruned) ⊆
      (domain P all).image (SharedPointLocalFamily.support P) := by
  intro s hs
  obtain ⟨⟨c, k⟩, hk, rfl⟩ := Finset.mem_image.mp hs
  have hk' := (SharedPointLocalFamily.mem_domain _ _).mp hk
  obtain ⟨node, hnode, l, r, hkind⟩ := (mem_additionIds _ _).mp hk'
  obtain ⟨hklt, rfl⟩ := List.getElem?_eq_some_iff.mp hnode
  obtain ⟨j, hj, hlive, hsup, hadd⟩ := DAGCompact.compact_source P.live P.nodes k hklt
  obtain ⟨l', r', hk2⟩ := hadd ⟨l, r, hkind⟩
  refine Finset.mem_image.mpr ⟨(c, j), ?_, ?_⟩
  · simp only [domain, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_sdiff]
    exact ⟨(mem_additionIds _ _).mpr ⟨_, List.getElem?_eq_getElem hj, l', r', hk2⟩,
      Finset.disjoint_left.mp hdis hlive⟩
  · simp only [SharedPointLocalFamily.support]
    rw [PairedLocalCircuit.support_get _ j hj, PairedLocalCircuit.support_get _ k hklt, hsup]
    rfl

/-! ### The local circuit used by replay -/

theorem src_nodes_map : PairedIndexedGraph.implementation49.nodes.map (PairedRename.node e49) =
    (PairedInitialGraph.circuit (List.range 49)).nodes := by
  rw [PairedIndexedPruning.implementation49_nodes]
  exact PairedIndexedPruning.circuit_nodes_map 49

/-- The sharp count for the pruned structural circuit: at most 450,394
distinct supports over all fifty copies, with no generated witness. -/
theorem support_bound :
    ((SharedPointLocalFamily.domain PairedIndexedPruning.implementation).image
      (SharedPointLocalFamily.support PairedIndexedPruning.implementation)).card ≤ 450394 := by
  obtain ⟨all, hsub, hcard, hdis, hbad⟩ := dead_49
  have hmap := src_nodes_map
  have hlive : PairedIndexedGraph.implementation49.live =
      mark (PairedInitialGraph.circuit (List.range 49)).nodes (outputRefs (List.range 49)).toFinset := by
    rw [PairedLocalCircuit.live, PairedIndexedPruning.roots_eq, map_mark _ _ hmap]
  have hsub' : all ⊆ additionIds PairedIndexedGraph.implementation49.nodes := by
    rw [map_additionIds _ _ hmap]; exact hsub
  have hcount : (additionIds PairedIndexedGraph.implementation49.nodes \ all).card ≤ 9813 := by
    rw [Finset.card_sdiff_of_subset hsub', additionIds_card, map_additionCount _ _ hmap, hcard]
    have := PairedLevelBound.circuit_additions_le
    omega
  unfold PairedIndexedPruning.implementation
  calc _ ≤ ((domain PairedIndexedGraph.implementation49 all).image
          (SharedPointLocalFamily.support PairedIndexedGraph.implementation49)).card :=
        Finset.card_le_card (pruned_subset _ all (hlive ▸ hdis))
    _ ≤ 450394 := image_bound _ _ all hmap
        (PairedInitialGraph.circuit_correct (List.range 49) List.pairwise_lt_range).valid
        (fun v hv xs hx => fam_stored v hv xs hx) hbad hcount

end IntegerMultBounds.Networks.PairedStarShared
