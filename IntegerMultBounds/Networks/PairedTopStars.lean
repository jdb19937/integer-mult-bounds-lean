module

public import IntegerMultBounds.Networks.PairedTopPruning
public import IntegerMultBounds.Networks.PairedStarPresence
import IntegerMultBounds.Networks.PairedLevelTools
import IntegerMultBounds.Networks.PairedBlockCorrect
import IntegerMultBounds.Networks.PairedCoarseQuery
import IntegerMultBounds.Networks.PairedStripSupport
import IntegerMultBounds.Networks.DisjointExclusion

/-! Stars of the top-level strips. With zero vertex weights the strip at a
member `b` of group `i` joins the partner `v` of `b` to the other groups, one
group per value. Its stored prefixes, suffixes, values and omissions are
therefore stars at `v` whose leaves are unions of other groups. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedTopStars

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect PairedLevelTools
open PairedLevelBound PairedTopPruning PairedStarPresence

/-- The edges from `v` to the fine vertices of the coarse groups `js`. -/
def edgesAt (m v : ℕ) (js : List ℕ) : Finset (ℕ × ℕ) :=
  ((List.range (2 * m + 1)).filter (fun x => x / 2 ∈ js)).toFinset.image (fun x => (min v x, max v x))

theorem mem_edgesAt (m v : ℕ) (js : List ℕ) (z : ℕ × ℕ) :
    z ∈ edgesAt m v js ↔ ∃ x, x ≤ 2 * m ∧ x / 2 ∈ js ∧ z = (min v x, max v x) := by
  simp only [edgesAt, Finset.mem_image, List.mem_toFinset, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hj⟩, rfl⟩; exact ⟨x, by omega, hj, rfl⟩
  · rintro ⟨x, hx, hj, rfl⟩; exact ⟨x, ⟨by omega, hj⟩, rfl⟩

/-- Every strip operand group, keyed by the other groups. -/
abbrev Q (m : ℕ) (ia : ℕ × ℕ) : List (List Ref) :=
  stripQueries (oddGroups m) (PairedInitialGraph.edges (P m)) (PairedInitialGraph.weights (P m)) ia

abbrev N0 (m : ℕ) := PairedInitialGraph.nodes (P m)

/-- The other groups of a strip in group `i`. -/
abbrev other (m i : ℕ) : List ℕ := (List.range (m + 1)).filter (· != i)

theorem Q_eq (m i b : ℕ) (hi : i < m) (hb : b = 2 * i ∨ b = 2 * i + 1) :
    Q m (i, b) = [none] :: (other m i).map (fun j =>
      (groupAt (oddGroups m) j).map (edgeLookup (PairedInitialGraph.edges (P m)) (partner i b))) := by
  have hrem : (groupAt (oddGroups m) i).filter (· != b) = [partner i b] := by
    rw [groupAt_lt m i hi]
    rcases hb with rfl | rfl <;> simp [partner]
  simp only [Q, stripQueries, hrem, List.map_cons, List.map_nil, weight_none, oddGroups_length,
    crossRefs_one]

theorem supports_sel (m i b : ℕ) (hi : i < m) (hb : b = 2 * i ∨ b = 2 * i + 1) (js : List ℕ)
    (hjs : ∀ j ∈ js, j ≤ m ∧ j ≠ i) :
    supports (N0 m) (js.map (fun j =>
      (groupAt (oddGroups m) j).map (edgeLookup (PairedInitialGraph.edges (P m)) (partner i b)))).flatten =
      edgesAt m (partner i b) js := by
  have hu := partner_facts i b hb
  ext z
  rw [supports_toFinset, Finset.mem_biUnion, mem_edgesAt]
  simp only [List.mem_toFinset, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨r, ⟨q, ⟨j, hj, rfl⟩, hr⟩, hz⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx' := (mem_groupAt m j x).mp hx
    have hj' := hjs j hj
    rw [edge_support m _ x (by omega) (by omega) (by omega)] at hz
    exact ⟨x, hx'.1, hx'.2 ▸ hj, Finset.mem_singleton.mp hz⟩
  · rintro ⟨x, hx, hj, rfl⟩
    have hj' := hjs _ hj
    refine ⟨edgeLookup (PairedInitialGraph.edges (P m)) (partner i b) x,
      ⟨_, ⟨x / 2, hj, rfl⟩, List.mem_map_of_mem ((mem_groupAt m _ x).mpr ⟨hx, rfl⟩)⟩, ?_⟩
    rw [edge_support m _ x (by omega) (by omega) (by omega)]
    exact Finset.mem_singleton_self _

theorem supports_none_cons (m : ℕ) (qs : List (List Ref)) :
    supports (N0 m) ([none] :: qs).flatten = supports (N0 m) qs.flatten := by
  simp [supports, refSupport]

theorem other_spec (m i : ℕ) (j : ℕ) (hj : j ∈ other m i) : j ≤ m ∧ j ≠ i := by
  simp only [other, List.mem_filter, List.mem_range, bne_iff_ne] at hj
  omega

theorem sub_spec (m i : ℕ) (js : List ℕ) (hs : js.Sublist (other m i)) :
    ∀ j ∈ js, j ≤ m ∧ j ≠ i := fun j hj => other_spec m i j (hs.subset hj)

theorem edgesAt_ne (m v : ℕ) (js : List ℕ) (j : ℕ) (hj : j ∈ js) (hjm : j ≤ m) :
    edgesAt m v js ≠ ∅ := by
  intro he
  have hz := (mem_edgesAt m v js (min v (2 * j), max v (2 * j))).mpr ⟨2 * j, by omega, by
    rw [show 2 * j / 2 = j by omega]; exact hj, rfl⟩
  rw [he] at hz
  simp at hz

theorem other_length (m i : ℕ) (hi : i ≤ m) : (other m i).length = m := by
  have herase : other m i = (List.range (m + 1)).erase i := by
    rw [List.nodup_range.erase_eq_filter]
  rw [herase, List.length_erase_of_mem (List.mem_range.mpr (by omega)), List.length_range]
  omega

/-! ### All top strips are stored in the final circuit -/

theorem forall₂_mem {X Y : Type*} {R : X → Y → Prop} {xs : List X} {ys : List Y}
    (h : List.Forall₂ R xs ys) (x : X) (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hr'⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr'⟩

theorem top_strip_stored (m : ℕ) (hm : 2 ≤ m) (ia : ℕ × ℕ) (hia : ia ∈ members (oddGroups m)) :
    StripStored (N0 m) (Q m ia) (C m) := by
  have hg := PairedInitialGraph.graphReady (P m) List.pairwise_lt_range
  have hc := PairedBlockCorrect.block_correct _ _ _ _ (PairedCoarseCorrect.coarseGraph_ready hg)
  have hr := PairedCoarseQuery.recursive_correct hg (coarse m) hc
  have hb := mapBuild_correct (fun ns ia => buildStrip ns (oddGroups m) (PairedInitialGraph.edges (P m))
      (PairedInitialGraph.weights (P m)) ia)
    (fun ns => Valid ns ∧ Extends (coarse m).nodes ns)
    (fun ia ns (_ : Strip) => StripStored (N0 m) (Q m ia) ns)
    (fun _ _ _ _ he h => stripStored_extends he h)
    (coarse m).nodes (members (oddGroups m)) ⟨hr.valid, extends_refl _⟩ (by
      intro ns hns ia _
      have hq := PairedStripSupport.stripQueries_ready hr.input ia
      have hq0 := PairedStripSupport.stripQueries_ready hg ia
      have hs := buildStrip_stored ns (oddGroups m) (PairedInitialGraph.edges (P m))
        (PairedInitialGraph.weights (P m)) ia hns.1
        (DisjointExclusion.refsValid_extends hns.2 hq.1)
        (DisjointExclusion.disjointRefs_extends hns.2 _ hq.1 hq.2)
      have hbuilt := buildStrip_built ns (oddGroups m) (PairedInitialGraph.edges (P m))
        (PairedInitialGraph.weights (P m)) ia hns.1
        (DisjointExclusion.refsValid_extends hns.2 hq.1)
        (DisjointExclusion.disjointRefs_extends hns.2 _ hq.1 hq.2)
      exact ⟨⟨hbuilt.valid, extends_trans hns.2 hbuilt.extension⟩, hbuilt.extension,
        stripStored_change _ _ (extends_trans hr.extension hns.2) hq0.1 hs⟩)
  obtain ⟨s, -, hs⟩ := forall₂_mem hb.outputs ia hia
  exact stripStored_extends (strips_extends m hm) hs

/-- The stars stored by the strip at member `b` of group `i`, centered at its partner. -/
theorem top_stars (m : ℕ) (hm : 2 ≤ m) (i b : ℕ) (hi : i < m) (hb : b = 2 * i ∨ b = 2 * i + 1) :
    (∀ s, 1 ≤ s → s ≤ (other m i).length →
      Stored (C m) (edgesAt m (partner i b) ((other m i).take s))) ∧
    (∀ d, 1 ≤ d → d < (other m i).length →
      Stored (C m) (edgesAt m (partner i b) ((other m i).drop d))) ∧
    (∀ k < (other m i).length, Stored (C m) (edgesAt m (partner i b) ((other m i).eraseIdx k))) ∧
    (∀ k (hk : k < (other m i).length), Stored (C m) (edgesAt m (partner i b) [(other m i)[k]])) := by
  have hmem : (i, b) ∈ members (oddGroups m) := by
    simp only [members, List.mem_flatMap, List.mem_range, oddGroups_length, List.mem_map]
    refine ⟨i, by omega, b, ?_, rfl⟩
    rw [groupAt_lt m i hi]
    rcases hb with rfl | rfl <;> simp
  have hst := top_strip_stored m hm (i, b) hmem
  rw [Q_eq m i b hi hb] at hst
  let f := fun j => (groupAt (oddGroups m) j).map (edgeLookup (PairedInitialGraph.edges (P m)) (partner i b))
  have hlen := other_length m i (by omega)
  have hsel := fun js hs => supports_sel m i b hi hb js (sub_spec m i js hs)
  have hne := fun js j hj hjs => edgesAt_ne m (partner i b) js j hj (other_spec m i j (List.Sublist.subset hjs hj)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hsl
    have h := hst.prefix_ (s + 1) (by simp only [List.length_cons, List.length_map]; omega)
    rw [List.take_succ_cons, supports_none_cons, ← List.map_take, hsel _ (List.take_sublist _ _)] at h
    obtain ⟨j, hj⟩ : ∃ j, j ∈ (other m i).take s := ⟨(other m i)[0], List.mem_take_iff_getElem.mpr
      ⟨0, by omega, rfl⟩⟩
    exact h (hne _ j hj (List.take_sublist _ _))
  · intro d hd hdl
    have h := hst.suffix (d + 1) (by omega)
    rw [List.drop_succ_cons, ← List.map_drop, hsel _ (List.drop_sublist _ _)] at h
    have hj : (other m i)[d] ∈ (other m i).drop d := by
      rw [List.mem_iff_getElem]; exact ⟨0, by simp; omega, by simp⟩
    exact h (hne _ _ hj (List.drop_sublist _ _))
  · intro k hk
    have h := hst.omission (k + 1) (by omega) (by simp only [List.length_cons, List.length_map]; omega)
    rw [List.eraseIdx_cons_succ, supports_none_cons, List.eraseIdx_map,
      hsel _ (List.eraseIdx_sublist _ _)] at h
    let k' := if k = 0 then 1 else 0
    have hk' : k' < (other m i).length := by simp only [k']; split_ifs <;> omega
    have hj : (other m i)[k'] ∈ (other m i).eraseIdx k := by
      rw [List.mem_eraseIdx_iff_getElem]
      exact ⟨k', hk', by simp only [k']; split_ifs <;> omega, rfl⟩
    exact h (hne _ _ hj (List.eraseIdx_sublist _ _))
  · intro k hk
    have h := hst.value (k + 1) (by simp only [List.length_cons, List.length_map]; omega)
    have he : ([none] :: (other m i).map f)[k + 1]'(by simp only [List.length_cons, List.length_map]; omega) = ([(other m i)[k]].map f).flatten := by
      simp [f]
    rw [he, hsel [(other m i)[k]] (List.singleton_sublist.mpr (List.getElem_mem hk))] at h
    exact h (hne _ _ (List.mem_singleton_self _) (List.singleton_sublist.mpr (List.getElem_mem hk)))

/-! ### Right cross sums -/

theorem mapBuild_stored {X Y : Type*} (f : List (Node PairedInitialGraph.Input) → X →
      List (Node PairedInitialGraph.Input) × Y)
    (hext : ∀ ns x, Extends ns (f ns x).1) (nodes : List (Node PairedInitialGraph.Input)) (xs : List X)
    (S : Finset (ℕ × ℕ)) (x₀ : X) (hx : x₀ ∈ xs)
    (hbody : ∀ ns, Extends nodes ns → Stored (f ns x₀).1 S) : Stored (mapBuild f nodes xs).1 S := by
  induction xs generalizing nodes with
  | nil => simp at hx
  | cons x xs ih =>
    by_cases he : x = x₀
    · subst he
      show Stored (mapBuild f (f nodes x).1 xs).1 S
      exact stored_extends (mapBuild_extends f hext _ _) (hbody nodes (extends_refl _))
    · have hx' : x₀ ∈ xs := by
        rcases List.mem_cons.mp hx with h | h
        · exact False.elim (he h.symm)
        · exact h
      exact ih (f nodes x).1 hx' (fun ns hns => hbody ns (extends_trans (hext nodes x) hns))

/-- The omission of strip `b` for its `k`th other group, in the strip DAG. -/
theorem outside_spec (m i b : ℕ) (hi : i < m) (hb : b = 2 * i ∨ b = 2 * i + 1)
    (k : ℕ) (hk : k < (other m i).length) :
    RefSpec (edgesAt m (partner i b) ((other m i).eraseIdx k)) (strips m).1
      (lookup (stripLookup (strips m).2 b).outside (other m i)[k]) := by
  have hmem : (i, b) ∈ members (oddGroups m) := by
    simp only [members, List.mem_flatMap, List.mem_range, oddGroups_length, List.mem_map]
    refine ⟨i, by omega, b, ?_, rfl⟩
    rw [groupAt_lt m i hi]
    rcases hb with rfl | rfl <;> simp
  have hg := PairedInitialGraph.graphReady (P m) List.pairwise_lt_range
  have hc := PairedBlockCorrect.block_correct _ _ _ _ (PairedCoarseCorrect.coarseGraph_ready hg)
  have hr := PairedCoarseQuery.recursive_correct hg (coarse m) hc
  have hbuilt := buildStrips_built (coarse m).nodes (oddGroups m) (PairedInitialGraph.edges (P m))
    (PairedInitialGraph.weights (P m)) hr.input.valid
    (fun ia _ => (PairedStripSupport.stripQueries_ready hr.input ia).1)
    (fun ia _ => (PairedStripSupport.stripQueries_ready hr.input ia).2)
  have hkeys : ((members (oddGroups m)).map Prod.snd).Nodup := by
    rw [PairedReconstructionKeys.members_groups]; exact List.nodup_range
  have hs := stripLookup_semantics _ _ _ _ _ _ _ hbuilt.2.2 hkeys (i, b) hmem
  have hk' : k < ((List.range (oddGroups m).length).filter (· != (i, b).1)).length := by
    simpa only [oddGroups_length] using hk
  have ho := hs.2.2.2 k hk'
  have hq0 := PairedStripSupport.stripQueries_ready hg (i, b)
  rw [DisjointExclusion.supports_extends hr.extension _ (fun r hm' => hq0.1 r (by
    obtain ⟨q, hq, hrq⟩ := List.mem_flatten.mp hm'
    exact List.mem_flatten.mpr ⟨q, (List.eraseIdx_sublist _ _).subset hq, hrq⟩))] at ho
  simp only [oddGroups_length] at ho
  change RefSpec (supports (N0 m) ((Q m (i, b)).eraseIdx (k + 1)).flatten) _ _ at ho
  rw [Q_eq m i b hi hb, List.eraseIdx_cons_succ, supports_none_cons, List.eraseIdx_map,
    supports_sel m i b hi hb _ (sub_spec m i _ (List.eraseIdx_sublist _ _))] at ho
  exact ho

theorem edge_spec (m u x : ℕ) (hu : u < 2 * m + 1) (hx : x < 2 * m + 1) (hux : u ≠ x) :
    RefSpec {(min u x, max u x)} (N0 m) (edgeLookup (PairedInitialGraph.edges (P m)) u x) := by
  have hp : (min u x, max u x) ∈ pairs (P m) := by rw [pairs_range_mem]; omega
  exact tableSpec_lookup _ _ _ _ (PairedInitialGraph.edges_spec (P m)) _ hp

theorem some_of_ne {nodes : List (Node PairedInitialGraph.Input)} {r : Ref} (h : refSupport nodes r ≠ ∅) :
    ∃ k, r = some k := by
  cases r with
  | none => exact False.elim (h rfl)
  | some k => exact ⟨k, rfl⟩

/-- Right cross support: the omission of group `g` at `b`'s strip, plus the
edge from `v` to the partner of `a`. -/
abbrev crossStar (m : ℕ) (g a i b : ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  edgesAt m (partner i b) ((other m i).eraseIdx k) ∪
    {(min (partner g a) (partner i b), max (partner g a) (partner i b))}

/-- Every right cross sum of the top level is stored. -/
theorem cross_stored (m : ℕ) (hm : 2 ≤ m) (g i : ℕ) (hgi : g < i) (hi : i < m) (a b : ℕ)
    (ha : a = 2 * g ∨ a = 2 * g + 1) (hb : b = 2 * i ∨ b = 2 * i + 1) (k : ℕ)
    (hk : k < (other m i).length) (hkg : (other m i)[k] = g) :
    Stored (C m) (crossStar m g a i b k) := by
  have hg := PairedInitialGraph.graphReady (P m) List.pairwise_lt_range
  have hc := PairedBlockCorrect.block_correct _ _ _ _ (PairedCoarseCorrect.coarseGraph_ready hg)
  have hr := PairedCoarseQuery.recursive_correct hg (coarse m) hc
  have hs0 : Extends (N0 m) (strips m).1 := extends_trans hr.extension
    (mapBuild_extends _ (fun ns ia => buildStrip_extends ns _ _ _ ia) _ _)
  let base := (buildSingles (strips m).1 (oddGroups m) (coarse m).one (strips m).2).1
  have hbase : Extends (strips m).1 base := buildSingles_extends _ _ _ _
  have hout := outside_spec m i b hi hb k hk
  rw [hkg] at hout
  obtain ⟨hpa1, hpa2⟩ := partner_facts g a ha
  obtain ⟨hpb1, hpb2⟩ := partner_facts i b hb
  have hedge := edge_spec m (partner g a) (partner i b) (by omega) (by omega) (by omega)
  show Stored (PairedInitialGraph.circuit (P m)).nodes _
  rw [circuit_eq m hm]
  show Stored (buildCrossPairs base (oddGroups m) (PairedInitialGraph.edges (P m)) (coarse m).two
    (strips m).2).1 _
  unfold buildCrossPairs
  have hgi' : (g, i) ∈ pairs (List.range (oddGroups m).length) := by
    rw [oddGroups_length, pairs_range_mem]; omega
  apply mapBuild_stored _ (fun ns ij => by
    unfold buildCrossGroup
    exact mapBuild_extends _ (fun ns' a => buildCrossLeft_extends _ _ _ _ _ _ _) _ _) _ _ _ _ hgi'
  intro ns hns
  unfold buildCrossGroup
  have hag : a ∈ groupAt (oddGroups m) g := by rw [groupAt_lt m g (by omega)]; rcases ha with rfl | rfl <;> simp
  apply mapBuild_stored _ (fun ns' a => buildCrossLeft_extends _ _ _ _ _ _ _) _ _ _ _ hag
  intro ns' hns'
  unfold buildCrossLeft
  have hbg : b ∈ groupAt (oddGroups m) i := by rw [groupAt_lt m i hi]; rcases hb with rfl | rfl <;> simp
  dsimp only
  refine mapBuild_stored _ ?_ _ _ _ _ hbg ?_
  · intro ns b
    exact extends_trans (total_extends _ _) (extends_trans (smartAdd_extends _ _ _) (smartAdd_extends _ _ _))
  intro ns'' hns''
  have hall : Extends (strips m).1 ns'' := extends_trans hbase (extends_trans hns
    (extends_trans hns' (extends_trans (smartAdd_extends _ _ _) hns'')))
  have hrem1 : (groupAt (oddGroups m) (g, i).1).filter (· != a) = [partner g a] := by
    rw [groupAt_lt m g (by omega)]; rcases ha with rfl | rfl <;> simp [partner]
  have hrem2 : (groupAt (oddGroups m) (g, i).2).filter (· != b) = [partner i b] := by
    rw [groupAt_lt m i hi]; rcases hb with rfl | rfl <;> simp [partner]
  have hcr : DisjointBalanced.total ns'' (crossRefs (PairedInitialGraph.edges (P m))
      ((groupAt (oddGroups m) (g, i).1).filter (· != a)) ((groupAt (oddGroups m) (g, i).2).filter (· != b))) =
      (ns'', edgeLookup (PairedInitialGraph.edges (P m)) (partner g a) (partner i b)) := by
    rw [hrem1, hrem2, crossRefs_one]
    simp [DisjointBalanced.total]
  simp only [hcr]
  have ho := refSpec_extends hall hout
  have he := refSpec_extends (extends_trans hs0 hall) hedge
  have hlen2 : 2 ≤ (other m i).length := by rw [other_length m i (by omega)]; omega
  have hk' : (if k = 0 then 1 else 0) < (other m i).length := by split_ifs <;> omega
  have hmem' : (other m i)[(if k = 0 then 1 else 0)] ∈ (other m i).eraseIdx k := by
    rw [List.mem_eraseIdx_iff_getElem]
    exact ⟨_, hk', by split_ifs <;> omega, rfl⟩
  obtain ⟨k₁, hk₁⟩ := some_of_ne (by
    rw [ho.2]
    exact edgesAt_ne m _ _ _ hmem' (other_spec m i _ (List.getElem_mem hk')).1)
  obtain ⟨k₂, hk₂⟩ := some_of_ne (by rw [he.2]; simp)
  have hm := smartAdd_union_mem ns'' _ _ k₁ k₂ hk₁ hk₂
  rw [ho.2, he.2] at hm
  exact stored_extends (smartAdd_extends _ _ _) hm

end IntegerMultBounds.Networks.PairedTopStars
