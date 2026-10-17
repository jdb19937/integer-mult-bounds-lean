module

public import IntegerMultBounds.Networks.PairedLevelTools
public import IntegerMultBounds.Networks.PairedBaseBound
public import IntegerMultBounds.Networks.PairedBlockCorrect
public import IntegerMultBounds.Networks.PairedInitialBudget

/-! Sharp allocation count of one paired recursion level on an odd interval.
Edges are all present and vertex weights follow a fixed zero pattern. Zero
operands are free, strip rows already built by the coarse edges are reused,
and the remaining stages are charged one addition per present pair. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedLevelBound

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator PairedCircuitCorrect
open PairedLevelTools DisjointSharingBudget

variable {ι : Type*} [DecidableEq ι]

/-- One level's input graph: canonical keys, present edges, and a weight
presence pattern. -/
structure LevelInput (nodes : List (Node ι)) (n : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (wp : ℕ → Bool) : Prop where
  ready : GraphReady nodes (List.range n) edges weights
  edge_keys : edges.map Prod.fst = pairs (List.range n)
  weight_keys : weights.map Prod.fst = List.range n
  edge_present : ∀ e ∈ edges, e.2.isSome = true
  weight_present : ∀ w ∈ weights, w.2.isSome = wp w.1

/-- An allocation budget for every level input of a given size and pattern. -/
def BlockBound (n : ℕ) (wp : ℕ → Bool) (budget : ℕ) : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (nodes : List (Node κ)) (edges : EdgeTable) (weights : WeightTable),
    LevelInput nodes n edges weights wp →
      additionCount (block nodes (List.range n) edges weights).nodes ≤ additionCount nodes + budget

/-! ### Table lookups -/

omit [DecidableEq ι] in
theorem lookup_of_mem_keys {K : Type*} [DecidableEq K] (table : List (K × Ref)) (k : K)
    (hk : k ∈ table.map Prod.fst) : ∃ e ∈ table, e.1 = k ∧ lookup table k = e.2 := by
  induction table with
  | nil => simp at hk
  | cons e table ih =>
    by_cases he : e.1 = k
    · exact ⟨e, by simp, he, by simp [lookup, he]⟩
    · have hk' : k ∈ table.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hk
        exact hk.resolve_left (Ne.symm he)
      obtain ⟨e', hm, h1, h2⟩ := ih hk'
      exact ⟨e', by simp [hm], h1, by simp [lookup, he] at h2 ⊢; exact h2⟩

theorem edge_lookup (nodes : List (Node ι)) (n : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (wp : ℕ → Bool) (h : LevelInput nodes n edges weights wp) (a b : ℕ) (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : ∃ i, edgeLookup edges a b = some i ∧ i < nodes.length := by
  have hp : (min a b, max a b) ∈ edges.map Prod.fst := by
    rw [h.edge_keys, pairs_mem _ List.pairwise_lt_range]
    simp only [List.mem_range]
    omega
  obtain ⟨e, he, -, hl⟩ := lookup_of_mem_keys edges _ hp
  have hs := h.edge_present e he
  have hv := h.ready.refsValid e.2 (List.mem_append_left _ (List.mem_map_of_mem he))
  unfold edgeLookup
  rw [hl]
  cases he2 : e.2 with
  | none => rw [he2] at hs; simp at hs
  | some i => rw [he2] at hv; exact ⟨i, rfl, hv⟩

theorem weight_lookup (nodes : List (Node ι)) (n : ℕ) (edges : EdgeTable) (weights : WeightTable)
    (wp : ℕ → Bool) (h : LevelInput nodes n edges weights wp) (a : ℕ) (ha : a < n) :
    (lookup weights a).isSome = wp a ∧ RefValid nodes (lookup weights a) := by
  have hp : a ∈ weights.map Prod.fst := by rw [h.weight_keys]; exact List.mem_range.mpr ha
  obtain ⟨w, hw, hk, hl⟩ := lookup_of_mem_keys weights _ hp
  rw [hl]
  refine ⟨by rw [h.weight_present w hw, hk], ?_⟩
  exact h.ready.refsValid w.2 (List.mem_append_right _ (List.mem_map_of_mem hw))

/-! ### All-zero strips -/

theorem prefixBuild_zero (nodes : List (Node ι)) (refs : List Ref) (h : ∀ r ∈ refs, r = none) :
    prefixBuild nodes none refs = (nodes, List.replicate (refs.length + 1) none) := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    rw [h r (by simp)]
    simp only [prefixBuild, smartAdd, ih (fun x hx => h x (by simp [hx])), List.length_cons,
      List.replicate_succ]

theorem suffixBuild_zero (nodes : List (Node ι)) (refs : List Ref) (h : ∀ r ∈ refs, r = none) :
    suffixBuild nodes refs = (nodes, List.replicate (refs.length + 1) none) := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    rw [h r (by simp)]
    simp only [suffixBuild, ih (fun x hx => h x (by simp [hx])), List.length_cons,
      List.replicate_succ, List.headD_cons, smartAdd]

theorem addPairs_zero (nodes : List (Node ι)) (ps : List (Ref × Ref))
    (h : ∀ p ∈ ps, p.1 = none ∧ p.2 = none) :
    mapBuild (fun ns p => smartAdd ns p.1 p.2) nodes ps = (nodes, List.replicate ps.length none) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨h1, h2⟩ := h p (by simp)
    have hih := ih (fun q hq => h q (by simp [hq]))
    have hz : smartAdd nodes p.1 p.2 = (nodes, none) := by rw [h1, h2]; rfl
    simp only [mapBuild, hz, hih, List.length_cons, List.replicate_succ]

/-- A vector of zeros builds nothing and returns only zeros. -/
theorem vectorTail_zero (nodes : List (Node ι)) (refs : List Ref) (h : ∀ r ∈ refs, r = none) :
    (vectorTail nodes refs).nodes = nodes ∧ (vectorTail nodes refs).total = none ∧
      ∀ r ∈ (vectorTail nodes refs).one, r = none := by
  cases refs with
  | nil => exact ⟨rfl, rfl, by simp [vectorTail]⟩
  | cons c vs =>
    have hvs : ∀ r ∈ vs, r = none := fun r hr => h r (by simp [hr])
    have hp := prefixBuild_zero nodes (c :: vs) h
    have hs := suffixBuild_zero nodes vs.tail (fun r hr => hvs r (List.mem_of_mem_tail hr))
    have hz : ∀ p ∈ (((prefixBuild nodes none (c :: vs)).2.drop 1).zip
        ((suffixBuild (prefixBuild nodes none (c :: vs)).1 vs.tail).2.take vs.length)),
        p.1 = none ∧ p.2 = none := by
      intro p hpm
      rw [hp, hs] at hpm
      have hh := List.of_mem_zip hpm
      exact ⟨List.eq_of_mem_replicate (List.mem_of_mem_drop hh.1),
        List.eq_of_mem_replicate (List.mem_of_mem_take hh.2)⟩
    simp only [vectorTail]
    rw [addPairs_zero _ _ hz]
    rw [hp] at hz ⊢
    rw [hs]
    refine ⟨rfl, ?_, ?_⟩
    · simp [List.getLast?_replicate]
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rfl
      · exact List.eq_of_mem_replicate hr

/-! ### Groups of an odd interval -/

/-- Weight pattern: all zero at the top level, otherwise zero only at the end. -/
def pattern (m : ℕ) (top : Bool) (a : ℕ) : Bool := !top && decide (a < 2 * m)

abbrev oddGroups (m : ℕ) : List (List ℕ) := PairGrouping.groups (List.range (2 * m + 1))

theorem oddGroups_length (m : ℕ) : (oddGroups m).length = m + 1 := by
  rw [oddGroups, PairGrouping.length_groups, List.length_range]; omega

theorem groupAt_lt (m i : ℕ) (hi : i < m) : groupAt (oddGroups m) i = [2 * i, 2 * i + 1] := by
  simp only [groupAt, oddGroups, groups_range_odd]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem groupAt_last (m : ℕ) : groupAt (oddGroups m) m = [2 * m] := by
  simp only [groupAt, oddGroups, groups_range_odd]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem mem_members (m : ℕ) (ia : ℕ × ℕ) (h : ia ∈ members (oddGroups m)) :
    (ia.1 < m ∧ (ia.2 = 2 * ia.1 ∨ ia.2 = 2 * ia.1 + 1)) ∨ (ia.1 = m ∧ ia.2 = 2 * m) := by
  simp only [members, List.mem_flatMap, List.mem_map, List.mem_range, oddGroups_length] at h
  obtain ⟨i, hi, a, ha, rfl⟩ := h
  by_cases him : i < m
  · rw [groupAt_lt m i him] at ha
    left
    simpa [him] using ha
  · have hi' : i = m := by omega
    subst hi'
    rw [groupAt_last] at ha
    right
    simpa using ha

theorem crossRefs_one (edges : EdgeTable) (u : ℕ) (right : List ℕ) :
    crossRefs edges [u] right = right.map (edgeLookup edges u) := by
  simp [crossRefs]

/-! ### Strips -/

/-- Rows already stored by the coarse edges between two pair groups. -/
def RowsStored (nodes : List (Node ι)) (edges : EdgeTable) (m : ℕ) (stored : List (Node ι)) : Prop :=
  ∀ i j, i < j → j < m → ∀ a ∈ [2 * i, 2 * i + 1],
    refSupport nodes (edgeLookup edges a (2 * j)) ∪ refSupport nodes (edgeLookup edges a (2 * j + 1)) ∈
      stored.map Node.support

/-- Strip cost: one addition per row toward an earlier pair group, plus the
vector; the last vertex's strip is empty. -/
def stripCost (m : ℕ) (top : Bool) (ia : ℕ × ℕ) : ℕ :=
  if ia.1 < m then
    (((List.range (m + 1)).filter (· != ia.1)).map (fun j => if j < ia.1 then 1 else 0)).sum +
      (if top then 3 * m - 5 else 3 * m - 3)
  else 0

theorem other_eq (m i : ℕ) : (List.range (m + 1)).filter (· != i) = (List.range (m + 1)).erase i := by
  rw [List.Nodup.erase_eq_filter List.nodup_range]

theorem other_length (m i : ℕ) (hi : i ≤ m) :
    ((List.range (m + 1)).filter (· != i)).length = m := by
  rw [other_eq, List.length_erase_of_mem (List.mem_range.mpr (by omega)), List.length_range]
  omega

omit [DecidableEq ι] in
theorem forall_of_forall₂ {X Y : Type*} {P : Y → Prop} {xs : List X} {ys : List Y}
    (h : List.Forall₂ (fun _ y => P y) xs ys) : ∀ y ∈ ys, P y := by
  induction h with
  | nil => simp
  | cons hy _ ih =>
    intro y hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hy
    · exact ih y hm

theorem groupAt_cases (m j : ℕ) (hj : j ≤ m) :
    (j < m ∧ groupAt (oddGroups m) j = [2 * j, 2 * j + 1]) ∨
      (j = m ∧ groupAt (oddGroups m) j = [2 * m]) := by
  by_cases h : j < m
  · exact Or.inl ⟨h, groupAt_lt m j h⟩
  · have : j = m := by omega
    subst this
    exact Or.inr ⟨rfl, groupAt_last j⟩

/-- A pair-group member's strip: rows toward later pair groups are reused,
and the vector costs 3m-5 or 3m-3 depending on whether the carry is zero. -/
theorem strip_pair_bound (m : ℕ) (hm : 2 ≤ m) (top : Bool) (nodes : List (Node ι))
    (edges : EdgeTable) (weights : WeightTable)
    (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (stored : List (Node ι)) (hrows : RowsStored nodes edges m stored) (hstored : Extends nodes stored)
    (ns : List (Node ι)) (hns : Extends stored ns) (i a : ℕ) (hi : i < m)
    (ha : a = 2 * i ∨ a = 2 * i + 1) :
    additionCount (buildStrip ns (oddGroups m) edges weights (i, a)).1 ≤
      additionCount ns + stripCost m top (i, a) := by
  let u := if a = 2 * i then 2 * i + 1 else 2 * i
  have hu : u = 2 * i ∨ u = 2 * i + 1 := by
    simp only [u]; split_ifs <;> simp
  have hrem : (groupAt (oddGroups m) i).filter (· != a) = [u] := by
    rw [groupAt_lt m i hi]
    rcases ha with rfl | rfl <;> simp [u]
  let other := (List.range (m + 1)).filter (· != i)
  let body := fun (ns : List (Node ι)) (j : ℕ) =>
    DisjointBalanced.total ns (crossRefs edges [u] (groupAt (oddGroups m) j))
  have hb : (buildStrip ns (oddGroups m) edges weights (i, a)).1 =
      (vectorTail (mapBuild body ns other).1 (lookup weights u :: (mapBuild body ns other).2)).nodes := by
    simp only [buildStrip, hrem, List.map_cons, List.map_nil, oddGroups_length]
    simp [DisjointBalanced.total, body, other]
  rw [hb]
  have hother : ∀ j ∈ other, j ≠ i ∧ j ≤ m := by
    intro j hj
    simp only [other, List.mem_filter, List.mem_range, bne_iff_ne] at hj
    exact ⟨hj.2, by omega⟩
  have hedge : ∀ j ∈ other, ∀ b ∈ groupAt (oddGroups m) j,
      ∃ k, edgeLookup edges u b = some k ∧ k < nodes.length := by
    intro j hj b hb'
    obtain ⟨hji, hjm⟩ := hother j hj
    apply edge_lookup nodes (2 * m + 1) edges weights _ h u b (by omega)
    · rcases groupAt_cases m j hjm with ⟨_, hg⟩ | ⟨_, hg⟩ <;> rw [hg] at hb' <;> simp at hb' <;> omega
    · rcases groupAt_cases m j hjm with ⟨_, hg⟩ | ⟨rfl, hg⟩ <;> rw [hg] at hb' <;> simp at hb' <;> omega
  -- the cross-group values
  have hvals : additionCount (mapBuild body ns other).1 ≤ additionCount ns +
      (other.map (fun j => if j < i then 1 else 0)).sum := by
    apply mapBuild_additions_le_inv body _ (fun ns' => Extends stored ns') other
    · intro ns' j _ he
      exact extends_trans he (total_extends _ _)
    · intro ns' j hj he
      obtain ⟨hji, hjm⟩ := hother j hj
      simp only [body]
      rcases groupAt_cases m j hjm with ⟨hjm', hg⟩ | ⟨hjeq, hg⟩
      · rw [hg, crossRefs_one]
        simp only [List.map_cons, List.map_nil]
        by_cases hlt : j < i
        · have hl := PairedCircuitBudget.total_additions_le ns'
            [edgeLookup edges u (2 * j), edgeLookup edges u (2 * j + 1)]
          simp only [hlt, ↓reduceIte, List.length_cons, List.length_nil] at hl ⊢
          omega
        · obtain ⟨k₁, hk₁, hk₁l⟩ := hedge j hj (2 * j) (by rw [hg]; simp)
          obtain ⟨k₂, hk₂, hk₂l⟩ := hedge j hj (2 * j + 1) (by rw [hg]; simp)
          have hrow := hrows i j (by omega) hjm' u (by rcases hu with h' | h' <;> simp [h'])
          have he' := extends_trans hstored he
          have hx := refSupport_extends he' (show RefValid nodes (edgeLookup edges u (2 * j)) by
            rw [hk₁]; exact hk₁l)
          have hy := refSupport_extends he' (show RefValid nodes (edgeLookup edges u (2 * j + 1)) by
            rw [hk₂]; exact hk₂l)
          have hmem : refSupport ns' (edgeLookup edges u (2 * j)) ∪
              refSupport ns' (edgeLookup edges u (2 * j + 1)) ∈ ns'.map Node.support := by
            rw [hx, hy]
            obtain ⟨tail, rfl⟩ := he
            rw [List.map_append]
            exact List.mem_append_left _ hrow
          have hfree := PairedVectorBudget.smartAdd_additions_of_union_mem ns' _ _ hmem
          have heq : DisjointBalanced.total ns' [edgeLookup edges u (2 * j), edgeLookup edges u (2 * j + 1)] =
              smartAdd ns' (edgeLookup edges u (2 * j)) (edgeLookup edges u (2 * j + 1)) := by
            simp [DisjointBalanced.total]
          rw [heq, hfree]
          simp [hlt]
      · rw [hg, crossRefs_one]
        simp [DisjointBalanced.total]
    · exact hns
  -- every value is present
  have hpres : ∀ r ∈ (mapBuild body ns other).2, r.isSome = true := by
    refine forall_of_forall₂ (mapBuild_forall₂ body (fun _ r => r.isSome = true) other ?_ ns)
    intro ns' j hj
    apply PairedPresence.total_isSome
    obtain ⟨_, hjm⟩ := hother j hj
    have hne : groupAt (oddGroups m) j ≠ [] := by
      rcases groupAt_cases m j hjm with ⟨_, hg⟩ | ⟨_, hg⟩ <;> rw [hg] <;> simp
    obtain ⟨b, hb'⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨k, hk, -⟩ := hedge j hj b hb'
    unfold presentCount
    rw [crossRefs_one]
    apply List.countP_pos_iff.mpr
    exact ⟨edgeLookup edges u b, List.mem_map_of_mem hb', by rw [hk]; rfl⟩
  have hlen : (mapBuild body ns other).2.length = m := by
    rw [mapBuild_length]; exact other_length m i (by omega)
  have hwu := (weight_lookup nodes _ edges weights _ h u (by omega)).1
  have hcost : stripCost m top (i, a) = (other.map (fun j => if j < i then 1 else 0)).sum +
      (if top then 3 * m - 5 else 3 * m - 3) := by
    simp [stripCost, hi, other]
  rw [hcost]
  cases top with
  | true =>
    have hnone : lookup weights u = none := by
      simp only [pattern, Bool.not_true, Bool.false_and] at hwu
      cases hl : lookup weights u <;> simp_all
    rw [hnone]
    have hv := PairedVectorBudget.vectorTail_cons_none_additions_le_sharp (mapBuild body ns other).1 _ hpres (by omega)
    rw [hlen] at hv
    simp only [↓reduceIte]
    omega
  | false =>
    have hsome : (lookup weights u).isSome = true := by
      rw [hwu]; simp only [pattern]; rcases hu with h' | h' <;> simp [h'] <;> omega
    have hv := PairedVectorBudget.vectorTail_additions_le_sharp (mapBuild body ns other).1
      (lookup weights u :: (mapBuild body ns other).2) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hsome
        · exact hpres r hr) (by simp only [List.length_cons, hlen]; omega)
    simp only [List.length_cons, hlen] at hv
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

omit [DecidableEq ι] in
theorem lookup_zero {K : Type*} [DecidableEq K] (table : List (K × Ref))
    (h : ∀ e ∈ table, e.2 = none) (k : K) : lookup table k = none := by
  induction table with
  | nil => rfl
  | cons e table ih =>
    by_cases he : e.1 = k
    · simp [lookup, he, h e (by simp)]
    · simpa [lookup, he] using ih (fun x hx => h x (by simp [hx]))

omit [DecidableEq ι] in
theorem mapBuild_const_none {X : Type*} (f : List (Node ι) → X → List (Node ι) × Ref)
    (hf : ∀ ns x, f ns x = (ns, none)) (nodes : List (Node ι)) (xs : List X) :
    mapBuild f nodes xs = (nodes, List.replicate xs.length none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mapBuild, hf, ih, List.length_cons, List.replicate_succ]

theorem total_nil (nodes : List (Node ι)) : DisjointBalanced.total nodes ([] : List Ref) = (nodes, none) := by
  simp [DisjointBalanced.total]

theorem mapBuild_total_nil {X : Type*} (nodes : List (Node ι)) (xs : List X) :
    mapBuild (fun ns (_ : X) => DisjointBalanced.total ns ([] : List Ref)) nodes xs =
      (nodes, List.replicate xs.length none) :=
  mapBuild_const_none _ (fun ns _ => total_nil ns) nodes xs

/-- The last vertex is alone in its group: its strip is empty. -/
theorem strip_last (m : ℕ) (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable) :
    (buildStrip nodes (oddGroups m) edges weights (m, 2 * m)).1 = nodes ∧
      (buildStrip nodes (oddGroups m) edges weights (m, 2 * m)).2.total = none ∧
      ∀ k, lookup (buildStrip nodes (oddGroups m) edges weights (m, 2 * m)).2.outside k = none := by
  have hrem : (groupAt (oddGroups m) m).filter (· != 2 * m) = [] := by
    rw [groupAt_last]; simp
  have hcross : ∀ g, crossRefs edges [] g = [] := fun g => by simp [crossRefs]
  let other := (List.range (oddGroups m).length).filter (· != m)
  have hz := vectorTail_zero nodes (none :: List.replicate other.length none) (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rfl
    · exact List.eq_of_mem_replicate hr)
  have hb : buildStrip nodes (oddGroups m) edges weights (m, 2 * m) =
      ((vectorTail nodes (none :: List.replicate other.length none)).nodes,
        ⟨2 * m, (vectorTail nodes (none :: List.replicate other.length none)).total,
          other.zip (vectorTail nodes (none :: List.replicate other.length none)).one.tail⟩) := by
    simp only [buildStrip, hrem, List.map_nil, hcross]
    rw [total_nil, mapBuild_total_nil]
  rw [hb]
  refine ⟨hz.1, hz.2.1, fun k => lookup_zero _ (fun e he => ?_) k⟩
  exact hz.2.2 _ (List.mem_of_mem_tail (List.of_mem_zip he).2)

/-- What the later stages need from each strip. -/
def StripPost (m : ℕ) (ia : ℕ × ℕ) (s : Strip) : Prop :=
  s.vertex = ia.2 ∧ (ia = (m, 2 * m) → s.total = none ∧ ∀ k, lookup s.outside k = none)

theorem strips_post (m : ℕ) (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable) :
    List.Forall₂ (StripPost m) (members (oddGroups m)) (buildStrips nodes (oddGroups m) edges weights).2 := by
  apply mapBuild_forall₂
  intro ns ia _
  refine ⟨rfl, ?_⟩
  rintro rfl
  exact (strip_last m ns edges weights).2

theorem strip_lookup (m : ℕ) (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable)
    (ia : ℕ × ℕ) (hia : ia ∈ members (oddGroups m)) :
    StripPost m ia (stripLookup (buildStrips nodes (oddGroups m) edges weights).2 ia.2) := by
  apply stripLookup_of_forall₂ (StripPost m) (fun _ _ h => h.1) _ _ (strips_post m nodes edges weights)
    _ ia hia
  rw [PairedReconstructionKeys.members_groups]
  exact List.nodup_range

theorem strips_additions_le (m : ℕ) (hm : 2 ≤ m) (top : Bool) (nodes : List (Node ι))
    (edges : EdgeTable) (weights : WeightTable)
    (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (stored : List (Node ι)) (hrows : RowsStored nodes edges m stored) (hstored : Extends nodes stored)
    (ns : List (Node ι)) (hns : Extends stored ns) :
    additionCount (buildStrips ns (oddGroups m) edges weights).1 ≤
      additionCount ns + ((members (oddGroups m)).map (stripCost m top)).sum := by
  apply mapBuild_additions_le_inv _ _ (fun ns' => Extends stored ns') _
  · intro ns' ia _ he
    exact extends_trans he (buildStrip_extends _ _ _ _ _)
  · intro ns' ia hia he
    rcases mem_members m ia hia with ⟨hi, ha⟩ | ⟨hi, ha⟩
    · have hia' : ia = (ia.1, ia.2) := rfl
      rw [hia']
      exact strip_pair_bound m hm top nodes edges weights h stored hrows hstored ns' he ia.1 ia.2 hi ha
    · have hia' : ia = (m, 2 * m) := Prod.ext hi ha
      rw [hia', (strip_last m ns' edges weights).1]
      simp [stripCost]
  · exact hns

/-! ### Singles and cross pairs -/

def singleCost (m : ℕ) (ia : ℕ × ℕ) : ℕ := if ia = (m, 2 * m) then 0 else 1

theorem singles_additions_le (m : ℕ) (_nodes : List (Node ι)) (edges : EdgeTable)
    (weights : WeightTable) (base : List (Node ι)) (outside : WeightTable) (ns : List (Node ι)) :
    additionCount (buildSingles ns (oddGroups m) outside
        (buildStrips base (oddGroups m) edges weights).2).1 ≤
      additionCount ns + ((members (oddGroups m)).map (singleCost m)).sum := by
  apply mapBuild_additions_le_inv _ _ (fun _ => True) _ (fun _ _ _ _ => trivial) _ _ trivial
  intro ns' ia hia _
  by_cases hl : ia = (m, 2 * m)
  · have hp := (strip_lookup m base edges weights ia hia).2 hl
    subst hl
    simp only [singleCost, ↓reduceIte]
    simp only [hp.1]
    cases lookup outside m <;> simp [smartAdd]
  · simp only [singleCost, hl, ↓reduceIte]
    exact PairedCircuitBudget.smartAdd_additions_le _ _ _

def crossCost (m : ℕ) (ij : ℕ × ℕ) : ℕ :=
  (groupAt (oddGroups m) ij.1).length *
    (1 + (if ij.2 < m then 2 * (groupAt (oddGroups m) ij.2).length else 0))

omit [DecidableEq ι] in
@[simp] theorem smartAdd_none_right' (nodes : List (Node ι)) (l : Ref) [DecidableEq ι] :
    smartAdd nodes l none = (nodes, l) := by cases l <;> rfl

theorem chain_le (ns : List (Node ι)) (c : List (Node ι) × Ref) (x y : Ref)
    (hc : additionCount c.1 ≤ additionCount ns) :
    additionCount (smartAdd (smartAdd c.1 x c.2).1 y (smartAdd c.1 x c.2).2).1 ≤
      additionCount ns + 2 := by
  have h1 := PairedCircuitBudget.smartAdd_additions_le c.1 x c.2
  have h2 := PairedCircuitBudget.smartAdd_additions_le (smartAdd c.1 x c.2).1 y (smartAdd c.1 x c.2).2
  omega

theorem crossLeft_additions_le (m : ℕ) (edges far : EdgeTable)
    (weights : WeightTable) (base : List (Node ι)) (ns : List (Node ι)) (ij : ℕ × ℕ)
    (hij : ij ∈ pairs (List.range (m + 1))) (a : ℕ) (ha : a ∈ groupAt (oddGroups m) ij.1) :
    additionCount (buildCrossLeft ns (oddGroups m) edges far
        (buildStrips base (oddGroups m) edges weights).2 ij a).1 ≤
      additionCount ns + (1 + (if ij.2 < m then 2 * (groupAt (oddGroups m) ij.2).length else 0)) := by
  have hp := (pairs_mem _ List.pairwise_lt_range ij.1 ij.2).mp hij
  simp only [List.mem_range] at hp
  have hi : ij.1 < m := by omega
  let strips := (buildStrips base (oddGroups m) edges weights).2
  have hl := PairedCircuitBudget.smartAdd_additions_le ns (lookup far ij) (lookup (stripLookup strips a).outside ij.2)
  have hloop := mapBuild_additions_le_inv (fun cur b =>
      let cross := DisjointBalanced.total cur (crossRefs edges
        ((groupAt (oddGroups m) ij.1).filter (· != a)) ((groupAt (oddGroups m) ij.2).filter (· != b)))
      let right := smartAdd cross.1 (lookup (stripLookup strips b).outside ij.1) cross.2
      let result := smartAdd right.1 (smartAdd ns (lookup far ij) (lookup (stripLookup strips a).outside ij.2)).2 right.2
      (result.1, ((a, b), result.2)))
    (fun _ => if ij.2 < m then 2 else 0) (fun _ => True) (groupAt (oddGroups m) ij.2)
    (fun _ _ _ _ => trivial) (by
      intro ns' b hb _
      have hai : ((groupAt (oddGroups m) ij.1).filter (· != a)).length ≤ 1 := by
        rw [groupAt_lt m ij.1 hi] at ha ⊢
        simp at ha
        rcases ha with rfl | rfl <;> simp
      by_cases hj : ij.2 < m
      · have hbj : ((groupAt (oddGroups m) ij.2).filter (· != b)).length ≤ 1 := by
          rw [groupAt_lt m ij.2 hj] at hb ⊢
          simp at hb
          rcases hb with rfl | rfl <;> simp
        have hc := PairedCircuitBudget.total_additions_le ns' (crossRefs edges
          ((groupAt (oddGroups m) ij.1).filter (· != a)) ((groupAt (oddGroups m) ij.2).filter (· != b)))
        rw [PairedCircuitBudget.crossRefs_length] at hc
        have hmul : ((groupAt (oddGroups m) ij.1).filter (· != a)).length *
            ((groupAt (oddGroups m) ij.2).filter (· != b)).length ≤ 1 :=
          (Nat.mul_le_mul hai hbj).trans (by norm_num)
        have hc' : additionCount (DisjointBalanced.total ns' (crossRefs edges
            ((groupAt (oddGroups m) ij.1).filter (· != a))
            ((groupAt (oddGroups m) ij.2).filter (· != b)))).1 ≤ additionCount ns' := by omega
        simp only [hj, ↓reduceIte]
        exact chain_le _ _ _ _ hc'
      · have hjm : ij.2 = m := by omega
        have hbm : b = 2 * m := by
          rw [hjm, groupAt_last] at hb; simpa using hb
        have hmem : (m, 2 * m) ∈ members (oddGroups m) := by
          simp only [members, List.mem_flatMap, List.mem_range, oddGroups_length, List.mem_map]
          exact ⟨m, by omega, 2 * m, by rw [groupAt_last]; simp, rfl⟩
        have hpost := (strip_lookup m base edges weights (m, 2 * m) hmem).2 rfl
        have hempty : (groupAt (oddGroups m) m).filter (· != 2 * m) = [] := by
          rw [groupAt_last]; simp
        simp only [hbm, hjm]
        rw [hempty]
        have hc : crossRefs edges ((groupAt (oddGroups m) ij.1).filter (· != a)) [] = [] := by
          simp [crossRefs]
        rw [hc, total_nil]
        have hz : lookup (stripLookup strips (2 * m)).outside ij.1 = none := hpost.2 ij.1
        simp only [hz, smartAdd_none_right']
        simp) (smartAdd ns (lookup far ij) (lookup (stripLookup strips a).outside ij.2)).1 trivial
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hloop
  refine (le_of_eq (rfl : _ = _)).trans (hloop.trans ?_)
  split_ifs with hj
  · rw [Nat.mul_comm]; omega
  · omega

theorem crossPairs_additions_le (m : ℕ) (edges far : EdgeTable) (weights : WeightTable)
    (base : List (Node ι)) (ns : List (Node ι)) :
    additionCount (buildCrossPairs ns (oddGroups m) edges far
        (buildStrips base (oddGroups m) edges weights).2).1 ≤
      additionCount ns + ((pairs (List.range (m + 1))).map (crossCost m)).sum := by
  unfold buildCrossPairs
  rw [oddGroups_length]
  apply mapBuild_additions_le_inv _ _ (fun _ => True) _ (fun _ _ _ _ => trivial) _ _ trivial
  intro ns' ij hij _
  unfold buildCrossGroup
  have h := mapBuild_additions_le_inv _ (fun _ => 1 + (if ij.2 < m then 2 * (groupAt (oddGroups m) ij.2).length else 0))
    (fun _ => True) (groupAt (oddGroups m) ij.1) (fun _ _ _ _ => trivial)
    (fun ns'' a ha _ => crossLeft_additions_le m edges far weights base ns'' ij hij a ha) ns' trivial
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h
  exact h

/-! ### Coarse stages -/

theorem smartAdd_union_mem (nodes : List (Node ι)) (x y : Ref) (k₁ k₂ : ℕ)
    (hx : x = some k₁) (hy : y = some k₂) :
    refSupport nodes x ∪ refSupport nodes y ∈ (smartAdd nodes x y).1.map Node.support := by
  subst hx; subst hy
  exact List.mem_of_getElem? (intern_support nodes _)

omit [DecidableEq ι] in
theorem mem_supports_extends {ns ns' : List (Node ι)} (he : Extends ns ns') {s : Finset ι}
    (h : s ∈ ns.map Node.support) : s ∈ ns'.map Node.support := by
  obtain ⟨tail, rfl⟩ := he
  rw [List.map_append]
  exact List.mem_append_left _ h

omit [DecidableEq ι] in
/-- A monotone fact established by some loop iteration survives the loop. -/
theorem mapBuild_establish (f : List (Node ι) → X → List (Node ι) × Y)
    (Q : X → List (Node ι) → Prop) (hQ : ∀ x ns ns', Extends ns ns' → Q x ns → Q x ns')
    (hext : ∀ ns x, Extends ns (f ns x).1) (xs : List X) (base : List (Node ι))
    (hbody : ∀ ns, Extends base ns → ∀ x ∈ xs, Q x (f ns x).1) (nodes : List (Node ι))
    (hn : Extends base nodes) :
    ∀ x ∈ xs, Q x (mapBuild f nodes xs).1 := by
  induction xs generalizing nodes with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · show Q y (mapBuild f (f nodes y).1 xs).1
      exact hQ _ _ _ (mapBuild_extends f hext _ _) (hbody nodes hn y (by simp))
    · exact ih (fun ns hb z hz => hbody ns hb z (by simp [hz])) _
        (extends_trans hn (hext _ _)) y hy

theorem coarse_rows (m : ℕ) (top : Bool) (nodes : List (Node ι)) (edges : EdgeTable)
    (weights : WeightTable) (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top)) :
    RowsStored nodes edges m (coarseEdges nodes (oddGroups m) edges).1 := by
  intro i j hij hjm a ha
  have hmem : (i, j) ∈ pairs (List.range (oddGroups m).length) := by
    rw [oddGroups_length, pairs_mem _ List.pairwise_lt_range]
    simp only [List.mem_range]; omega
  let Q := fun (p : ℕ × ℕ) (ns : List (Node ι)) => p.1 < m → p.2 < m → p.1 < p.2 →
    ∀ a ∈ [2 * p.1, 2 * p.1 + 1], refSupport nodes (edgeLookup edges a (2 * p.2)) ∪
      refSupport nodes (edgeLookup edges a (2 * p.2 + 1)) ∈ ns.map Node.support
  have hQ : ∀ p ns ns', Extends ns ns' → Q p ns → Q p ns' :=
    fun p ns ns' he hq h1 h2 h3 a ha => mem_supports_extends he (hq h1 h2 h3 a ha)
  have key := mapBuild_establish (fun ns (p : ℕ × ℕ) =>
      let r := DisjointBalanced.total ns (crossRefs edges (groupAt (oddGroups m) p.1)
        (groupAt (oddGroups m) p.2))
      (r.1, (p, r.2))) Q hQ (fun ns p => total_extends ns _)
    (pairs (List.range (oddGroups m).length)) nodes (by
    intro ns hns p _ h1 h2 h3 a ha
    have hga := groupAt_lt m p.1 h1
    have hgb := groupAt_lt m p.2 h2
    have hl (x y : ℕ) (hx : x < 2 * m + 1) (hy : y < 2 * m + 1) (hxy : x ≠ y) :=
      edge_lookup nodes _ edges weights _ h x y hx hy hxy
    obtain ⟨k₁, h₁, l₁⟩ := hl (2 * p.1) (2 * p.2) (by omega) (by omega) (by omega)
    obtain ⟨k₂, h₂, l₂⟩ := hl (2 * p.1) (2 * p.2 + 1) (by omega) (by omega) (by omega)
    obtain ⟨k₃, h₃, l₃⟩ := hl (2 * p.1 + 1) (2 * p.2) (by omega) (by omega) (by omega)
    obtain ⟨k₄, h₄, l₄⟩ := hl (2 * p.1 + 1) (2 * p.2 + 1) (by omega) (by omega) (by omega)
    have hcr : crossRefs edges (groupAt (oddGroups m) p.1) (groupAt (oddGroups m) p.2) =
        [edgeLookup edges (2 * p.1) (2 * p.2), edgeLookup edges (2 * p.1) (2 * p.2 + 1),
          edgeLookup edges (2 * p.1 + 1) (2 * p.2), edgeLookup edges (2 * p.1 + 1) (2 * p.2 + 1)] := by
      rw [hga, hgb]; simp [crossRefs]
    show refSupport nodes _ ∪ refSupport nodes _ ∈
      (DisjointBalanced.total ns (crossRefs edges (groupAt (oddGroups m) p.1)
        (groupAt (oddGroups m) p.2))).1.map Node.support
    rw [hcr]
    let x₁ := edgeLookup edges (2 * p.1) (2 * p.2)
    let x₂ := edgeLookup edges (2 * p.1) (2 * p.2 + 1)
    let x₃ := edgeLookup edges (2 * p.1 + 1) (2 * p.2)
    let x₄ := edgeLookup edges (2 * p.1 + 1) (2 * p.2 + 1)
    have he4 : DisjointBalanced.total ns [x₁, x₂, x₃, x₄] =
        smartAdd (smartAdd (smartAdd ns x₁ x₂).1 x₃ x₄).1 (smartAdd ns x₁ x₂).2
          (smartAdd (smartAdd ns x₁ x₂).1 x₃ x₄).2 := by
      simp [DisjointBalanced.total]
    change _ ∈ (DisjointBalanced.total ns [x₁, x₂, x₃, x₄]).1.map Node.support
    rw [he4]
    have hleft := smartAdd_extends ns x₁ x₂
    have hright := smartAdd_extends (smartAdd ns x₁ x₂).1 x₃ x₄
    have hlast := smartAdd_extends (smartAdd (smartAdd ns x₁ x₂).1 x₃ x₄).1
      (smartAdd ns x₁ x₂).2 (smartAdd (smartAdd ns x₁ x₂).1 x₃ x₄).2
    have hv (x : Ref) (k : ℕ) (hx : x = some k) (hk : k < nodes.length) (big : List (Node ι))
        (hb : Extends nodes big) : refSupport big x = refSupport nodes x :=
      refSupport_extends hb (by rw [hx]; exact hk)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · have hm := smartAdd_union_mem ns x₁ x₂ k₁ k₂ h₁ h₂
      rw [hv x₁ k₁ h₁ l₁ ns hns, hv x₂ k₂ h₂ l₂ ns hns] at hm
      exact mem_supports_extends hlast (mem_supports_extends hright hm)
    · have hm := smartAdd_union_mem (smartAdd ns x₁ x₂).1 x₃ x₄ k₃ k₄ h₃ h₄
      have hb := extends_trans hns hleft
      rw [hv x₃ k₃ h₃ l₃ _ hb, hv x₄ k₄ h₄ l₄ _ hb] at hm
      exact mem_supports_extends hlast hm) nodes (extends_refl _)
  exact key (i, j) hmem (by simp; omega) hjm hij a ha

/-- The coarse weight operands of group `i`. -/
def weightRefs (m : ℕ) (edges : EdgeTable) (weights : WeightTable) (i : ℕ) : List Ref :=
  (groupAt (oddGroups m) i).map (lookup weights) ++
    (pairs (groupAt (oddGroups m) i)).map (fun p => edgeLookup edges p.1 p.2)

def cwCost (m : ℕ) (top : Bool) (i : ℕ) : ℕ := if i < m ∧ top = false then 2 else 0

theorem weightRefs_present (m : ℕ) (top : Bool) (nodes : List (Node ι)) (edges : EdgeTable)
    (weights : WeightTable) (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (i : ℕ) (hi : i ≤ m) :
    presentCount (weightRefs m edges weights i) =
      if i < m then (if top then 1 else 3) else 0 := by
  rcases groupAt_cases m i hi with ⟨him, hg⟩ | ⟨rfl, hg⟩
  · have w₁ := (weight_lookup nodes _ edges weights _ h (2 * i) (by omega)).1
    have w₂ := (weight_lookup nodes _ edges weights _ h (2 * i + 1) (by omega)).1
    obtain ⟨k, hk, -⟩ := edge_lookup nodes _ edges weights _ h (2 * i) (2 * i + 1) (by omega)
      (by omega) (by omega)
    simp only [weightRefs, hg, pairs, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil]
    have h₁ : 2 * i < 2 * m := by omega
    have h₂ : 2 * i + 1 < 2 * m := by omega
    simp only [presentCount, List.countP_cons, List.countP_nil, w₁, w₂, hk, him, ↓reduceIte]
    cases top <;> simp [pattern, h₁, h₂]
  · have w := (weight_lookup nodes _ edges weights _ h (2 * i) (by omega)).1
    simp only [weightRefs, hg, pairs, List.map_cons, List.map_nil, List.append_nil]
    simp [presentCount, w, pattern]

theorem coarseWeights_additions_le (m : ℕ) (top : Bool) (nodes : List (Node ι)) (edges : EdgeTable)
    (weights : WeightTable) (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top))
    (ns : List (Node ι)) :
    additionCount (coarseWeights ns (oddGroups m) edges weights).1 ≤
      additionCount ns + ((List.range (m + 1)).map (cwCost m top)).sum := by
  unfold coarseWeights
  rw [oddGroups_length]
  apply mapBuild_additions_le_inv _ _ (fun _ => True) _ (fun _ _ _ _ => trivial) _ _ trivial
  intro ns' i hi _
  have hp := weightRefs_present m top nodes edges weights h i (by simp at hi; omega)
  have ht := PairedPresence.total_additions_le_present ns' (weightRefs m edges weights i)
  rw [hp] at ht
  simp only [weightRefs] at ht
  dsimp only
  refine ht.trans ?_
  simp only [cwCost]
  split_ifs <;> simp_all

/-! ### The coarse level input -/

theorem coarse_input (m : ℕ) (top : Bool) (nodes : List (Node ι)) (edges : EdgeTable)
    (weights : WeightTable) (h : LevelInput nodes (2 * m + 1) edges weights (pattern m top)) :
    LevelInput (coarseWeights (coarseEdges nodes (oddGroups m) edges).1 (oddGroups m) edges weights).1
      (m + 1) (coarseEdges nodes (oddGroups m) edges).2
      (coarseWeights (coarseEdges nodes (oddGroups m) edges).1 (oddGroups m) edges weights).2
      (fun i => decide (i < m)) := by
  have hready := PairedCoarseCorrect.coarseGraph_ready h.ready
  simp only [oddGroups_length] at hready
  refine ⟨hready, ?_, ?_, ?_, ?_⟩
  · unfold coarseEdges
    rw [mapBuild_keys _ Prod.fst id (fun _ _ => rfl), List.map_id, oddGroups_length]
  · unfold coarseWeights
    rw [mapBuild_keys _ Prod.fst id (fun _ _ => rfl), List.map_id, oddGroups_length]
  · intro e he
    unfold coarseEdges at he
    have hf := mapBuild_forall₂ (fun ns (p : ℕ × ℕ) =>
        let r := DisjointBalanced.total ns (crossRefs edges (groupAt (oddGroups m) p.1)
          (groupAt (oddGroups m) p.2))
        (r.1, (p, r.2))) (fun _ e => e.2.isSome = true) (pairs (List.range (oddGroups m).length)) (by
      intro ns p hp
      rw [oddGroups_length] at hp
      have hp' := (pairs_mem _ List.pairwise_lt_range p.1 p.2).mp hp
      simp only [List.mem_range] at hp'
      apply PairedPresence.total_isSome
      obtain ⟨k, hk, -⟩ := edge_lookup nodes _ edges weights _ h (2 * p.1)
        (if p.2 < m then 2 * p.2 else 2 * m) (by omega) (by split_ifs <;> omega)
        (by split_ifs <;> omega)
      unfold presentCount
      apply List.countP_pos_iff.mpr
      refine ⟨edgeLookup edges (2 * p.1) (if p.2 < m then 2 * p.2 else 2 * m), ?_, by rw [hk]; rfl⟩
      simp only [crossRefs, List.mem_flatMap, List.mem_map]
      refine ⟨2 * p.1, by rw [groupAt_lt m p.1 (by omega)]; simp, _, ?_, rfl⟩
      rcases groupAt_cases m p.2 (by omega) with ⟨hj, hg⟩ | ⟨hj, hg⟩
      · rw [hg]; simp [hj]
      · rw [hg]; simp [hj]) nodes
    exact forall_of_forall₂ hf e he
  · intro w hw
    unfold coarseWeights at hw
    have hf := mapBuild_forall₂ (fun ns i =>
        let g := groupAt (oddGroups m) i
        let refs := g.map (lookup weights) ++ (pairs g).map (fun p => edgeLookup edges p.1 p.2)
        let result := DisjointBalanced.total ns refs
        (result.1, (i, result.2))) (fun i w => w.1 = i ∧ w.2.isSome = decide (i < m))
        (List.range (oddGroups m).length) (by
      intro ns i hi
      rw [oddGroups_length, List.mem_range] at hi
      refine ⟨rfl, ?_⟩
      have hp := weightRefs_present m top nodes edges weights h i (by omega)
      show (DisjointBalanced.total ns (weightRefs m edges weights i)).2.isSome = decide (i < m)
      by_cases him : i < m
      · rw [PairedPresence.total_isSome ns _ (by rw [hp]; simp only [him, ↓reduceIte]; split_ifs <;> omega)]
        simp [him]
      · rw [PairedPresence.total_none ns _ (by rw [hp]; simp [him])]
        simp [him]) (coarseEdges nodes (oddGroups m) edges).1
    have hw' := forall_of_forall₂ (hf.imp (fun _ _ hab => hab.1 ▸ hab.2)) w hw
    exact hw'

/-! ### One level -/

/-- The sharp allocation count of one level on `2m+1` vertices. -/
def levelCost (m : ℕ) (top : Bool) : ℕ :=
  PairedCircuitBudget.coarseEdgeBudget (oddGroups m) + ((List.range (m + 1)).map (cwCost m top)).sum +
    ((members (oddGroups m)).map (stripCost m top)).sum +
    ((members (oddGroups m)).map (singleCost m)).sum +
    ((pairs (List.range (m + 1))).map (crossCost m)).sum

/-- A level costs its own stages plus whatever its coarse call costs. -/
theorem level_bound (m : ℕ) (hm : 2 ≤ m) (top : Bool) (budget : ℕ)
    (hc : BlockBound (m + 1) (fun i => decide (i < m)) budget) :
    BlockBound (2 * m + 1) (pattern m top) (levelCost m top + budget) := by
  intro κ _ nodes edges weights h
  have hlarge : 4 < (List.range (2 * m + 1)).length := by simp; omega
  rw [block_large _ _ _ _ hlarge]
  dsimp only
  let ce := coarseEdges nodes (oddGroups m) edges
  let cw := coarseWeights ce.1 (oddGroups m) edges weights
  have hin := coarse_input m top nodes edges weights h
  have hlen : (PairGrouping.groups (List.range (2 * m + 1))).length = m + 1 := oddGroups_length m
  rw [hlen]
  let coarse := block cw.1 (List.range (m + 1)) ce.2 cw.2
  have hcoarse := hc κ cw.1 ce.2 cw.2 hin
  have hce := PairedCircuitBudget.coarseEdges_additions_le nodes (oddGroups m) edges
  have hcw := coarseWeights_additions_le m top nodes edges weights h ce.1
  have hcwe : Extends ce.1 cw.1 := by
    unfold cw coarseWeights
    exact mapBuild_extends _ (fun ns x => by exact total_extends _ _) _ _
  have hext : Extends ce.1 coarse.nodes :=
    extends_trans hcwe (PairedBlockCorrect.block_correct _ _ _ _ hin.ready).extension
  have hrows := coarse_rows m top nodes edges weights h
  have hnce : Extends nodes ce.1 := by
    unfold ce coarseEdges
    exact mapBuild_extends _ (fun ns x => by exact total_extends _ _) _ _
  have hs := strips_additions_le m hm top nodes edges weights h ce.1 hrows hnce coarse.nodes hext
  have hsi := singles_additions_le m nodes edges weights coarse.nodes coarse.one
    (buildStrips coarse.nodes (oddGroups m) edges weights).1
  have hcr := crossPairs_additions_le m edges coarse.two weights coarse.nodes
    (buildSingles (buildStrips coarse.nodes (oddGroups m) edges weights).1 (oddGroups m) coarse.one
      (buildStrips coarse.nodes (oddGroups m) edges weights).2).1
  change additionCount (buildCrossPairs (buildSingles (buildStrips coarse.nodes (oddGroups m) edges
    weights).1 (oddGroups m) coarse.one (buildStrips coarse.nodes (oddGroups m) edges weights).2).1
    (oddGroups m) edges coarse.two (buildStrips coarse.nodes (oddGroups m) edges weights).2).1 ≤ _
  change additionCount coarse.nodes ≤ additionCount cw.1 + budget at hcoarse
  change additionCount cw.1 ≤ additionCount ce.1 + _ at hcw
  change additionCount ce.1 ≤ _ at hce
  unfold levelCost
  omega

/-! ### The forty-nine vertex chain -/

theorem base_bound : BlockBound 4 (fun i => decide (i < 3)) 24 := by
  intro κ _ nodes edges weights h
  rw [block_small _ _ _ _ (by simp)]
  apply PairedBaseBound.base_additions_le nodes edges weights h.edge_keys
  · intro e he
    have hs := h.edge_present e he
    have hv := h.ready.refsValid e.2 (List.mem_append_left _ (List.mem_map_of_mem he))
    cases he2 : e.2 with
    | none => rw [he2] at hs; simp at hs
    | some i => rw [he2] at hv; exact ⟨i, rfl, hv⟩
  · exact h.weight_keys
  · intro w hw hw3
    have hs := h.weight_present w hw
    have hv := h.ready.refsValid w.2 (List.mem_append_right _ (List.mem_map_of_mem hw))
    cases hw2 : w.2 with
    | none => rw [hw2] at hs; simp at hs; omega
    | some i => rw [hw2] at hv; exact ⟨i, rfl, hv⟩
  · intro w hw hw3
    have hs := h.weight_present w hw
    cases hw2 : w.2 with
    | none => rfl
    | some i =>
      rw [hw2] at hs
      simp at hs
      omega

theorem pattern_inner (m : ℕ) : pattern m false = fun i => decide (i < 2 * m) := by
  funext i; simp [pattern]

theorem bound_7 : BlockBound 7 (fun i => decide (i < 6)) (levelCost 3 false + 24) := by
  have h := level_bound 3 (by norm_num) false 24 base_bound
  rw [pattern_inner] at h
  exact h

theorem bound_13 : BlockBound 13 (fun i => decide (i < 12))
    (levelCost 6 false + (levelCost 3 false + 24)) := by
  have h := level_bound 6 (by norm_num) false _ bound_7
  rw [pattern_inner] at h
  exact h

theorem bound_25 : BlockBound 25 (fun i => decide (i < 24))
    (levelCost 12 false + (levelCost 6 false + (levelCost 3 false + 24))) := by
  have h := level_bound 12 (by norm_num) false _ bound_13
  rw [pattern_inner] at h
  exact h

theorem bound_49 : BlockBound 49 (pattern 24 true)
    (levelCost 24 true + (levelCost 12 false + (levelCost 6 false + (levelCost 3 false + 24)))) :=
  level_bound 24 (by norm_num) true _ bound_25

theorem chain_total :
    levelCost 24 true + (levelCost 12 false + (levelCost 6 false + (levelCost 3 false + 24))) = 9915 := by
  decide +kernel

/-- The literal 49-vertex local construction allocates at most 9,915 additions.
No generated circuit, mask bank, or concrete node list is evaluated. -/
theorem circuit_additions_le :
    additionCount (PairedInitialGraph.circuit (List.range 49)).nodes ≤ 9915 := by
  have hin : LevelInput (PairedInitialGraph.nodes (List.range 49)) 49
      (PairedInitialGraph.edges (List.range 49)) (PairedInitialGraph.weights (List.range 49))
      (pattern 24 true) := by
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
  have h := bound_49 _ _ _ _ hin
  rw [chain_total, PairedInitialGraph.nodes_additionCount] at h
  simpa [PairedInitialGraph.circuit] using h

end IntegerMultBounds.Networks.PairedLevelBound
