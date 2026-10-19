module

public import IntegerMultBounds.Networks.DisjointBalanced

/-! Support uniqueness and nonemptiness for actual persistent DAG nodes.
Interning reuses every existing support, and valid nonzero additions have
at least two input atoms, separating them from singleton input nodes. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DisjointUnique

open DisjointCircuit DisjointBuilder
variable {ι : Type*} [DecidableEq ι]

/-- Lookup fails exactly when the requested support is absent. -/
theorem findSupport_none_iff (support : Finset ι) (prior : List (Finset ι)) :
    findSupport support prior = none ↔ support ∉ prior := by
  induction prior with
  | nil => simp [findSupport]
  | cons s ss ih =>
    by_cases h : s = support
    · simp [findSupport, h]
    · simp [findSupport, h, ih, Ne.symm h]

/-- Pairwise-distinct, nonempty stored supports. Zero is represented by an
absent reference, never by an empty-support stored node. -/
structure Unique (nodes : List (Node ι)) : Prop where
  nodup : (nodes.map Node.support).Nodup
  nonempty : ∀ node ∈ nodes, node.support.Nonempty

/-- Interning preserves distinct support identifiers regardless of the
proposed node's expression: an equal support is always reused. -/
theorem intern_nodup (nodes : List (Node ι)) (node : Node ι)
    (hn : (nodes.map Node.support).Nodup) :
    ((intern nodes node).1.map Node.support).Nodup := by
  unfold intern
  split
  · exact hn
  · rename_i hf
    have ha := (findSupport_none_iff node.support _).mp hf
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
      List.nodup_singleton]
    refine ⟨hn, trivial, ?_⟩
    intro s hs t ht hst
    have ht' : t = node.support := List.mem_singleton.mp ht
    exact ha (hst.trans ht' ▸ hs)

/-- Smart addition preserves uniqueness even before its semantic hypotheses
are discharged: both allocating and reuse branches go through interning. -/
theorem smartAdd_nodup (nodes : List (Node ι)) (l r : Ref)
    (hn : (nodes.map Node.support).Nodup) :
    ((smartAdd nodes l r).1.map Node.support).Nodup := by
  cases l <;> cases r
  all_goals first | exact hn | exact intern_nodup nodes _ hn

/-- A valid node over nonempty prior supports also has a nonempty support. -/
theorem node_nonempty (prior : List (Finset ι)) (node : Node ι)
    (hp : ∀ s ∈ prior, s.Nonempty) (hv : node.Valid prior) : node.support.Nonempty := by
  rcases node with ⟨kind,support⟩
  cases kind with
  | input a =>
    change support = {a} at hv
    rw [hv]
    exact Finset.singleton_nonempty a
  | add l r =>
    simp only [Node.Valid] at hv
    split at hv
    next hl =>
      split at hv
      next hr =>
        rw [hv.2]
        exact (hp _ (List.getElem_mem hl)).mono Finset.subset_union_left
      next hr => contradiction
    next hl => contradiction

theorem validFrom_nonempty (prior : List (Finset ι)) (nodes : List (Node ι))
    (hp : ∀ s ∈ prior, s.Nonempty) (hv : ValidFrom prior nodes) :
    ∀ node ∈ nodes, node.support.Nonempty := by
  induction nodes generalizing prior with
  | nil => simp
  | cons node nodes ih =>
    have hn := node_nonempty prior node hp hv.1
    have ht := ih (prior ++ [node.support]) (by
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hp s hs
      · simpa using (List.mem_singleton.mp hs).symm ▸ hn) hv.2
    intro n hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hn
    · exact ht n hm

/-- Nonemptiness follows from the actual DAG validity predicate alone. -/
theorem valid_nonempty (nodes : List (Node ι)) (hv : Valid nodes) :
    ∀ node ∈ nodes, node.support.Nonempty :=
  validFrom_nonempty [] nodes (by simp) hv

theorem unique_of_valid_nodup (nodes : List (Node ι)) (hv : Valid nodes)
    (hn : (nodes.map Node.support).Nodup) : Unique nodes :=
  ⟨hn, valid_nonempty nodes hv⟩

omit [DecidableEq ι] in
theorem refSupport_nonempty (nodes : List (Node ι)) (hn : ∀ node ∈ nodes, node.support.Nonempty)
    (i : ℕ) (hi : RefValid nodes (some i)) : (refSupport nodes (some i)).Nonempty := by
  rw [refSupport_some nodes i hi]
  exact hn _ (List.getElem_mem hi)

/-- Two disjoint nonempty summands contain at least two distinct atoms. -/
theorem union_card_two (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t) :
    2 ≤ (s ∪ t).card := by
  rw [Finset.card_union_of_disjoint hd]
  have h1 := Finset.card_pos.mpr hs
  have h2 := Finset.card_pos.mpr ht
  omega

/-- Every structurally valid addition over nonempty prior supports has
cardinality at least two, independently of how its node was constructed. -/
theorem node_add_card_two (prior : List (Finset ι)) (support : Finset ι) (l r : ℕ)
    (hp : ∀ s ∈ prior, s.Nonempty) (hv : (⟨.add l r, support⟩ : Node ι).Valid prior) :
    2 ≤ support.card := by
  simp only [Node.Valid] at hv
  split at hv
  next hl =>
    split at hv
    next hr =>
      rw [hv.2]
      exact union_card_two _ _ (hp _ (List.getElem_mem hl)) (hp _ (List.getElem_mem hr)) hv.1
    next hr => contradiction
  next hl => contradiction

/-- Every stored addition in a valid suffix has at least two atoms. -/
theorem validFrom_add_card_two (prior : List (Finset ι)) (nodes : List (Node ι))
    (hp : ∀ s ∈ prior, s.Nonempty) (hv : ValidFrom prior nodes) :
    ∀ node ∈ nodes, ∀ l r, node.kind = .add l r → 2 ≤ node.support.card := by
  induction nodes generalizing prior with
  | nil => simp
  | cons node nodes ih =>
    have hn := node_nonempty prior node hp hv.1
    have ht := ih (prior ++ [node.support]) (by
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hp s hs
      · simpa using (List.mem_singleton.mp hs).symm ▸ hn) hv.2
    intro n hm l r he
    rcases List.mem_cons.mp hm with heq | hm
    · subst n
      rcases node with ⟨kind,support⟩
      simp only at he
      subst kind
      exact node_add_card_two prior support l r hp hv.1
    · exact ht n hm l r he

/-- Genuine additions anywhere in a valid completed DAG are never singleton
input supports, including additions retained after later interning. -/
theorem valid_add_card_two (nodes : List (Node ι)) (hv : Valid nodes)
    (node : Node ι) (hn : node ∈ nodes) (l r : ℕ) (he : node.kind = .add l r) :
    2 ≤ node.support.card :=
  validFrom_add_card_two [] nodes (by simp) hv node hn l r he

/-- Literal balanced totals retain the unique support-id invariant. -/
theorem balanced_total_nodup (nodes : List (Node ι)) (refs : List Ref)
    (hn : (nodes.map Node.support).Nodup) :
    ((DisjointBalanced.total nodes refs).1.map Node.support).Nodup := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction generalizing nodes with
  | h refs ih =>
    cases refs with
    | nil => simpa only [DisjointBalanced.total] using hn
    | cons r rs =>
      cases rs with
      | nil => simpa only [DisjointBalanced.total] using hn
      | cons s rs =>
        let values := r :: s :: rs
        let left := values.take (values.length / 2)
        let right := values.drop (values.length / 2)
        have hlen : 2 ≤ values.length := by simp [values]
        have hl : left.length < values.length := by simp only [left, List.length_take]; omega
        have hr : right.length < values.length := by simp only [right, List.length_drop]; omega
        rw [DisjointBalanced.total]
        exact smartAdd_nodup _ _ _ (ih right hr _ (ih left hl nodes hn))

end IntegerMultBounds.Networks.DisjointUnique
