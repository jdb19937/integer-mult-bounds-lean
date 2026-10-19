module

public import IntegerMultBounds.Networks.DisjointBalanced
public import Mathlib.Data.List.Sublists

/-! Weighted paired-exclusion builder foundations. The upstream small-block
branch computes all, leave-one-out, and leave-two-out weighted graph sums.
This file executes that branch using the upstream floor-half balanced totals
with left-before-right evaluation, zero elision, and support interning, and proves the complete returned list of references correct. The recursive
coarse-graph and strip reconstruction are not asserted here. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DisjointPaired

open DisjointCircuit DisjointBuilder

variable {ι V A : Type*} [DecidableEq ι] [DecidableEq V]

private theorem supports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) : supports larger refs = supports nodes refs := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    rw [supports, supports, refSupport_extends he (hr r (by simp))]
    rw [ih (fun s hs => hr s (by simp [hs]))]

omit [DecidableEq ι] in
private theorem refsValid_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) : RefsValid larger refs :=
  fun r h => refValid_extends he (hr r h)

omit [DecidableEq ι] in
private theorem disjointRefs_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    DisjointRefs larger refs := by
  apply List.Pairwise.imp_of_mem _ hd
  intro l r hl hr' hdis
  rw [refSupport_extends he (hr l hl), refSupport_extends he (hr r hr')]
  exact hdis

/-- Sequentially build several totals in one shared DAG. Later totals may
intern supports already built for earlier queries. -/
def batch (nodes : List (Node ι)) : List (List Ref) → List (Node ι) × List Ref
  | [] => (nodes, [])
  | query :: queries =>
    let first := DisjointBalanced.total nodes query
    let rest := batch first.1 queries
    (rest.1, first.2 :: rest.2)

def budget (queries : List (List Ref)) : ℕ :=
  (queries.map (fun q => q.length - 1)).sum

structure BatchBuilt (nodes : List (Node ι)) (queries : List (List Ref))
    (result : List (Node ι) × List Ref) : Prop where
  valid : Valid result.1
  extension : Extends nodes result.1
  refsValid : RefsValid result.1 result.2
  supports_eq : result.2.map (refSupport result.1) = queries.map (supports nodes)
  length_le : result.1.length ≤ nodes.length + budget queries

/-- A whole batch is a valid extension, with ordered output support semantics
and a concrete bound on the total number of appended addition nodes. -/
theorem batch_built (nodes : List (Node ι)) (queries : List (List Ref)) (hv : Valid nodes)
    (hr : ∀ q ∈ queries, RefsValid nodes q) (hd : ∀ q ∈ queries, DisjointRefs nodes q) :
    BatchBuilt nodes queries (batch nodes queries) := by
  induction queries generalizing nodes with
  | nil => exact ⟨hv, extends_refl _, by simp [RefsValid, batch], rfl, by simp [batch, budget]⟩
  | cons q qs ih =>
    have hq := DisjointBalanced.total_built nodes q hv (hr q (by simp)) (hd q (by simp))
    have hrest := ih (DisjointBalanced.total nodes q).1 hq.valid
      (fun s hs => refsValid_extends hq.extension s (hr s (by simp [hs])))
      (fun s hs => disjointRefs_extends hq.extension s (hr s (by simp [hs])) (hd s (by simp [hs])))
    refine ⟨hrest.valid, extends_trans hq.extension hrest.extension, ?_, ?_, ?_⟩
    · intro r hr'
      rcases List.mem_cons.mp hr' with rfl | hrr
      · exact refValid_extends hrest.extension hq.refValid
      · exact hrest.refsValid r hrr
    · change refSupport (batch (DisjointBalanced.total nodes q).1 qs).1 (DisjointBalanced.total nodes q).2 ::
        ((batch (DisjointBalanced.total nodes q).1 qs).2.map (refSupport (batch (DisjointBalanced.total nodes q).1 qs).1)) = _
      rw [refSupport_extends hrest.extension hq.refValid, hq.support_eq, hrest.supports_eq]
      simp only [List.map_cons]
      congr 1
      apply List.map_congr_left
      intro s hs
      exact supports_extends hq.extension s (hr s (by simp [hs]))
    · have ht := hq.length_le
      have hs := hrest.length_le
      change (batch (DisjointBalanced.total nodes q).1 qs).1.length ≤ _
      simp only [budget, List.map_cons, List.sum_cons] at hs ⊢
      omega

section Values

variable [AddCommMonoid A]

end Values

/-- Each weighted term records its incident vertices and existing DAG reference.
Vertex weights have one incident vertex and graph edges have two. -/
abbrev Entry (V : Type*) := Finset V × Ref

/-- The concrete weighted graph term list used by the paired recursion. -/
def weightedEntries (edges : List (V × V × Ref)) (weights : List (V × Ref)) : List (Entry V) :=
  edges.map (fun e => ({e.1, e.2.1}, e.2.2)) ++ weights.map (fun w => ({w.1}, w.2))

/-- Exactly the terms touching none of the omitted vertices, as in the
upstream `block` small-case filter. Zero terms remain optional references. -/
def select (entries : List (Entry V)) (excluded : Finset V) : List Ref :=
  (entries.filter (fun e => decide (Disjoint e.1 excluded))).map Prod.snd

/-- The empty omission, each singleton, and each unordered pair in list order. -/
def omissions (points : List V) : List (Finset V) :=
  ∅ :: (points.map (fun p => {p}) ++ (points.sublistsLen 2).map List.toFinset)

def baseQueries (points : List V) (entries : List (Entry V)) : List (List Ref) :=
  (omissions points).map (select entries)

/-- The actual weighted all/one/two exclusion branch. It is valid for any
finite vertex list; the optimized paired recursion uses it at size at most four. -/
def baseBlock (nodes : List (Node ι)) (points : List V)
    (edges : List (V × V × Ref)) (weights : List (V × Ref)) : List (Node ι) × List Ref :=
  batch nodes (baseQueries points (weightedEntries edges weights))

end IntegerMultBounds.Networks.DisjointPaired
