module

public import IntegerMultBounds.Networks.PairedVectorBudget
public import IntegerMultBounds.Networks.PairedStripCorrect

/-! Sharp structural budgets for the actual batch-then-vector strip builder.
Nonempty query supports establish present operands semantically. The same
proof applies at every weighted recursive level, without concrete DAG rows. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStripBudget

open DisjointCircuit DisjointBuilder DisjointExclusion PairedCircuit PairedCircuitCorrect
open PairedVectorBudget DAGAllocator

variable {ι : Type*} [DecidableEq ι]

/-- Balanced query construction is bounded independently of the intern bank. -/
theorem batch_additions_le (nodes : List (Node ι)) (queries : List (List Ref)) :
    additionCount (DisjointPaired.batch nodes queries).1 ≤
      additionCount nodes + DisjointPaired.budget queries := by
  induction queries generalizing nodes with
  | nil => simp [DisjointPaired.batch, DisjointPaired.budget]
  | cons q qs ih =>
    have hq := PairedCircuitBudget.total_additions_le nodes q
    have ht := ih (DisjointBalanced.total nodes q).1
    simp only [DisjointPaired.batch, DisjointPaired.budget, List.map_cons, List.sum_cons]
    unfold DisjointPaired.budget at ht
    omega

/-- Every nonempty query support gives a present batch result, regardless of
zero terms within the query or reuse of an older support. -/
theorem batch_all_present (nodes : List (Node ι)) (queries : List (List Ref))
    (hv : Valid nodes) (hr : RefsValid nodes queries.flatten)
    (hd : DisjointRefs nodes queries.flatten)
    (hn : ∀ q ∈ queries, (supports nodes q).Nonempty) :
    ∀ r ∈ (DisjointPaired.batch nodes queries).2, r.isSome = true := by
  have hb := DisjointPaired.batch_built nodes queries hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  intro r hmem
  have hm : refSupport (DisjointPaired.batch nodes queries).1 r ∈ queries.map (supports nodes) := by
    rw [← hb.supports_eq]
    exact List.mem_map.mpr ⟨r, hmem, rfl⟩
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  cases r with
  | none => simpa [he, refSupport] using hn q hq
  | some i => rfl

/-- A whole weighted strip costs its balanced-query budget plus three k minus
six additions for k nonempty query groups. -/
theorem batch_vector_additions_le_sharp (nodes : List (Node ι)) (queries : List (List Ref))
    (hv : Valid nodes) (hr : RefsValid nodes queries.flatten)
    (hd : DisjointRefs nodes queries.flatten)
    (hn : ∀ q ∈ queries, (supports nodes q).Nonempty) (hk : 3 ≤ queries.length) :
    additionCount (vectorTail (DisjointPaired.batch nodes queries).1
      (DisjointPaired.batch nodes queries).2).nodes ≤
      additionCount nodes + DisjointPaired.budget queries + (3 * queries.length - 6) := by
  have hb := DisjointPaired.batch_built nodes queries hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  have hlen : (DisjointPaired.batch nodes queries).2.length = queries.length := by
    have hh := congrArg List.length hb.supports_eq
    simpa only [List.length_map] using hh
  have hvb := vectorTail_additions_le_sharp (DisjointPaired.batch nodes queries).1
    (DisjointPaired.batch nodes queries).2 (batch_all_present nodes queries hv hr hd hn)
    (by omega)
  rw [hlen] at hvb
  have hbudget := batch_additions_le nodes queries
  omega

/-- The zero-carry variant charges only the nonempty cross-group queries.
Empty carry terms may have any length and are handled by their exact support. -/
theorem batch_vector_empty_carry_additions_le_sharp (nodes : List (Node ι))
    (carry : List Ref) (queries : List (List Ref))
    (hv : Valid nodes) (hr : RefsValid nodes (carry :: queries).flatten)
    (hd : DisjointRefs nodes (carry :: queries).flatten)
    (hc : supports nodes carry = ∅)
    (hn : ∀ q ∈ queries, (supports nodes q).Nonempty) (hk : 2 ≤ queries.length) :
    additionCount (vectorTail (DisjointPaired.batch nodes (carry :: queries)).1
      (DisjointPaired.batch nodes (carry :: queries)).2).nodes ≤
      additionCount nodes + DisjointPaired.budget (carry :: queries) + (3 * queries.length - 5) := by
  let batch := DisjointPaired.batch nodes (carry :: queries)
  have hb := DisjointPaired.batch_built nodes (carry :: queries) hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  have hlen : batch.2.length = queries.length + 1 := by
    have hh := congrArg List.length hb.supports_eq
    simpa only [List.length_map, List.length_cons] using hh
  have hbudget := batch_additions_le nodes (carry :: queries)
  have hs := hb.supports_eq
  change batch.2.map (refSupport batch.1) = _ at hs
  cases hout : batch.2 with
  | nil => simp [hout] at hlen
  | cons r rs =>
    have hs' : refSupport batch.1 r = ∅ ∧
        rs.map (refSupport batch.1) = queries.map (supports nodes) := by
      simpa only [hout, List.map_cons, List.cons.injEq, hc] using hs
    have hvalid : RefsValid batch.1 (r :: rs) := by
      simpa only [← hout] using hb.refsValid
    have hr0 := hvalid r (by simp)
    have hrnone := ref_eq_none_of_support_empty batch.1 r hb.valid hr0 hs'.1
    have hall : ∀ r ∈ rs, r.isSome = true := by
      intro r hmem
      have hm : refSupport batch.1 r ∈ queries.map (supports nodes) := by
        rw [← hs'.2]
        exact List.mem_map.mpr ⟨r, hmem, rfl⟩
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
      cases r with
      | none => simpa [he, refSupport] using hn q hq
      | some i => rfl
    have hlen' : rs.length = queries.length := by simpa [hout] using hlen
    have hvb := vectorTail_cons_none_additions_le_sharp batch.1 rs hall (by omega)
    change additionCount (vectorTail batch.1 (r :: rs)).nodes ≤ _
    rw [hrnone]
    rw [hlen'] at hvb
    change additionCount batch.1 ≤ _ at hbudget
    omega

/-- Transfer the sharp weighted-vector budget directly to a literal strip. -/
theorem buildStrip_additions_le_sharp (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ)
    (hv : Valid nodes) (hr : RefsValid nodes (stripQueries groups edges weights ia).flatten)
    (hd : DisjointRefs nodes (stripQueries groups edges weights ia).flatten)
    (hn : ∀ q ∈ stripQueries groups edges weights ia, (supports nodes q).Nonempty)
    (hk : 3 ≤ (stripQueries groups edges weights ia).length) :
    additionCount (buildStrip nodes groups edges weights ia).1 ≤
      additionCount nodes + DisjointPaired.budget (stripQueries groups edges weights ia) +
        (3 * (stripQueries groups edges weights ia).length - 6) := by
  rw [buildStrip_eq]
  exact batch_vector_additions_le_sharp nodes _ hv hr hd hn hk

end IntegerMultBounds.Networks.PairedStripBudget
