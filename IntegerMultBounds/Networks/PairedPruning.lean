module

public import IntegerMultBounds.Networks.PairedInitialBudget

/-! Structural pruning of unused single-exclusion outputs. A single-exclusion
sum always contains an edge forbidden by each pair-exclusion output, so it
cannot be an ancestor of a requested output. This works for every sorted graph
with at least three vertices, without inspecting a generated node list. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedInitialGraph

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open DAGSupportTrace DisjointPruning

def singleSupport (points : List ℕ) (a : ℕ) : Finset Input :=
  (pairs points).toFinset.filter (fun q => q.1 ≠ a ∧ q.2 ≠ a)

/-- A vertex different from the excluded vertex has a surviving incident edge. -/
theorem exists_edge_avoiding (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a v : ℕ) (hv : v ∈ points) (hne : v ≠ a) :
    ∃ q ∈ singleSupport points a, v ∈ [q.1, q.2] := by
  have hsmall : ({a, v} : Finset ℕ).card < points.toFinset.card := by
    have h := Finset.card_insert_le a ({v} : Finset ℕ)
    simp only [Finset.card_singleton] at h
    omega
  obtain ⟨w, hw, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hw' : w ∈ points := List.mem_toFinset.mp hw
  have hnot' : w ≠ a ∧ w ≠ v := by simpa using hnot
  have hwa := hnot'.1
  have hwv := hnot'.2
  by_cases hvw : v < w
  · refine ⟨(v, w), ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      ((pairs_mem points hs v w).mpr ⟨hv, hw', hvw⟩), hne, hwa⟩
  · refine ⟨(w, v), ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      ((pairs_mem points hs w v).mpr ⟨hw', hv, by omega⟩), hwa, hne⟩

/-- Every pair-exclusion target forbids an edge of each single-exclusion sum. -/
theorem singleSupport_not_subset_pair (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a : ℕ) (p : Input) (hp : p ∈ pairs points) :
    ¬ singleSupport points a ⊆ (pairs points).toFinset.filter
      (fun q => q.1 ∉ [p.1, p.2] ∧ q.2 ∉ [p.1, p.2]) := by
  have hpm := (pairs_mem points hs p.1 p.2).mp hp
  obtain ⟨v, hv, hva, hvp⟩ : ∃ v ∈ points, v ≠ a ∧ v ∈ [p.1, p.2] := by
    by_cases h : p.1 = a
    · exact ⟨p.2, hpm.2.1, by omega, by simp⟩
    · exact ⟨p.1, hpm.1, h, by simp⟩
  obtain ⟨q, hq, hvq⟩ := exists_edge_avoiding points hs hcard a v hv hva
  intro hsub
  have h := (Finset.mem_filter.mp (hsub hq)).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvq
  rcases hvq with rfl | rfl
  · exact h.1 hvp
  · exact h.2 hvp

theorem circuit_single_support (points : List ℕ) (hs : points.Pairwise (· < ·))
    (a : ℕ) (ha : a ∈ points) :
    RefSpec (singleSupport points a) (circuit points).nodes (lookup (circuit points).one a) := by
  have h := (circuit_correct points hs).one a ha
  rw [query_support points hs] at h
  simpa [singleSupport] using h

/-- None of the actual single-exclusion references is live when only pair
outputs are requested. This includes reused references from recursive levels. -/
theorem single_output_not_marked (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a : ℕ) (ha : a ∈ points)
    (i : ℕ) (hi : lookup (circuit points).one a = some i) :
    i ∉ mark (circuit points).nodes (outputRefs points).toFinset := by
  have hsingle := (circuit_single_support points hs a ha).2
  rw [hi] at hsingle
  change nodeSupport (circuit points).nodes i = singleSupport points a at hsingle
  apply not_marked_of_support _ (circuit_correct points hs).valid
  intro r hr
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hr)
  have hpair := (circuit_pair_support points hs p hp).2
  rw [he] at hpair
  change nodeSupport (circuit points).nodes r = _ at hpair
  rw [hsingle, hpair]
  exact singleSupport_not_subset_pair points hs hcard a p hp

/-- References whose single-exclusion results are not requested by the caller. -/
def singleRefs (points : List ℕ) : Finset ℕ :=
  (points.filterMap (lookup (circuit points).one)).toFinset

/-- Count only actual addition nodes: absent references, inputs, and reused
identifiers cannot inflate the pruning credit. -/
def singleSavings (points : List ℕ) : ℕ :=
  additionCountFrom 0 (singleRefs points) (circuit points).nodes

theorem single_additions_saved (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) :
    additionCountFrom 0 (mark (circuit points).nodes (outputRefs points).toFinset)
        (circuit points).nodes + singleSavings points ≤
      DAGAllocator.additionCount (circuit points).nodes := by
  apply additionCountFrom_add_le
  apply Finset.disjoint_left.mpr
  intro i hi hsingle
  obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
  exact single_output_not_marked points hs hcard a ha i he hi

/-- Every constructor bound automatically receives the single-output pruning
credit, including savings from references allocated at a recursive level. -/
theorem compile_bounds_without_singles (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (capacity : ℕ)
    (hc : DAGAllocator.additionCount (circuit points).nodes ≤ capacity) :
    (DAGAllocator.compile (circuit points).nodes (outputRefs points)).state.next ≤
        (capacity - singleSavings points) + (pairs points).length ∧
      (DAGAllocator.compile (circuit points).nodes (outputRefs points)).program.length ≤
        2 * (capacity - singleSavings points) + (pairs points).length := by
  apply compile_bounds_of_active points hs (capacity - singleSavings points)
  have h := single_additions_saved points hs hcard
  omega

end IntegerMultBounds.Networks.PairedInitialGraph
