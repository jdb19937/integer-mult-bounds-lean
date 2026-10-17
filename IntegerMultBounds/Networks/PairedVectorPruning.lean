module

public import IntegerMultBounds.Networks.PairedVectorBudget
public import IntegerMultBounds.Networks.DisjointPruningBudget
public import IntegerMultBounds.Networks.DisjointExclusion
public import IntegerMultBounds.Networks.PairedVectorCorrect
public import IntegerMultBounds.Networks.DisjointUnique

/-! The full total of a leave-one-out vector is unnecessary when every
requested output omits a present operand. Support containment proves deadness
without running the backwards marker, even if the total aliases an older node. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedVectorPruning

open DisjointCircuit DisjointBuilder DisjointExclusion DisjointUnique
open PairedCircuit PairedVectorCorrect PairedVectorBudget DisjointPruning DAGSupportTrace

variable {ι : Type*} [DecidableEq ι]

/-- Every operand's support lies in the total support. -/
theorem refSupport_subset_supports (nodes : List (Node ι)) (refs : List Ref)
    (r : Ref) (hr : r ∈ refs) : refSupport nodes r ⊆ supports nodes refs := by
  induction refs with
  | nil => simp at hr
  | cons x xs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Finset.subset_union_left
    · exact (ih hr).trans Finset.subset_union_right

/-- An omitted operand is disjoint from every operand left in its query. -/
theorem refSupport_disjoint_eraseIdx (nodes : List (Node ι)) (refs : List Ref)
    (hd : DisjointRefs nodes refs) (i : ℕ) (hi : i < refs.length) :
    Disjoint (refSupport nodes refs[i]) (supports nodes (refs.eraseIdx i)) := by
  induction refs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    have hh := List.pairwise_cons.mp hd
    cases i with
    | zero => exact disjoint_supports nodes _ rs hh.1
    | succ i =>
      have hi' : i < rs.length := by simpa using hi
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, supports]
      apply Finset.disjoint_union_right.mpr
      exact ⟨(hh.1 _ (List.getElem_mem hi')).symm, ih hh.2 i hi'⟩

/-- Removing a present disjoint operand strictly decreases the total support. -/
theorem supports_not_subset_eraseIdx (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (i : ℕ) (hi : i < refs.length) (hp : refs[i].isSome = true) :
    ¬ supports nodes refs ⊆ supports nodes (refs.eraseIdx i) := by
  have hn : (refSupport nodes refs[i]).Nonempty := by
    have hri := hr _ (List.getElem_mem hi)
    cases he : refs[i] with
    | none => simp [he] at hp
    | some j => exact refSupport_nonempty nodes (valid_nonempty nodes hv) j (he ▸ hri)
  obtain ⟨a, ha⟩ := hn
  have hs := refSupport_subset_supports nodes refs refs[i] (List.getElem_mem hi)
  intro hsub
  exact Finset.disjoint_left.mp (refSupport_disjoint_eraseIdx nodes refs hd i hi) ha (hsub (hs ha))

/-- The total cannot be an ancestor of any omission of a present operand.
The roots may be later sums with smaller supports, so this also applies after
other stages have extended the vector's DAG. -/
theorem total_not_marked (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (larger : List (Node ι)) (he : Extends (vectorFalse nodes refs).nodes larger)
    (hl : Valid larger) (roots : Finset ℕ) (total : ℕ)
    (ht : (vectorFalse nodes refs).total = some total)
    (hroots : ∀ r ∈ roots, ∃ i, ∃ hi : i < refs.length, refs[i].isSome = true ∧
      nodeSupport larger r ⊆ supports nodes (refs.eraseIdx i)) :
    total ∉ mark larger roots := by
  have hb := vectorFalse_built nodes refs hv hr hd
  have htotal : nodeSupport larger total = supports nodes refs := by
    change refSupport larger (some total) = _
    rw [← ht, refSupport_extends he hb.total_valid, hb.total_support]
  apply not_marked_of_support larger hl roots total
  intro r hmem hsub
  obtain ⟨i, hi, hp, hs⟩ := hroots r hmem
  rw [htotal] at hsub
  exact supports_not_subset_eraseIdx nodes refs hv hr hd i hi hp (hsub.trans hs)

/-- In particular, no marker replay is needed when the roots are the vector's
actual leave-one-out outputs and every operand is present. -/
theorem total_not_marked_outputs (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hall : ∀ r ∈ refs, r.isSome = true) (total : ℕ)
    (ht : (vectorFalse nodes refs).total = some total) :
    total ∉ mark (vectorFalse nodes refs).nodes
      ((vectorFalse nodes refs).one.filterMap id).toFinset := by
  apply total_not_marked nodes refs hv hr hd _ (extends_refl _)
    (vectorFalse_built nodes refs hv hr hd).valid _ total ht
  intro r hmem
  obtain ⟨out, hout, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hmem)
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hout
  have hi' : i < refs.length := by simpa only [vectorFalse_length] using hi
  refine ⟨i, hi', hall _ (List.getElem_mem hi'), ?_⟩
  have hs := vectorFalse_support nodes refs hv hr hd i hi'
  have hrout : (vectorFalse nodes refs).one[i]?.getD none = some r := by
    simp only [List.getElem?_eq_getElem hi, Option.getD_some, hget]
    exact he
  rw [hrout] at hs
  exact hs.le

/-- When only a strip's outside outputs are requested, the full total is dead
even when the carry is zero: each outside output omits a present cross-group
value. This does not apply to callers that also consume the total for singles. -/
theorem total_not_marked_tail_outputs (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hall : ∀ r ∈ refs.tail, r.isSome = true) (total : ℕ)
    (ht : (vectorFalse nodes refs).total = some total) :
    total ∉ mark (vectorFalse nodes refs).nodes
      ((vectorFalse nodes refs).one.tail.filterMap id).toFinset := by
  apply total_not_marked nodes refs hv hr hd _ (extends_refl _)
    (vectorFalse_built nodes refs hv hr hd).valid _ total ht
  intro r hmem
  obtain ⟨out, hout, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hmem)
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hout
  have hi' : i + 1 < refs.length := by
    rw [List.length_tail, vectorFalse_length] at hi
    omega
  have htail : i < refs.tail.length := by simp only [List.length_tail]; omega
  refine ⟨i+1, hi', ?_, ?_⟩
  · have hmem' := List.getElem_mem htail
    rw [List.getElem_tail] at hmem'
    exact hall _ hmem'
  · have hs := vectorFalse_support nodes refs hv hr hd (i+1) hi'
    have houtlen : i+1 < (vectorFalse nodes refs).one.length := by
      rw [vectorFalse_length]
      exact hi'
    have hrout : (vectorFalse nodes refs).one[i+1]?.getD none = some r := by
      simp only [List.getElem?_eq_getElem houtlen, Option.getD_some]
      rw [← List.getElem_tail hi, hget]
      exact he
    rw [hrout] at hs
    exact hs.le

end IntegerMultBounds.Networks.PairedVectorPruning
