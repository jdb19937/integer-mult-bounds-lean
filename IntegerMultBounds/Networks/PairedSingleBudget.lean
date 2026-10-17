module

public import IntegerMultBounds.Networks.PairedPruning
public import IntegerMultBounds.Networks.DAGAdditionIds
import IntegerMultBounds.Networks.DisjointPruningBudget
import IntegerMultBounds.Networks.DAGValueTransfer
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient

/-! Symbolic count of unused single-exclusion additions. With at least four
vertices each single output is a distinct genuine addition, so all n outputs
contribute exactly n pruning credits without reducing the concrete node list. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedInitialGraph

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open DAGAdditionIds DAGSupportTrace DisjointPruning

/-- Each single-exclusion query contains an edge once three vertices exist. -/
theorem singleSupport_nonempty (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a : ℕ) : (singleSupport points a).Nonempty := by
  have hsmall : ({a} : Finset ℕ).card < points.toFinset.card := by simp; omega
  obtain ⟨v, hv, hne⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  obtain ⟨q, hq, _⟩ := exists_edge_avoiding points hs hcard a v
    (List.mem_toFinset.mp hv) (by simpa using hne)
  exact ⟨q, hq⟩

/-- A fourth vertex supplies an edge distinct from any chosen surviving edge. -/
theorem singleSupport_card_two (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 4 ≤ points.toFinset.card) (a : ℕ) : 2 ≤ (singleSupport points a).card := by
  obtain ⟨q, hq⟩ := singleSupport_nonempty points hs (by omega) a
  have hsmall : ({a, q.1, q.2} : Finset ℕ).card < points.toFinset.card := by
    have h1 := Finset.card_insert_le a ({q.1, q.2} : Finset ℕ)
    have h2 := Finset.card_insert_le q.1 ({q.2} : Finset ℕ)
    simp only [Finset.card_singleton] at h2
    omega
  obtain ⟨v, hv, hne⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hnot : v ≠ a ∧ v ≠ q.1 ∧ v ≠ q.2 := by simpa using hne
  obtain ⟨r, hr, hvr⟩ := exists_edge_avoiding points hs (by omega) a v
    (List.mem_toFinset.mp hv) hnot.1
  have hqr : q ≠ r := by
    intro he
    rw [← he] at hvr
    simp [hnot.2.1, hnot.2.2] at hvr
  have h := Finset.one_lt_card.mpr ⟨q, hq, r, hr, hqr⟩
  omega

/-- Two different excluded vertices have different single-output supports. -/
theorem singleSupport_ne (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a b : ℕ) (hb : b ∈ points) (hne : a ≠ b) :
    singleSupport points a ≠ singleSupport points b := by
  obtain ⟨q, hq, hbq⟩ := exists_edge_avoiding points hs hcard a b hb hne.symm
  intro he
  rw [he] at hq
  have havoid := (Finset.mem_filter.mp hq).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbq
  rcases hbq with hbq | hbq
  · exact havoid.1 hbq.symm
  · exact havoid.2 hbq.symm

/-- Actual single-output references are present; zero cannot carry an edge. -/
theorem single_output_present (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a : ℕ) (ha : a ∈ points) :
    ∃ i, lookup (circuit points).one a = some i := by
  have hh := (circuit_single_support points hs a ha).2
  cases he : lookup (circuit points).one a with
  | none =>
    have hn := singleSupport_nonempty points hs hcard a
    rw [he] at hh
    rw [← hh] at hn
    exact False.elim (Finset.not_nonempty_empty hn)
  | some i => exact ⟨i, rfl⟩

/-- A total index function used only after presence has been proved. -/
def singleIndex (points : List ℕ) (a : ℕ) : ℕ := (lookup (circuit points).one a).getD 0

theorem singleIndex_spec (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) (a : ℕ) (ha : a ∈ points) :
    lookup (circuit points).one a = some (singleIndex points a) := by
  obtain ⟨i, hi⟩ := single_output_present points hs hcard a ha
  simp [singleIndex, hi]

theorem singleIndex_injOn (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) : Set.InjOn (singleIndex points) (↑points.toFinset : Set ℕ) := by
  intro a ha b hb he
  have hsa := (circuit_single_support points hs a (List.mem_toFinset.mp ha)).2
  have hsb := (circuit_single_support points hs b (List.mem_toFinset.mp hb)).2
  rw [singleIndex_spec points hs hcard a (List.mem_toFinset.mp ha)] at hsa
  rw [singleIndex_spec points hs hcard b (List.mem_toFinset.mp hb), ← he] at hsb
  by_contra hne
  exact singleSupport_ne points hs hcard a b (List.mem_toFinset.mp hb) hne (hsa.symm.trans hsb)

/-- Finite-set images account for aliases before any pruning credit is taken. -/
theorem singleRefs_eq_image (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) :
    singleRefs points = points.toFinset.image (singleIndex points) := by
  ext i
  simp only [singleRefs, List.mem_toFinset, List.mem_filterMap, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, ?_⟩
    simp [singleIndex, he]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, singleIndex_spec points hs hcard a ha⟩

theorem singleRefs_card (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 3 ≤ points.toFinset.card) : (singleRefs points).card = points.length := by
  rw [singleRefs_eq_image points hs hcard, Finset.card_image_of_injOn
    (singleIndex_injOn points hs hcard), List.toFinset_card_of_nodup
      (hs.imp (fun h => Nat.ne_of_lt h))]

/-- Non-singleton support rules out an input node, so every single reference
is an actual allocated addition, including references reused across levels. -/
theorem singleRefs_subset_additionIds (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 4 ≤ points.toFinset.card) : singleRefs points ⊆ additionIds (circuit points).nodes := by
  intro i hi
  obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hi)
  have hspec := circuit_single_support points hs a ha
  rw [he] at hspec
  have hbound : i < (circuit points).nodes.length := hspec.1
  have hsupport : (circuit points).nodes[i].support = singleSupport points a := by
    rw [← hspec.2, refSupport_some _ i hbound]
  have hnode := DAGValueTransfer.validFrom_get [] (circuit points).nodes
    (circuit_correct points hs).valid i hbound
  cases hk : (circuit points).nodes[i].kind with
  | input p =>
    have heq : (circuit points).nodes[i].support = {p} := by
      simpa only [Node.Valid, hk] using hnode
    have hc := singleSupport_card_two points hs hcard a
    rw [← hsupport, heq, Finset.card_singleton] at hc
    omega
  | add l r =>
    exact (mem_additionIds _ i).mpr ⟨_, List.getElem?_eq_getElem hbound, l, r, hk⟩

/-- There are exactly n distinct unused single additions once n is at least
four. No executable count of the constructed DAG appears in the proof. -/
theorem singleSavings_eq_length (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 4 ≤ points.toFinset.card) : singleSavings points = points.length := by
  unfold singleSavings
  rw [additionCountFrom_eq_card _ _ (singleRefs_subset_additionIds points hs hcard),
    singleRefs_card points hs (by omega)]

/-- The concrete 49-vertex single-output pruning count follows by substitution
into the structural theorem, without constructing or checking its DAG. -/
theorem singleSavings_49 : singleSavings (List.range 49) = 49 := by
  simpa only [List.length_range] using
    singleSavings_eq_length (List.range 49) List.pairwise_lt_range (by
      rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
      decide)

/-- Transfer the symbolic single-output saving to actual compiler budgets. -/
theorem compile_bounds_without_single_outputs (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 4 ≤ points.toFinset.card) (capacity : ℕ)
    (hc : DAGAllocator.additionCount (circuit points).nodes ≤ capacity) :
    (DAGAllocator.compile (circuit points).nodes (outputRefs points)).state.next ≤
        (capacity - points.length) + (pairs points).length ∧
      (DAGAllocator.compile (circuit points).nodes (outputRefs points)).program.length ≤
        2 * (capacity - points.length) + (pairs points).length := by
  simpa only [singleSavings_eq_length points hs hcard] using
    compile_bounds_without_singles points hs (by omega) capacity hc

/-- Other structurally dead additions may be credited alongside the singles
once their actual identifiers are disjoint. Finset cardinality prevents any
saving from being counted twice across recursive construction stages. -/
theorem compile_bounds_without_singles_and_dead (points : List ℕ) (hs : points.Pairwise (· < ·))
    (hcard : 4 ≤ points.toFinset.card) (extra : Finset ℕ)
    (hextra : extra ⊆ additionIds (circuit points).nodes)
    (hdis : Disjoint (singleRefs points) extra)
    (hdead : ∀ i ∈ extra, i ∉ mark (circuit points).nodes (outputRefs points).toFinset)
    (capacity : ℕ) (hc : DAGAllocator.additionCount (circuit points).nodes ≤ capacity) :
    (DAGAllocator.compile (circuit points).nodes (outputRefs points)).state.next ≤
        (capacity - (points.length + extra.card)) + (pairs points).length ∧
      (DAGAllocator.compile (circuit points).nodes (outputRefs points)).program.length ≤
        2 * (capacity - (points.length + extra.card)) + (pairs points).length := by
  have hactive : Disjoint (mark (circuit points).nodes (outputRefs points).toFinset)
      (singleRefs points ∪ extra) := by
    apply Finset.disjoint_left.mpr
    intro i hi hmem
    rcases Finset.mem_union.mp hmem with hsingle | hother
    · obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hsingle)
      exact single_output_not_marked points hs (by omega) a ha i he hi
    · exact hdead i hother hi
  have hcount := additionCountFrom_eq_card (circuit points).nodes (singleRefs points ∪ extra)
    (Finset.union_subset (singleRefs_subset_additionIds points hs hcard) hextra)
  rw [Finset.card_union_of_disjoint hdis, singleRefs_card points hs (by omega)] at hcount
  have h := additionCountFrom_add_le 0 (circuit points).nodes
    (mark (circuit points).nodes (outputRefs points).toFinset) (singleRefs points ∪ extra) hactive
  rw [hcount] at h
  apply compile_bounds_of_active points hs (capacity - (points.length + extra.card))
  omega

end IntegerMultBounds.Networks.PairedInitialGraph
