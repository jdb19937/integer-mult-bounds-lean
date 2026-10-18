module

public import IntegerMultBounds.Networks.PairedCircuit
public import IntegerMultBounds.Networks.DAGAllocatorBudget
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Algebra.Group.Action.Defs

/-! Compositional bounds for the actual paired-circuit constructors. These count
allocated addition nodes, so zero elision and support interning can only improve
the bounds. No generated certificate or concrete vertex count is required. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedCircuitBudget

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator

variable {ι X Y : Type*} [DecidableEq ι]

theorem smartAdd_additions_le (nodes : List (Node ι)) (l r : Ref) :
    additionCount (smartAdd nodes l r).1 ≤ additionCount nodes + 1 := by
  cases l <;> cases r
  all_goals simp only [smartAdd]
  all_goals try omega
  unfold intern
  split <;> simp [additionCount, List.countP_append]

omit [DecidableEq ι] in
/-- Sum the per-iteration bounds of an actual state-threading constructor loop. -/
theorem mapBuild_additions_le (f : List (Node ι) → X → List (Node ι) × Y)
    (budget : X → ℕ) (nodes : List (Node ι)) (xs : List X)
    (h : ∀ ns x, additionCount (f ns x).1 ≤ additionCount ns + budget x) :
    additionCount (mapBuild f nodes xs).1 ≤ additionCount nodes + (xs.map budget).sum := by
  induction xs generalizing nodes with
  | nil => simp [mapBuild]
  | cons x xs ih =>
    have hs := h nodes x
    have ht := ih (f nodes x).1
    simp only [mapBuild, List.map_cons, List.sum_cons]
    omega

/-- Balanced summation creates at most one fewer addition than input references,
even when some references are absent or the union was already interned. -/
theorem total_additions_le (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (DisjointBalanced.total nodes refs).1 ≤
      additionCount nodes + (refs.length - 1) := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction generalizing nodes with
  | h refs ih =>
    cases refs with
    | nil => simp [DisjointBalanced.total]
    | cons r tail =>
      cases tail with
      | nil => simp [DisjointBalanced.total]
      | cons s rs =>
        let values := r :: s :: rs
        let left := values.take (values.length / 2)
        let right := values.drop (values.length / 2)
        have hlen : 2 ≤ values.length := by simp [values]
        have hl : left.length < values.length := by simp only [left, List.length_take]; omega
        have hr : right.length < values.length := by simp only [right, List.length_drop]; omega
        have hlpos : 0 < left.length := by simp only [left, List.length_take]; omega
        have hrpos : 0 < right.length := by simp only [right, List.length_drop]; omega
        have hsum : left.length + right.length = values.length := by
          simp only [left, right, List.length_take, List.length_drop]; omega
        have hleft := ih left hl nodes
        have hright := ih right hr (DisjointBalanced.total nodes left).1
        have hadd := smartAdd_additions_le (DisjointBalanced.total
          (DisjointBalanced.total nodes left).1 right).1
          (DisjointBalanced.total nodes left).2
          (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2
        rw [DisjointBalanced.total]
        change additionCount (smartAdd (DisjointBalanced.total
          (DisjointBalanced.total nodes left).1 right).1
          (DisjointBalanced.total nodes left).2
          (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2).1 ≤ _
        change _ ≤ additionCount nodes + (values.length - 1)
        omega

theorem prefixBuild_additions_le (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    additionCount (prefixBuild nodes acc refs).1 ≤ additionCount nodes + refs.length := by
  induction refs generalizing nodes acc with
  | nil => simp [prefixBuild]
  | cons r refs ih =>
    have hs := smartAdd_additions_le nodes acc r
    have ht := ih (smartAdd nodes acc r).1 (smartAdd nodes acc r).2
    simp only [prefixBuild, List.length_cons]
    omega

theorem suffixBuild_additions_le (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (suffixBuild nodes refs).1 ≤ additionCount nodes + refs.length := by
  induction refs generalizing nodes with
  | nil => simp [suffixBuild]
  | cons r refs ih =>
    have ht := ih nodes
    have hs := smartAdd_additions_le (suffixBuild nodes refs).1 r
      ((suffixBuild nodes refs).2.headD none)
    simp only [suffixBuild, List.length_cons]
    omega

theorem vectorFalse_additions_le (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (vectorFalse nodes refs).nodes ≤ additionCount nodes + 3 * refs.length := by
  have hp := prefixBuild_additions_le nodes none refs
  have hs := suffixBuild_additions_le (prefixBuild nodes none refs).1 refs
  have ho := mapBuild_additions_le (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2)
    (fun _ => 1) (suffixBuild (prefixBuild nodes none refs).1 refs).1
    ((prefixBuild nodes none refs).2.zip
      (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail)
    (fun ns p => smartAdd_additions_le ns p.1 p.2)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one, List.length_zip,
    prefixBuild_length, List.length_tail, suffixBuild_length] at ho
  change additionCount (mapBuild _ _ _).1 ≤ _
  omega


theorem vectorTail_additions_le (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (vectorTail nodes refs).nodes ≤ additionCount nodes + 3 * refs.length := by
  cases refs with
  | nil => simp [vectorTail]
  | cons carry values =>
    have hp := prefixBuild_additions_le nodes none (carry :: values)
    have hs := suffixBuild_additions_le (prefixBuild nodes none (carry :: values)).1 values.tail
    have ho := mapBuild_additions_le (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2)
      (fun _ => 1) (suffixBuild (prefixBuild nodes none (carry :: values)).1 values.tail).1
      (((prefixBuild nodes none (carry :: values)).2.drop 1).zip
        ((suffixBuild (prefixBuild nodes none (carry :: values)).1 values.tail).2.take values.length))
      (fun ns p => smartAdd_additions_le ns p.1 p.2)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one, List.length_zip,
      List.length_drop, prefixBuild_length, List.length_take, suffixBuild_length] at ho
    have ht : values.tail.length ≤ values.length := by simp
    change additionCount (mapBuild _ _ _).1 ≤ _
    simp only [List.length_cons] at hp ⊢
    omega

/-- A state-independent budget for each level's actual balanced totals. The
total is charged as one addition per removed term of the last single. -/
def baseBudget (points : List ℕ) (edges : EdgeTable) (weights : WeightTable) : ℕ :=
  (points.map (fun a => (query edges weights [a]).length - 1)).sum +
    ((pairs points).map (fun p => (query edges weights [p.1, p.2]).length - 1)).sum +
    (match points.getLast? with
      | none => (query edges weights []).length - 1
      | some a => (removed edges weights [a]).length)

theorem baseBlock_additions_le (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) :
    additionCount (baseBlock nodes points edges weights).nodes ≤
      additionCount nodes + baseBudget points edges weights := by
  let one := mapBuild (fun ns a =>
    let r := DisjointBalanced.total ns (query edges weights [a]); (r.1, (a, r.2))) nodes points
  have ho := mapBuild_additions_le (fun ns a =>
    let r := DisjointBalanced.total ns (query edges weights [a]); (r.1, (a, r.2)))
    (fun a => (query edges weights [a]).length - 1) nodes points
    (fun ns a => total_additions_le ns (query edges weights [a]))
  let two := mapBuild (fun ns (p : ℕ × ℕ) =>
    let r := DisjointBalanced.total ns (query edges weights [p.1, p.2]); (r.1, (p, r.2))) one.1 (pairs points)
  have hp := mapBuild_additions_le (fun ns (p : ℕ × ℕ) =>
    let r := DisjointBalanced.total ns (query edges weights [p.1, p.2]); (r.1, (p, r.2)))
    (fun p => (query edges weights [p.1, p.2]).length - 1) one.1
    (pairs points) (fun ns p => total_additions_le ns (query edges weights [p.1, p.2]))
  change additionCount one.1 ≤ _ at ho
  change additionCount two.1 ≤ _ at hp
  have ht : additionCount (baseBlock nodes points edges weights).nodes ≤ additionCount two.1 +
      (match points.getLast? with
        | none => (query edges weights []).length - 1
        | some a => (removed edges weights [a]).length) := by
    cases hl : points.getLast? with
    | none =>
      have h := total_additions_le two.1 (query edges weights [])
      simpa only [baseBlock, hl] using h
    | some a =>
      have h1 := total_additions_le two.1 (removed edges weights [a])
      have h2 := smartAdd_additions_le (DisjointBalanced.total two.1 (removed edges weights [a])).1
        (lookup one.2 a) (DisjointBalanced.total two.1 (removed edges weights [a])).2
      have h : additionCount (smartAdd (DisjointBalanced.total two.1 (removed edges weights [a])).1
          (lookup one.2 a) (DisjointBalanced.total two.1 (removed edges weights [a])).2).1 ≤
          additionCount two.1 + (removed edges weights [a]).length := by
        cases hre : removed edges weights [a] with
        | nil =>
          simp only [DisjointBalanced.total]
          cases lookup one.2 a <;> simp [smartAdd]
        | cons r rs =>
          rw [hre] at h1 h2
          simp only [List.length_cons] at h1 ⊢
          omega
      simpa only [baseBlock, hl] using h
  unfold baseBudget
  omega

theorem crossRefs_length (edges : EdgeTable) (left right : List ℕ) :
    (crossRefs edges left right).length = left.length * right.length := by
  induction left with
  | nil => simp [crossRefs]
  | cons a left ih => simp [crossRefs, List.flatMap_cons, Nat.add_mul, Nat.add_comm] at *

def coarseEdgeBudget (groups : List (List ℕ)) : ℕ :=
  ((pairs (List.range groups.length)).map (fun ij =>
    (groupAt groups ij.1).length * (groupAt groups ij.2).length - 1)).sum

def coarseWeightBudget (groups : List (List ℕ)) : ℕ :=
  ((List.range groups.length).map (fun i =>
    (groupAt groups i).length + (pairs (groupAt groups i)).length - 1)).sum

theorem coarseEdges_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) : additionCount (coarseEdges nodes groups edges).1 ≤
      additionCount nodes + coarseEdgeBudget groups := by
  apply mapBuild_additions_le
  intro ns ij
  simpa only [crossRefs_length] using total_additions_le ns
    (crossRefs edges (groupAt groups ij.1) (groupAt groups ij.2))

theorem coarseWeights_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) :
    additionCount (coarseWeights nodes groups edges weights).1 ≤
      additionCount nodes + coarseWeightBudget groups := by
  apply mapBuild_additions_le
  intro ns i
  simpa only [List.length_append, List.length_map] using total_additions_le ns
    ((groupAt groups i).map (lookup weights) ++
      (pairs (groupAt groups i)).map (fun p => edgeLookup edges p.1 p.2))

def stripBudget (groups : List (List ℕ)) (ia : ℕ × ℕ) : ℕ :=
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  (remaining.length - 1) +
    (other.map (fun j => remaining.length * (groupAt groups j).length - 1)).sum +
    3 * (1 + other.length)

theorem buildStrip_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) :
    additionCount (buildStrip nodes groups edges weights ia).1 ≤
      additionCount nodes + stripBudget groups ia := by
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  let carry := DisjointBalanced.total nodes (remaining.map (lookup weights))
  let vals := mapBuild (fun ns j => DisjointBalanced.total ns
    (crossRefs edges remaining (groupAt groups j))) carry.1 other
  have hc := total_additions_le nodes (remaining.map (lookup weights))
  have hv := mapBuild_additions_le (fun ns j => DisjointBalanced.total ns
    (crossRefs edges remaining (groupAt groups j)))
    (fun j => remaining.length * (groupAt groups j).length - 1) carry.1 other
    (fun ns j => by simpa only [crossRefs_length] using
      total_additions_le ns (crossRefs edges remaining (groupAt groups j)))
  have hs := vectorTail_additions_le vals.1 (carry.2 :: vals.2)
  have hlen : vals.2.length = other.length := mapBuild_length _ _ _
  simp only [List.length_map] at hc
  simp only [List.length_cons, hlen] at hs
  change additionCount (vectorTail vals.1 (carry.2 :: vals.2)).nodes ≤ _
  change _ ≤ additionCount nodes + ((remaining.length - 1) +
    (other.map (fun j => remaining.length * (groupAt groups j).length - 1)).sum +
      3 * (1 + other.length))
  change additionCount carry.1 ≤ _ at hc
  change additionCount vals.1 ≤ _ at hv
  omega

def stripsBudget (groups : List (List ℕ)) : ℕ := ((members groups).map (stripBudget groups)).sum

theorem buildStrips_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) :
    additionCount (buildStrips nodes groups edges weights).1 ≤
      additionCount nodes + stripsBudget groups :=
  mapBuild_additions_le _ _ _ _ (fun ns ia => buildStrip_additions_le ns groups edges weights ia)

theorem buildSingles_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) :
    additionCount (buildSingles nodes groups outside strips).1 ≤
      additionCount nodes + (members groups).length := by
  have h := mapBuild_additions_le (fun ns ia =>
    let r := smartAdd ns (lookup outside ia.1) (stripLookup strips ia.2).total
    (r.1, (ia.2, r.2))) (fun _ => 1) nodes (members groups)
    (fun ns ia => smartAdd_additions_le ns _ _)
  simpa only [buildSingles, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one] using h

def crossLeftBudget (groups : List (List ℕ)) (ij : ℕ × ℕ) (a : ℕ) : ℕ :=
  1 + ((groupAt groups ij.2).map (fun b =>
    (((groupAt groups ij.1).filter (· != a)).length *
      ((groupAt groups ij.2).filter (· != b)).length - 1) + 2)).sum

theorem buildCrossLeft_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a : ℕ) :
    additionCount (buildCrossLeft nodes groups edges far strips ij a).1 ≤
      additionCount nodes + crossLeftBudget groups ij a := by
  have hl := smartAdd_additions_le nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)
  let body := fun (ns : List (Node ι)) b =>
    let cross := DisjointBalanced.total ns (crossRefs edges
      ((groupAt groups ij.1).filter (· != a)) ((groupAt groups ij.2).filter (· != b)))
    let right := smartAdd cross.1 (lookup (stripLookup strips b).outside ij.1) cross.2
    let result := smartAdd right.1
      (smartAdd nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)).2 right.2
    (result.1, ((a, b), result.2))
  have hbody : ∀ ns b, additionCount (body ns b).1 ≤ additionCount ns +
      (((groupAt groups ij.1).filter (· != a)).length *
        ((groupAt groups ij.2).filter (· != b)).length - 1) + 2 := by
    intro ns b
    have hc := total_additions_le ns (crossRefs edges
      ((groupAt groups ij.1).filter (· != a)) ((groupAt groups ij.2).filter (· != b)))
    simp only [crossRefs_length] at hc
    let cross := DisjointBalanced.total ns (crossRefs edges
      ((groupAt groups ij.1).filter (· != a)) ((groupAt groups ij.2).filter (· != b)))
    let right := smartAdd cross.1 (lookup (stripLookup strips b).outside ij.1) cross.2
    have hr := smartAdd_additions_le cross.1 (lookup (stripLookup strips b).outside ij.1) cross.2
    have ho := smartAdd_additions_le right.1
      (smartAdd nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)).2 right.2
    change additionCount cross.1 ≤ _ at hc
    change additionCount right.1 ≤ _ at hr
    change additionCount (smartAdd right.1
      (smartAdd nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)).2 right.2).1 ≤ _
    omega
  have h := mapBuild_additions_le body (fun b =>
    (((groupAt groups ij.1).filter (· != a)).length *
      ((groupAt groups ij.2).filter (· != b)).length - 1) + 2)
    (smartAdd nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)).1
    (groupAt groups ij.2) (fun ns b => by have := hbody ns b; omega)
  change additionCount (mapBuild body _ _).1 ≤ _
  unfold crossLeftBudget
  omega

def crossGroupBudget (groups : List (List ℕ)) (ij : ℕ × ℕ) : ℕ :=
  ((groupAt groups ij.1).map (crossLeftBudget groups ij)).sum

def crossBudget (groups : List (List ℕ)) : ℕ :=
  ((pairs (List.range groups.length)).map (crossGroupBudget groups)).sum

theorem buildCrossGroup_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) :
    additionCount (buildCrossGroup nodes groups edges far strips ij).1 ≤
      additionCount nodes + crossGroupBudget groups ij :=
  mapBuild_additions_le _ _ _ _
    (fun ns a => buildCrossLeft_additions_le ns groups edges far strips ij a)

theorem buildCrossPairs_additions_le (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) :
    additionCount (buildCrossPairs nodes groups edges far strips).1 ≤
      additionCount nodes + crossBudget groups :=
  mapBuild_additions_le _ _ _ _
    (fun ns ij => buildCrossGroup_additions_le ns groups edges far strips ij)

def reconstructBudget (groups : List (List ℕ)) : ℕ :=
  stripsBudget groups + (members groups).length + crossBudget groups

theorem reconstruct_additions_le (groups : List (List ℕ)) (edges : EdgeTable)
    (weights : WeightTable) (coarse : BlockResult ι) :
    additionCount (reconstruct groups edges weights coarse).nodes ≤
      additionCount coarse.nodes + reconstructBudget groups := by
  have ht := buildStrips_additions_le coarse.nodes groups edges weights
  have hs := buildSingles_additions_le (buildStrips coarse.nodes groups edges weights).1
    groups coarse.one (buildStrips coarse.nodes groups edges weights).2
  have hc := buildCrossPairs_additions_le (buildSingles
    (buildStrips coarse.nodes groups edges weights).1 groups coarse.one
    (buildStrips coarse.nodes groups edges weights).2).1 groups edges coarse.two
    (buildStrips coarse.nodes groups edges weights).2
  simp only [reconstruct, reconstructBudget]
  try dsimp only at *
  omega

private theorem sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (k : ℕ)
    (h : ∀ x, f x ≤ k) : (xs.map f).sum ≤ xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem query_length_le (edges : EdgeTable) (weights : WeightTable) (excluded : List ℕ) :
    (query edges weights excluded).length ≤ edges.length + weights.length := by
  have he := List.length_filter_le (fun e : (ℕ × ℕ) × Ref =>
    decide (e.1.1 ∉ excluded ∧ e.1.2 ∉ excluded)) edges
  have hw := List.length_filter_le (fun w : ℕ × Ref => decide (w.1 ∉ excluded)) weights
  simpa only [query, List.length_append, List.length_map] using Nat.add_le_add he hw

/-- A conservative base-case bound, uniform in edge values and input node state. -/
def baseBound (points : List ℕ) (edgeCount weightCount : ℕ) : ℕ :=
  (1 + points.length + (pairs points).length) * (edgeCount + weightCount)

theorem removed_length_le (edges : EdgeTable) (weights : WeightTable) (excluded : List ℕ) :
    (removed edges weights excluded).length ≤ edges.length + weights.length := by
  have he := List.length_filter_le (fun e : (ℕ × ℕ) × Ref =>
    !decide (e.1.1 ∉ excluded ∧ e.1.2 ∉ excluded)) edges
  have hw := List.length_filter_le (fun w : ℕ × Ref => !decide (w.1 ∉ excluded)) weights
  simpa only [removed, List.length_append, List.length_map] using Nat.add_le_add he hw

theorem baseBudget_le (points : List ℕ) (edges : EdgeTable) (weights : WeightTable) :
    baseBudget points edges weights ≤ baseBound points edges.length weights.length := by
  have h (excluded : List ℕ) := Nat.sub_le_sub_right (query_length_le edges weights excluded) 1
  have ho := sum_map_le points (fun a => (query edges weights [a]).length - 1)
    (edges.length + weights.length) (fun a => (h [a]).trans (Nat.sub_le _ _))
  have hp := sum_map_le (pairs points) (fun p => (query edges weights [p.1, p.2]).length - 1)
    (edges.length + weights.length) (fun p => (h [p.1, p.2]).trans (Nat.sub_le _ _))
  have ht : (match points.getLast? with
      | none => (query edges weights []).length - 1
      | some a => (removed edges weights [a]).length) ≤ edges.length + weights.length := by
    cases points.getLast? with
    | none => exact (h []).trans (Nat.sub_le _ _)
    | some a => exact removed_length_le edges weights [a]
  simp only [baseBudget, baseBound, Nat.add_mul, Nat.one_mul]
  omega

/-- A computable budget depending only on graph shape and input table sizes.
Every recursive level uses the same reusable constructor bounds. This is a
conservative structural budget; tighter pruning or interning proofs may replace
it without changing correctness or the compiler's resource accounting. -/
def blockBudget (points : List ℕ) (edgeCount weightCount : ℕ) : ℕ :=
  if points.length ≤ 4 then baseBound points edgeCount weightCount else
    let groups := PairGrouping.groups points
    coarseEdgeBudget groups + coarseWeightBudget groups +
      blockBudget (List.range groups.length) (pairs (List.range groups.length)).length groups.length +
      reconstructBudget groups
termination_by points.length
decreasing_by
  simp only [List.length_range]
  exact PairGrouping.length_groups_lt points (by omega)

/-- The literal recursive circuit satisfies the shape budget for every input
state, including states that already contain reusable supports. -/
theorem block_additions_le (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) :
    additionCount (block nodes points edges weights).nodes ≤
      additionCount nodes + blockBudget points edges.length weights.length := by
  induction points using (measure (fun ps : List ℕ => ps.length)).wf.induction
      generalizing nodes edges weights with
  | h points ih =>
    by_cases hsmall : points.length ≤ 4
    · rw [block_small _ _ _ _ hsmall, blockBudget, ite_eq_left hsmall]
      exact (baseBlock_additions_le nodes points edges weights).trans
        (Nat.add_le_add_left (baseBudget_le points edges weights) _)
    · have hlarge : 4 < points.length := by omega
      let groups := PairGrouping.groups points
      let ce := coarseEdges nodes groups edges
      let cw := coarseWeights ce.1 groups edges weights
      have hlen : (List.range groups.length).length < points.length := by
        simpa [groups] using PairGrouping.length_groups_lt points hlarge
      have he := coarseEdges_additions_le nodes groups edges
      have hw := coarseWeights_additions_le ce.1 groups edges weights
      have hr := ih (List.range groups.length) hlen cw.1 ce.2 cw.2
      have hc := reconstruct_additions_le groups edges weights
        (block cw.1 (List.range groups.length) ce.2 cw.2)
      have helen : ce.2.length = (pairs (List.range groups.length)).length :=
        mapBuild_length _ _ _
      have hwlen : cw.2.length = groups.length := by
        simpa only [cw, coarseWeights, List.length_range] using mapBuild_length
          (fun (ns : List (Node ι)) i => let g := groupAt groups i
            let refs := g.map (lookup weights) ++ (pairs g).map (fun p => edgeLookup edges p.1 p.2)
            let r := DisjointBalanced.total ns refs
            (r.1, (i, r.2))) ce.1 (List.range groups.length)
      rw [helen, hwlen] at hr
      rw [block_large _ _ _ _ hlarge, blockBudget, ite_eq_right hsmall]
      change additionCount (reconstruct groups edges weights
        (block cw.1 (List.range groups.length) ce.2 cw.2)).nodes ≤ _
      change additionCount ce.1 ≤ _ at he
      change additionCount cw.1 ≤ _ at hw
      change _ ≤ additionCount nodes + (coarseEdgeBudget groups + coarseWeightBudget groups +
        blockBudget (List.range groups.length) (pairs (List.range groups.length)).length groups.length +
        reconstructBudget groups)
      omega

end IntegerMultBounds.Networks.PairedCircuitBudget
