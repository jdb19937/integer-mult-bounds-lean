module

public import IntegerMultBounds.Networks.PairedInitialGraph
public import IntegerMultBounds.Networks.DisjointUnique
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Support uniqueness of the actual recursive paired constructor. Every stage
uses the persistent intern bank, so uniqueness follows by composition for all
graph sizes rather than by checking a generated list of support masks. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedCircuitUnique

open DisjointCircuit DisjointBuilder DisjointUnique PairedCircuit

variable {ι X Y : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Any stateful loop preserves support uniqueness when each body does. -/
theorem mapBuild_nodup (f : List (Node ι) → X → List (Node ι) × Y)
    (hf : ∀ ns x, (ns.map Node.support).Nodup → ((f ns x).1.map Node.support).Nodup)
    (nodes : List (Node ι)) (xs : List X) (hn : (nodes.map Node.support).Nodup) :
    ((mapBuild f nodes xs).1.map Node.support).Nodup := by
  induction xs generalizing nodes with
  | nil => exact hn
  | cons x xs ih => exact ih (f nodes x).1 (hf nodes x hn)

theorem prefixBuild_nodup (nodes : List (Node ι)) (acc : Ref) (refs : List Ref)
    (hn : (nodes.map Node.support).Nodup) :
    ((prefixBuild nodes acc refs).1.map Node.support).Nodup := by
  induction refs generalizing nodes acc with
  | nil => exact hn
  | cons r rs ih => exact ih _ _ (smartAdd_nodup nodes acc r hn)

theorem suffixBuild_nodup (nodes : List (Node ι)) (refs : List Ref)
    (hn : (nodes.map Node.support).Nodup) :
    ((suffixBuild nodes refs).1.map Node.support).Nodup := by
  induction refs with
  | nil => exact hn
  | cons r rs ih => exact smartAdd_nodup _ _ _ ih

theorem vectorFalse_nodup (nodes : List (Node ι)) (refs : List Ref)
    (hn : (nodes.map Node.support).Nodup) :
    ((vectorFalse nodes refs).nodes.map Node.support).Nodup := by
  apply mapBuild_nodup _ (fun ns p h => smartAdd_nodup ns p.1 p.2 h)
  exact suffixBuild_nodup _ refs (prefixBuild_nodup nodes none refs hn)

theorem vectorTail_nodup (nodes : List (Node ι)) (refs : List Ref)
    (hn : (nodes.map Node.support).Nodup) :
    ((vectorTail nodes refs).nodes.map Node.support).Nodup := by
  cases refs with
  | nil => exact hn
  | cons carry values =>
    apply mapBuild_nodup _ (fun ns p h => smartAdd_nodup ns p.1 p.2 h)
    exact suffixBuild_nodup _ _ (prefixBuild_nodup nodes none _ hn)

theorem baseBlock_nodup (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hn : (nodes.map Node.support).Nodup) :
    ((baseBlock nodes points edges weights).nodes.map Node.support).Nodup := by
  have hone := mapBuild_nodup (fun ns a =>
    let r := DisjointBalanced.total ns (query edges weights [a]); (r.1, (a, r.2)))
    (fun ns a h => balanced_total_nodup ns _ h) nodes points hn
  have htwo := mapBuild_nodup (fun ns (p : ℕ × ℕ) =>
    let r := DisjointBalanced.total ns (query edges weights [p.1, p.2]); (r.1, (p, r.2)))
    (fun ns p h => balanced_total_nodup ns _ h) _ (pairs points) hone
  cases hl : points.getLast? with
  | none =>
    simpa only [baseBlock, hl] using balanced_total_nodup _ (query edges weights []) htwo
  | some a =>
    simpa only [baseBlock, hl] using smartAdd_nodup _ _ _
      (balanced_total_nodup _ (removed edges weights [a]) htwo)

theorem coarseEdges_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (hn : (nodes.map Node.support).Nodup) :
    ((coarseEdges nodes groups edges).1.map Node.support).Nodup := by
  refine mapBuild_nodup _ ?_ nodes _ hn
  intro ns p h
  exact balanced_total_nodup ns _ h

theorem coarseWeights_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (hn : (nodes.map Node.support).Nodup) :
    ((coarseWeights nodes groups edges weights).1.map Node.support).Nodup := by
  refine mapBuild_nodup _ ?_ nodes _ hn
  intro ns i h
  exact balanced_total_nodup ns _ h

theorem buildStrip_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) (hn : (nodes.map Node.support).Nodup) :
    ((buildStrip nodes groups edges weights ia).1.map Node.support).Nodup := by
  apply vectorTail_nodup
  apply mapBuild_nodup _ (fun ns j h => balanced_total_nodup ns _ h)
  exact balanced_total_nodup nodes _ hn

theorem buildStrips_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (hn : (nodes.map Node.support).Nodup) :
    ((buildStrips nodes groups edges weights).1.map Node.support).Nodup :=
  mapBuild_nodup _ (fun ns ia h => buildStrip_nodup ns groups edges weights ia h) nodes _ hn

theorem buildSingles_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) (hn : (nodes.map Node.support).Nodup) :
    ((buildSingles nodes groups outside strips).1.map Node.support).Nodup := by
  refine mapBuild_nodup _ ?_ nodes _ hn
  intro ns ia h
  exact smartAdd_nodup ns _ _ h

theorem buildCrossLeft_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a : ℕ)
    (hn : (nodes.map Node.support).Nodup) :
    ((buildCrossLeft nodes groups edges far strips ij a).1.map Node.support).Nodup := by
  refine mapBuild_nodup _ ?_ _ _ ?_
  · intro ns b h
    apply smartAdd_nodup
    apply smartAdd_nodup
    exact balanced_total_nodup ns _ h
  · exact smartAdd_nodup nodes _ _ hn

theorem buildCrossGroup_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ)
    (hn : (nodes.map Node.support).Nodup) :
    ((buildCrossGroup nodes groups edges far strips ij).1.map Node.support).Nodup :=
  mapBuild_nodup _ (fun ns a h => buildCrossLeft_nodup ns groups edges far strips ij a h) nodes _ hn

theorem buildCrossPairs_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (hn : (nodes.map Node.support).Nodup) :
    ((buildCrossPairs nodes groups edges far strips).1.map Node.support).Nodup :=
  mapBuild_nodup _ (fun ns ij h => buildCrossGroup_nodup ns groups edges far strips ij h) nodes _ hn

theorem reconstruct_nodup (groups : List (List ℕ)) (edges : EdgeTable)
    (weights : WeightTable) (coarse : BlockResult ι) (hn : (coarse.nodes.map Node.support).Nodup) :
    ((reconstruct groups edges weights coarse).nodes.map Node.support).Nodup := by
  apply buildCrossPairs_nodup
  apply buildSingles_nodup
  exact buildStrips_nodup coarse.nodes groups edges weights hn

/-- Support interning preserves uniqueness through the entire recursion,
including zero elision, aliases, and sharing between construction stages. -/
theorem block_nodup (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hn : (nodes.map Node.support).Nodup) :
    ((block nodes points edges weights).nodes.map Node.support).Nodup := by
  induction points using (measure (fun ps : List ℕ => ps.length)).wf.induction
      generalizing nodes edges weights with
  | h points ih =>
    by_cases hsmall : points.length ≤ 4
    · rw [block_small _ _ _ _ hsmall]
      exact baseBlock_nodup nodes points edges weights hn
    · have hlarge : 4 < points.length := by omega
      rw [block_large _ _ _ _ hlarge]
      apply reconstruct_nodup
      have hlen : (List.range (PairGrouping.groups points).length).length < points.length := by
        simpa only [List.length_range] using PairGrouping.length_groups_lt points hlarge
      exact ih (List.range (PairGrouping.groups points).length) hlen _ _ _
        (coarseWeights_nodup _ _ _ _ (coarseEdges_nodup nodes _ edges hn))

end IntegerMultBounds.Networks.PairedCircuitUnique

namespace IntegerMultBounds.Networks.PairedInitialGraph

open DisjointCircuit DisjointUnique PairedCircuitCorrect PairedCircuitUnique

/-- Singleton inputs have distinct supports for any sorted vertex list. -/
theorem nodes_nodup (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    ((nodes points).map Node.support).Nodup := by
  simp only [nodes, List.map_map, Function.comp_def]
  exact (pairs_nodup points hs).map (fun _ _ h => Finset.singleton_injective h)

/-- The actual local circuit has distinct nonempty support identifiers for
all graph sizes. No generated uniqueness certificate is required. -/
theorem circuit_unique (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    Unique (circuit points).nodes :=
  unique_of_valid_nodup _ (circuit_correct points hs).valid
    (block_nodup _ _ _ _ (nodes_nodup points hs))

theorem circuit49_unique : Unique (circuit (List.range 49)).nodes :=
  circuit_unique _ List.pairwise_lt_range

end IntegerMultBounds.Networks.PairedInitialGraph
