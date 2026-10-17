module

public import IntegerMultBounds.Networks.PairedCircuit
public import IntegerMultBounds.Networks.DAGAllocatorBudget
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! The paired constructor commutes with injective relabeling of input atoms.
Interning compares supports only, so relabeled supports hit and miss exactly
as before; every reference and node kind is unchanged. Counts, markings and
pruning credits proved in one input alphabet therefore hold in any other. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedRename

open DisjointCircuit DisjointBuilder PairedCircuit

variable {α β : Type*} (e : α ↪ β)

def kind : Kind α → Kind β
  | .input a => .input (e a)
  | .add l r => .add l r

def node (n : Node α) : Node β := ⟨kind e n.kind, n.support.map e⟩

theorem supports_map (ns : List (Node α)) :
    (ns.map (node e)).map Node.support = (ns.map Node.support).map (Finset.map e) := by
  simp [node, Function.comp_def]

variable [DecidableEq α] [DecidableEq β]

theorem findSupport_map (s : Finset α) (prior : List (Finset α)) :
    findSupport (s.map e) (prior.map (Finset.map e)) = findSupport s prior := by
  induction prior with
  | nil => rfl
  | cons t prior ih => simp [findSupport, ih, Finset.map_inj]

theorem intern_map (ns : List (Node α)) (n : Node α) :
    intern (ns.map (node e)) (node e n) = ((intern ns n).1.map (node e), (intern ns n).2) := by
  unfold intern
  rw [supports_map]
  change (match findSupport (n.support.map e) ((ns.map Node.support).map (Finset.map e)) with
    | some i => (ns.map (node e), i)
    | none => (ns.map (node e) ++ [node e n], (ns.map (node e)).length)) = _
  rw [findSupport_map]
  cases findSupport n.support (ns.map Node.support) <;> simp

omit [DecidableEq α] [DecidableEq β] in
theorem refSupport_map (ns : List (Node α)) (r : Ref) :
    refSupport (ns.map (node e)) r = (refSupport ns r).map e := by
  cases r with
  | none => simp [refSupport]
  | some i =>
    simp only [refSupport, supports_map, List.getElem?_map]
    cases ns[i]? <;> simp

theorem smartAdd_map (ns : List (Node α)) (l r : Ref) :
    smartAdd (ns.map (node e)) l r = ((smartAdd ns l r).1.map (node e), (smartAdd ns l r).2) := by
  cases l with
  | none => rfl
  | some l =>
    cases r with
    | none => rfl
    | some r =>
      simp only [smartAdd, refSupport_map, ← Finset.map_union]
      exact congrArg (fun x : List (Node β) × ℕ => (x.1, some x.2))
        (intern_map e ns ⟨.add l r, refSupport ns (some l) ∪ refSupport ns (some r)⟩)

theorem total_map (ns : List (Node α)) (refs : List Ref) :
    DisjointBalanced.total (ns.map (node e)) refs =
      ((DisjointBalanced.total ns refs).1.map (node e), (DisjointBalanced.total ns refs).2) := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction generalizing ns with
  | h refs ih =>
    match refs with
    | [] => simp only [DisjointBalanced.total]
    | [x] => simp only [DisjointBalanced.total]
    | x :: y :: rs =>
      rw [DisjointBalanced.total, DisjointBalanced.total]
      have hl : ((x :: y :: rs).take ((x :: y :: rs).length / 2)).length < (x :: y :: rs).length := by
        simp only [List.length_take, List.length_cons]; omega
      have hr : ((x :: y :: rs).drop ((x :: y :: rs).length / 2)).length < (x :: y :: rs).length := by
        simp only [List.length_drop, List.length_cons]; omega
      rw [ih _ hl ns, ih _ hr, smartAdd_map]

omit [DecidableEq α] [DecidableEq β] in
theorem mapBuild_map {X Y : Type*} (f : List (Node α) → X → List (Node α) × Y)
    (g : List (Node β) → X → List (Node β) × Y)
    (h : ∀ ns x, g (ns.map (node e)) x = ((f ns x).1.map (node e), (f ns x).2))
    (ns : List (Node α)) (xs : List X) :
    mapBuild g (ns.map (node e)) xs = ((mapBuild f ns xs).1.map (node e), (mapBuild f ns xs).2) := by
  induction xs generalizing ns with
  | nil => rfl
  | cons x xs ih => simp only [mapBuild, h, ih]

theorem prefixBuild_map (ns : List (Node α)) (acc : Ref) (refs : List Ref) :
    prefixBuild (ns.map (node e)) acc refs =
      ((prefixBuild ns acc refs).1.map (node e), (prefixBuild ns acc refs).2) := by
  induction refs generalizing ns acc with
  | nil => rfl
  | cons x xs ih => simp only [prefixBuild, smartAdd_map, ih]

theorem suffixBuild_map (ns : List (Node α)) (refs : List Ref) :
    suffixBuild (ns.map (node e)) refs =
      ((suffixBuild ns refs).1.map (node e), (suffixBuild ns refs).2) := by
  induction refs with
  | nil => rfl
  | cons x xs ih => simp only [suffixBuild, ih, smartAdd_map]

theorem addPairs_map (ns : List (Node α)) (ps : List (Ref × Ref)) :
    mapBuild (fun ns p => smartAdd ns p.1 p.2) (ns.map (node e)) ps =
      ((mapBuild (fun ns p => smartAdd ns p.1 p.2) ns ps).1.map (node e),
        (mapBuild (fun ns p => smartAdd ns p.1 p.2) ns ps).2) :=
  mapBuild_map e _ _ (fun ns p => smartAdd_map e ns p.1 p.2) ns ps

def vector (v : VectorResult α) : VectorResult β := ⟨v.nodes.map (node e), v.total, v.one⟩

theorem vectorFalse_map (ns : List (Node α)) (refs : List Ref) :
    vectorFalse (ns.map (node e)) refs = vector e (vectorFalse ns refs) := by
  simp only [vectorFalse, prefixBuild_map, suffixBuild_map, addPairs_map, vector]

def block (b : BlockResult α) : BlockResult β := ⟨b.nodes.map (node e), b.total, b.one, b.two⟩

theorem vectorTail_map (ns : List (Node α)) (refs : List Ref) :
    vectorTail (ns.map (node e)) refs = vector e (vectorTail ns refs) := by
  cases refs with
  | nil => rfl
  | cons carry values =>
    simp only [vectorTail, prefixBuild_map, suffixBuild_map, addPairs_map, vector]

theorem baseBlock_map (ns : List (Node α)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) :
    baseBlock (ns.map (node e)) points edges weights = block e (baseBlock ns points edges weights) := by
  have hone := mapBuild_map e
    (fun (ns : List (Node α)) a => ((DisjointBalanced.total ns (query edges weights [a])).1,
      (a, (DisjointBalanced.total ns (query edges weights [a])).2)))
    (fun (ns : List (Node β)) a => ((DisjointBalanced.total ns (query edges weights [a])).1,
      (a, (DisjointBalanced.total ns (query edges weights [a])).2)))
    (fun ns a => by simp only [total_map])
  have htwo := mapBuild_map e
    (fun (ns : List (Node α)) (p : ℕ × ℕ) =>
      ((DisjointBalanced.total ns (query edges weights [p.1, p.2])).1,
        (p, (DisjointBalanced.total ns (query edges weights [p.1, p.2])).2)))
    (fun (ns : List (Node β)) (p : ℕ × ℕ) =>
      ((DisjointBalanced.total ns (query edges weights [p.1, p.2])).1,
        (p, (DisjointBalanced.total ns (query edges weights [p.1, p.2])).2)))
    (fun ns p => by simp only [total_map])
  cases hl : points.getLast? with
  | none => simp only [baseBlock, hl, total_map, block, hone, htwo]
  | some a => simp only [baseBlock, hl, total_map, smartAdd_map, block, hone, htwo]

theorem coarseEdges_map (ns : List (Node α)) (groups : List (List ℕ)) (edges : EdgeTable) :
    coarseEdges (ns.map (node e)) groups edges =
      ((coarseEdges ns groups edges).1.map (node e), (coarseEdges ns groups edges).2) :=
  mapBuild_map e _ _ (fun ns p => by simp only [total_map]) ns _

theorem coarseWeights_map (ns : List (Node α)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) :
    coarseWeights (ns.map (node e)) groups edges weights =
      ((coarseWeights ns groups edges weights).1.map (node e),
        (coarseWeights ns groups edges weights).2) :=
  mapBuild_map e _ _ (fun ns i => by simp only [total_map]) ns _

theorem buildStrip_map (ns : List (Node α)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) :
    buildStrip (ns.map (node e)) groups edges weights ia =
      ((buildStrip ns groups edges weights ia).1.map (node e),
        (buildStrip ns groups edges weights ia).2) := by
  have hvals := mapBuild_map e
    (fun (ns : List (Node α)) j => DisjointBalanced.total ns
      (crossRefs edges ((groupAt groups ia.1).filter (· != ia.2)) (groupAt groups j)))
    (fun (ns : List (Node β)) j => DisjointBalanced.total ns
      (crossRefs edges ((groupAt groups ia.1).filter (· != ia.2)) (groupAt groups j)))
    (fun ns j => total_map e ns _)
  simp only [buildStrip, total_map, hvals, vectorTail_map]
  rfl

theorem buildStrips_map (ns : List (Node α)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) :
    buildStrips (ns.map (node e)) groups edges weights =
      ((buildStrips ns groups edges weights).1.map (node e),
        (buildStrips ns groups edges weights).2) :=
  mapBuild_map e _ _ (fun ns ia => buildStrip_map e ns groups edges weights ia) ns _

theorem buildSingles_map (ns : List (Node α)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) :
    buildSingles (ns.map (node e)) groups outside strips =
      ((buildSingles ns groups outside strips).1.map (node e),
        (buildSingles ns groups outside strips).2) :=
  mapBuild_map e _ _ (fun ns ia => by simp only [smartAdd_map]) ns _

theorem buildCrossLeft_map (ns : List (Node α)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a : ℕ) :
    buildCrossLeft (ns.map (node e)) groups edges far strips ij a =
      ((buildCrossLeft ns groups edges far strips ij a).1.map (node e),
        (buildCrossLeft ns groups edges far strips ij a).2) := by
  simp only [buildCrossLeft, smartAdd_map]
  exact mapBuild_map e _ _ (fun ns b => by simp only [total_map, smartAdd_map]) _ _

theorem buildCrossGroup_map (ns : List (Node α)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) :
    buildCrossGroup (ns.map (node e)) groups edges far strips ij =
      ((buildCrossGroup ns groups edges far strips ij).1.map (node e),
        (buildCrossGroup ns groups edges far strips ij).2) := by
  simp only [buildCrossGroup]
  rw [mapBuild_map e _ _ (fun ns a => buildCrossLeft_map e ns groups edges far strips ij a)]

theorem buildCrossPairs_map (ns : List (Node α)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) :
    buildCrossPairs (ns.map (node e)) groups edges far strips =
      ((buildCrossPairs ns groups edges far strips).1.map (node e),
        (buildCrossPairs ns groups edges far strips).2) := by
  simp only [buildCrossPairs]
  rw [mapBuild_map e _ _ (fun ns ij => buildCrossGroup_map e ns groups edges far strips ij)]

theorem reconstruct_map (groups : List (List ℕ)) (edges : EdgeTable) (weights : WeightTable)
    (coarse : BlockResult α) :
    reconstruct groups edges weights (block e coarse) =
      block e (reconstruct groups edges weights coarse) := by
  simp only [reconstruct, block, buildStrips_map, buildSingles_map, buildCrossPairs_map]

/-- The complete recursion commutes with relabeling its input atoms. -/
theorem block_map (ns : List (Node α)) (points : List ℕ) (edges : EdgeTable)
    (weights : WeightTable) :
    PairedCircuit.block (ns.map (node e)) points edges weights =
      block e (PairedCircuit.block ns points edges weights) := by
  induction points using (measure (fun ps : List ℕ => ps.length)).wf.induction
      generalizing ns edges weights with
  | h points ih =>
    by_cases hsmall : points.length ≤ 4
    · rw [block_small _ _ _ _ hsmall, block_small _ _ _ _ hsmall, baseBlock_map]
    · have hlarge : 4 < points.length := by omega
      have hlen : (List.range (PairGrouping.groups points).length).length < points.length := by
        simpa using PairGrouping.length_groups_lt points hlarge
      rw [block_large _ _ _ _ hlarge, block_large _ _ _ _ hlarge]
      dsimp only
      rw [coarseEdges_map, coarseWeights_map, ih _ hlen, reconstruct_map]

/-! Counting and marking ignore input labels. -/

omit [DecidableEq α] [DecidableEq β] in
theorem additionCount_map (ns : List (Node α)) :
    DAGAllocator.additionCount (ns.map (node e)) = DAGAllocator.additionCount ns := by
  simp only [DAGAllocator.additionCount, List.countP_map]
  congr 1
  funext n
  cases hk : n.kind <;> simp [node, kind, hk]

omit [DecidableEq α] [DecidableEq β] in
theorem parents_node (n : Node α) : DisjointPruning.parents (node e n) = DisjointPruning.parents n := by
  cases hk : n.kind <;> simp [DisjointPruning.parents, node, kind, hk]

omit [DecidableEq α] [DecidableEq β] in
theorem markFrom_map (offset : ℕ) (ns : List (Node α)) (roots : Finset ℕ) :
    DisjointPruning.markFrom offset (ns.map (node e)) roots =
      DisjointPruning.markFrom offset ns roots := by
  induction ns generalizing offset with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons, DisjointPruning.markFrom, ih, parents_node]

omit [DecidableEq α] [DecidableEq β] in
theorem mark_map (ns : List (Node α)) (roots : Finset ℕ) :
    DisjointPruning.mark (ns.map (node e)) roots = DisjointPruning.mark ns roots :=
  markFrom_map e 0 ns roots

omit [DecidableEq α] [DecidableEq β] in
theorem additionCountFrom_map (offset : ℕ) (active : Finset ℕ) (ns : List (Node α)) :
    DisjointPruning.additionCountFrom offset active (ns.map (node e)) =
      DisjointPruning.additionCountFrom offset active ns := by
  induction ns generalizing offset with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons, DisjointPruning.additionCountFrom, ih]
    cases hk : n.kind <;> simp [node, kind, hk]

end IntegerMultBounds.Networks.PairedRename
