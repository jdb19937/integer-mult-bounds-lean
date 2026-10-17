module

public import IntegerMultBounds.Networks.DAGReplay
import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DAGAllocatorBudget
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! Compaction of a DAG to a parent-closed active set. Active nodes are
re-interned in topological order with renumbered references; inactive nodes
allocate nothing. The result is a genuine DAG with unique supports, so a
pruned circuit can be consumed by any construction expecting a node list. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DAGCompact

open DisjointCircuit DisjointBuilder DisjointPruning DAGReplay

variable {ι : Type*} [DecidableEq ι]

/-- Scan in topological order. The reference list has one entry per source
node; inactive entries hold a placeholder that is never dereferenced. -/
def compactFrom (active : Finset ℕ) (target : List (Node ι)) (refs : List ℕ) :
    List (Node ι) → List (Node ι) × List ℕ
  | [] => (target, refs)
  | node :: nodes =>
    if refs.length ∈ active then
      let next := intern target (translated (Function.Embedding.refl ι) refs node)
      compactFrom active next.1 (refs ++ [next.2]) nodes
    else compactFrom active target (refs ++ [0]) nodes

def compact (active : Finset ℕ) (nodes : List (Node ι)) : List (Node ι) × List ℕ :=
  compactFrom active [] [] nodes

/-- Active source supports agree with the target references. -/
def AlignedOn (active : Finset ℕ) (prior : List (Finset ι))
    (target : List (Node ι)) (refs : List ℕ) : Prop :=
  refs.length = prior.length ∧ ∀ j (hj : j < prior.length), j ∈ active →
    (target.map Node.support)[refs[j]?.getD 0]? = some prior[j]

omit [DecidableEq ι] in
theorem alignedOn_extends {active : Finset ℕ} {prior : List (Finset ι)}
    {target larger : List (Node ι)} {refs : List ℕ} (he : Extends target larger)
    (ha : AlignedOn active prior target refs) : AlignedOn active prior larger refs :=
  ⟨ha.1, fun j hj hm => lookup_extends he (ha.2 j hj hm)⟩

omit [DecidableEq ι] in
@[simp] theorem translated_support (refs : List ℕ) (node : Node ι) :
    (translated (Function.Embedding.refl ι) refs node).support = node.support := by
  simp [translated]

/-- A translated active instruction is valid once its parents are active. -/
theorem translated_valid_on (active : Finset ℕ) (prior : List (Finset ι))
    (target : List (Node ι)) (refs : List ℕ) (node : Node ι)
    (ha : AlignedOn active prior target refs) (hn : node.Valid prior)
    (hp : parents node ⊆ active) :
    (translated (Function.Embedding.refl ι) refs node).Valid (target.map Node.support) := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      change support = {label} at hn
      simp [translated, Node.Valid, hn]
    | add left right =>
      simp only [Node.Valid] at hn
      split at hn
      next hl =>
        split at hn
        next hr =>
          have hleft := ha.2 left hl (hp (by simp [parents]))
          have hright := ha.2 right hr (hp (by simp [parents]))
          have hbl := lookup_bound hleft
          have hbr := lookup_bound hright
          have hsl : (target.map Node.support)[refs[left]?.getD 0]'(by simpa using hbl) =
              prior[left] := (List.getElem?_eq_some_iff.mp hleft).2
          have hsr : (target.map Node.support)[refs[right]?.getD 0]'(by simpa using hbr) =
              prior[right] := (List.getElem?_eq_some_iff.mp hright).2
          simp only [translated, Node.Valid, List.length_map, hbl, hbr, ↓reduceDIte]
          rw [hsl, hsr, hn.2, Finset.map_refl]
          exact ⟨hn.1, rfl⟩
        next hr => contradiction
      next hl => contradiction

/-- Publishing the interned reference of an active node extends the alignment. -/
theorem alignedOn_step (active : Finset ℕ) (prior : List (Finset ι))
    (target : List (Node ι)) (refs : List ℕ) (node : Node ι)
    (ha : AlignedOn active prior target refs) :
    AlignedOn active (prior ++ [node.support])
      (intern target (translated (Function.Embedding.refl ι) refs node)).1
      (refs ++ [(intern target (translated (Function.Embedding.refl ι) refs node)).2]) := by
  have hlen := ha.1
  have hold := alignedOn_extends (intern_extends target
    (translated (Function.Embedding.refl ι) refs node)) ha
  refine ⟨by simp [ha.1], ?_⟩
  intro j hj hm
  by_cases hlt : j < prior.length
  · rw [List.getElem?_append_left (by omega), List.getElem_append_left hlt]
    exact hold.2 j hlt hm
  · have he : j = prior.length := by
      simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    rw [List.getElem?_append_right (by omega), List.getElem_append_right (le_refl _)]
    simpa only [← ha.1, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.getElem_cons_zero, translated_support] using
      intern_support target (translated (Function.Embedding.refl ι) refs node)

omit [DecidableEq ι] in
/-- An inactive node only extends the reference list. -/
theorem alignedOn_skip (active : Finset ℕ) (prior : List (Finset ι))
    (target : List (Node ι)) (refs : List ℕ) (support : Finset ι)
    (ha : AlignedOn active prior target refs) (hn : prior.length ∉ active) :
    AlignedOn active (prior ++ [support]) target (refs ++ [0]) := by
  have hlen := ha.1
  refine ⟨by simp [ha.1], ?_⟩
  intro j hj hm
  by_cases hlt : j < prior.length
  · rw [List.getElem?_append_left (by omega), List.getElem_append_left hlt]
    exact ha.2 j hlt hm
  · have he : j = prior.length := by
      simp only [List.length_append, List.length_singleton] at hj; omega
    exact False.elim (hn (he ▸ hm))

/-- Compaction preserves validity and every active support. -/
theorem compactFrom_correct (active : Finset ℕ) (prior : List (Finset ι))
    (target : List (Node ι)) (refs : List ℕ) (source : List (Node ι))
    (ht : Valid target) (hs : ValidFrom prior source)
    (hc : ClosedFrom prior.length active source) (ha : AlignedOn active prior target refs) :
    Valid (compactFrom active target refs source).1 ∧
      Extends target (compactFrom active target refs source).1 ∧
      AlignedOn active (prior ++ source.map Node.support)
        (compactFrom active target refs source).1 (compactFrom active target refs source).2 := by
  induction source generalizing prior target refs with
  | nil => exact ⟨ht, extends_refl _, by simpa [compactFrom] using ha⟩
  | cons node source ih =>
    obtain ⟨hcn, hct⟩ := hc
    have hlen : refs.length = prior.length := ha.1
    by_cases hm : prior.length ∈ active
    · have hnode := translated_valid_on active prior target refs node ha hs.1 (hcn hm)
      have hstep := alignedOn_step active prior target refs node ha
      have hh := ih (prior ++ [node.support]) _ _ (intern_valid target _ ht hnode) hs.2
        (by simpa using hct) hstep
      have he : compactFrom active target refs (node :: source) =
          compactFrom active (intern target (translated (Function.Embedding.refl ι) refs node)).1
            (refs ++ [(intern target (translated (Function.Embedding.refl ι) refs node)).2])
            source := by
        simp only [compactFrom, hlen, hm, ↓reduceIte]
      rw [he]
      refine ⟨hh.1, extends_trans (intern_extends target _) hh.2.1, ?_⟩
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using hh.2.2
    · have hstep := alignedOn_skip active prior target refs node.support ha hm
      have hh := ih (prior ++ [node.support]) target (refs ++ [0]) ht hs.2
        (by simpa using hct) hstep
      have he : compactFrom active target refs (node :: source) =
          compactFrom active target (refs ++ [0]) source := by
        simp only [compactFrom, hlen, hm, ↓reduceIte]
      rw [he]
      refine ⟨hh.1, hh.2.1, ?_⟩
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using hh.2.2

/-- Every compaction step interns, so supports remain pairwise distinct. -/
theorem compactFrom_nodup (active : Finset ℕ) (target : List (Node ι))
    (refs : List ℕ) (source : List (Node ι)) (hn : (target.map Node.support).Nodup) :
    ((compactFrom active target refs source).1.map Node.support).Nodup := by
  induction source generalizing target refs with
  | nil => exact hn
  | cons node source ih =>
    simp only [compactFrom]
    split_ifs
    · exact ih _ _ (DisjointUnique.intern_nodup target _ hn)
    · exact ih _ _ hn

/-- Interning appends at most one node, and an input stays an input. -/
theorem intern_additionCount_le (target : List (Node ι)) (node : Node ι) :
    DAGAllocator.additionCount (intern target node).1 ≤ DAGAllocator.additionCount target +
      (match node.kind with | .input _ => 0 | .add _ _ => 1) := by
  unfold intern
  split
  · exact Nat.le_add_right _ _
  · simp only [DAGAllocator.additionCount, List.countP_append, List.countP_singleton]
    cases node.kind <;> simp

omit [DecidableEq ι] in
theorem translated_kind_add (refs : List ℕ) (node : Node ι) :
    (match (translated (Function.Embedding.refl ι) refs node).kind with
      | .input _ => 0 | .add _ _ => 1) =
    (match node.kind with | .input _ => 0 | .add _ _ => 1) := by
  cases hk : node.kind <;> simp [translated, hk]

/-- Only active additions can be allocated by compaction. -/
theorem compactFrom_additions_le (active : Finset ℕ) (target : List (Node ι))
    (refs : List ℕ) (source : List (Node ι)) :
    DAGAllocator.additionCount (compactFrom active target refs source).1 ≤
      DAGAllocator.additionCount target + additionCountFrom refs.length active source := by
  induction source generalizing target refs with
  | nil => simp [compactFrom, additionCountFrom]
  | cons node source ih =>
    by_cases hm : refs.length ∈ active
    · have hi := intern_additionCount_le target (translated (Function.Embedding.refl ι) refs node)
      have hr := ih (intern target (translated (Function.Embedding.refl ι) refs node)).1
        (refs ++ [(intern target (translated (Function.Embedding.refl ι) refs node)).2])
      rw [translated_kind_add] at hi
      simp only [List.length_append, List.length_singleton] at hr
      simp only [compactFrom, hm, ↓reduceIte, additionCountFrom]
      cases hk : node.kind <;> simp only [hk] at hi ⊢ <;> omega
    · have hr := ih target (refs ++ [0])
      simp only [List.length_append, List.length_singleton] at hr
      simp only [compactFrom, hm, ↓reduceIte, additionCountFrom]
      omega

/-- The compacted DAG of a parent-closed active set. -/
theorem compact_correct (active : Finset ℕ) (nodes : List (Node ι)) (hv : Valid nodes)
    (hc : ClosedFrom 0 active nodes) :
    Valid (compact active nodes).1 ∧ ((compact active nodes).1.map Node.support).Nodup ∧
      ∀ j (hj : j < nodes.length), j ∈ active →
        ((compact active nodes).1.map Node.support)[(compact active nodes).2[j]?.getD 0]? =
          some nodes[j].support := by
  have hh := compactFrom_correct active [] [] [] nodes trivial hv hc ⟨rfl, by simp⟩
  refine ⟨hh.1, compactFrom_nodup active [] [] nodes (by simp), ?_⟩
  intro j hj hm
  have h := hh.2.2.2 j (by simpa using hj) hm
  simpa only [compact, List.nil_append, List.getElem_map] using h

theorem compact_additions_le (active : Finset ℕ) (nodes : List (Node ι)) :
    DAGAllocator.additionCount (compact active nodes).1 ≤ additionCountFrom 0 active nodes := by
  have h := compactFrom_additions_le active [] [] nodes
  simpa [compact, DAGAllocator.additionCount] using h

/-- Backward marking is a parent-closed active set for any valid DAG. -/
theorem mark_closed (nodes : List (Node ι)) (roots : Finset ℕ) (hv : Valid nodes) :
    ClosedFrom 0 (mark nodes roots) nodes :=
  markFrom_closed [] nodes roots hv

end IntegerMultBounds.Networks.DAGCompact
