module

public import IntegerMultBounds.Networks.PairedVectorBudget
public import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DisjointExclusion

/-! Balanced coarse-edge totals already store their row sums. Reconstructing
those rows during strip construction reuses the support bank for free. This
explains interning savings structurally, without enumerating generated nodes. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedBalancedSharing

open DisjointCircuit DisjointBuilder DisjointUnique DisjointExclusion
open PairedVectorBudget DAGAllocator

variable {ι : Type*} [DecidableEq ι]

private theorem smartAdd_extends (nodes : List (Node ι)) (l r : Ref) :
    Extends nodes (smartAdd nodes l r).1 := by
  cases l <;> cases r
  all_goals first | exact extends_refl _ | skip
  simp only [smartAdd]
  unfold intern
  split
  · exact extends_refl _
  · exact ⟨[_], rfl⟩

/-- The exact four-entry balanced total builds two rows before their union. -/
theorem total_four (nodes : List (Node ι)) (a b c d : Ref) :
    DisjointBalanced.total nodes [a, b, c, d] =
      let left := smartAdd nodes a b
      let right := smartAdd left.1 c d
      smartAdd right.1 left.2 right.2 := by
  simp [DisjointBalanced.total]

/-- A four-edge coarse cell retains the exact support of each of its two rows.
Empty rows remain absent references and are not charged as stored nodes. -/
theorem total_four_rows (nodes : List (Node ι)) (a b c d : Ref)
    (hv : Valid nodes) (hr : RefsValid nodes [a, b, c, d])
    (hd : DisjointRefs nodes [a, b, c, d]) :
    let result := DisjointBalanced.total nodes [a, b, c, d]
    (∃ left, RefValid result.1 left ∧ refSupport result.1 left =
      refSupport nodes a ∪ refSupport nodes b) ∧
    (∃ right, RefValid result.1 right ∧ refSupport result.1 right =
      refSupport nodes c ∪ refSupport nodes d) := by
  have hab : Disjoint (refSupport nodes a) (refSupport nodes b) :=
    (List.pairwise_cons.mp hd).1 b (by simp)
  have hcd : Disjoint (refSupport nodes c) (refSupport nodes d) :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hd).2).2).1 d (by simp)
  let left := smartAdd nodes a b
  let right := smartAdd left.1 c d
  have hl := smartAdd_built nodes a b hv (hr a (by simp)) (hr b (by simp)) hab
  have hrl := refValid_extends hl.extension (hr c (by simp))
  have hrr := refValid_extends hl.extension (hr d (by simp))
  have hright := smartAdd_built left.1 c d hl.valid hrl hrr (by
    rw [refSupport_extends hl.extension (hr c (by simp)),
      refSupport_extends hl.extension (hr d (by simp))]
    exact hcd)
  have hlast := smartAdd_extends right.1 left.2 right.2
  have hleft := extends_trans hright.extension hlast
  rw [total_four]
  refine ⟨⟨left.2, refValid_extends hleft hl.refValid, ?_⟩,
    ⟨right.2, refValid_extends hlast hright.refValid, ?_⟩⟩
  · rw [refSupport_extends hleft hl.refValid]
    exact hl.support_eq
  · rw [refSupport_extends hlast hright.refValid, hright.support_eq,
      refSupport_extends hl.extension (hr c (by simp)),
      refSupport_extends hl.extension (hr d (by simp))]

/-- Any valid pair whose union is represented by a valid reference is free.
This covers both support interning and an absent, empty-support row. -/
theorem smartAdd_additions_of_ref (nodes : List (Node ι)) (l r stored : Ref)
    (hv : Valid nodes) (hl : RefValid nodes l) (_hr : RefValid nodes r)
    (hs : RefValid nodes stored)
    (he : refSupport nodes stored = refSupport nodes l ∪ refSupport nodes r) :
    additionCount (smartAdd nodes l r).1 = additionCount nodes := by
  cases stored with
  | none =>
    have hzero : refSupport nodes l = ∅ := by
      have hu : refSupport nodes l ∪ refSupport nodes r = ∅ := he.symm
      exact (Finset.union_eq_empty.mp hu).1
    have hlzero := ref_eq_none_of_support_empty nodes l hv hl hzero
    simp [hlzero, smartAdd]
  | some i =>
    apply smartAdd_additions_of_union_mem
    rw [← he]
    exact refSupport_mem nodes i hs

/-- Strip reconstruction can reuse either coarse row after any later stages
have extended the graph. The support witness survives those extensions. -/
theorem row_reuse_of_extends (prior larger : List (Node ι)) (a b c d l r : Ref)
    (hv : Valid prior) (hr : RefsValid prior [a, b, c, d])
    (hd : DisjointRefs prior [a, b, c, d])
    (he : Extends (DisjointBalanced.total prior [a, b, c, d]).1 larger)
    (hlarger : Valid larger) (hl : RefValid larger l) (hright : RefValid larger r)
    (hrow : refSupport larger l ∪ refSupport larger r = refSupport prior a ∪ refSupport prior b ∨
      refSupport larger l ∪ refSupport larger r = refSupport prior c ∪ refSupport prior d) :
    additionCount (smartAdd larger l r).1 = additionCount larger := by
  obtain ⟨hleft, hrightRow⟩ := total_four_rows prior a b c d hv hr hd
  rcases hrow with hrow | hrow
  · obtain ⟨stored, hs, hsupport⟩ := hleft
    apply smartAdd_additions_of_ref larger l r stored hlarger hl hright (refValid_extends he hs)
    rw [refSupport_extends he hs, hsupport, hrow]
  · obtain ⟨stored, hs, hsupport⟩ := hrightRow
    apply smartAdd_additions_of_ref larger l r stored hlarger hl hright (refValid_extends he hs)
    rw [refSupport_extends he hs, hsupport, hrow]

end IntegerMultBounds.Networks.PairedBalancedSharing
