module
public import IntegerMultBounds.Networks.DisjointSharingBudget
import IntegerMultBounds.Networks.PairedCircuitBudget
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum.Pow


/-! Presence-only allocation bounds. Whether a constructed reference is zero
depends only on which operands are zero, never on their supports, so these
bounds need no validity or disjointness hypotheses. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedPresence

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator DisjointSharingBudget

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem presentCount_append (xs ys : List Ref) :
    presentCount (xs ++ ys) = presentCount xs + presentCount ys := by
  simp [presentCount, List.countP_append]

private theorem smartAdd_presence' (nodes : List (Node ι)) (l r : Ref) :
    ((smartAdd nodes l r).2.isSome.toNat) = max l.isSome.toNat r.isSome.toNat := by
  cases l <;> cases r <;> simp [smartAdd]

private theorem smartAdd_potential' (nodes : List (Node ι)) (l r : Ref) :
    additionCount (smartAdd nodes l r).1 + (smartAdd nodes l r).2.isSome.toNat ≤
      additionCount nodes + l.isSome.toNat + r.isSome.toNat := by
  have h := PairedCircuitBudget.smartAdd_additions_le nodes l r
  cases l <;> cases r <;> simp_all [smartAdd]

/-- Balanced totals carry one unit of potential in their result: allocations
plus result presence never exceed the number of present operands. -/
theorem total_potential (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (DisjointBalanced.total nodes refs).1 +
        (DisjointBalanced.total nodes refs).2.isSome.toNat ≤ additionCount nodes + presentCount refs ∧
      (DisjointBalanced.total nodes refs).2.isSome.toNat = min 1 (presentCount refs) := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction generalizing nodes with
  | h refs ih =>
    cases refs with
    | nil => simp [DisjointBalanced.total, presentCount]
    | cons r tail =>
      cases tail with
      | nil => cases r <;> simp [DisjointBalanced.total, presentCount]
      | cons s rs =>
        let values := r :: s :: rs
        let left := values.take (values.length / 2)
        let right := values.drop (values.length / 2)
        have hlen : 2 ≤ values.length := by simp [values]
        have hl : left.length < values.length := by simp only [left, List.length_take]; omega
        have hr : right.length < values.length := by simp only [right, List.length_drop]; omega
        have hsplit : presentCount values = presentCount left + presentCount right := by
          rw [← presentCount_append, List.take_append_drop]
        have hleft := ih left hl nodes
        have hright := ih right hr (DisjointBalanced.total nodes left).1
        have hp := smartAdd_potential' (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).1
          (DisjointBalanced.total nodes left).2
          (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2
        have hq := smartAdd_presence' (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).1
          (DisjointBalanced.total nodes left).2
          (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2
        rw [DisjointBalanced.total]
        change additionCount (smartAdd (DisjointBalanced.total
            (DisjointBalanced.total nodes left).1 right).1 (DisjointBalanced.total nodes left).2
            (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2).1 +
            (smartAdd (DisjointBalanced.total
            (DisjointBalanced.total nodes left).1 right).1 (DisjointBalanced.total nodes left).2
            (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2).2.isSome.toNat ≤
          additionCount nodes + presentCount values ∧
          (smartAdd (DisjointBalanced.total
            (DisjointBalanced.total nodes left).1 right).1 (DisjointBalanced.total nodes left).2
            (DisjointBalanced.total (DisjointBalanced.total nodes left).1 right).2).2.isSome.toNat =
            min 1 (presentCount values)
        rw [hsplit]
        constructor <;> omega

theorem total_presence (nodes : List (Node ι)) (refs : List Ref) :
    (DisjointBalanced.total nodes refs).2.isSome.toNat = min 1 (presentCount refs) :=
  (total_potential nodes refs).2

/-- A balanced total allocates at most one fewer node than its present operands. -/
theorem total_additions_le_present (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (DisjointBalanced.total nodes refs).1 ≤
      additionCount nodes + (presentCount refs - 1) := by
  have h := total_potential nodes refs
  omega

theorem total_isSome (nodes : List (Node ι)) (refs : List Ref) (h : 0 < presentCount refs) :
    (DisjointBalanced.total nodes refs).2.isSome = true := by
  have hp := total_presence nodes refs
  cases hs : (DisjointBalanced.total nodes refs).2.isSome
  · rw [hs] at hp; simp at hp; omega
  · rfl

theorem total_none (nodes : List (Node ι)) (refs : List Ref) (h : presentCount refs = 0) :
    (DisjointBalanced.total nodes refs).2 = none := by
  have hp := total_presence nodes refs
  rw [h] at hp
  cases hs : (DisjointBalanced.total nodes refs).2
  · rfl
  · rw [hs] at hp; simp at hp

end IntegerMultBounds.Networks.PairedPresence
