module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Card
public import Aesop
public import Lean.Elab.Tactic.Omega

/-! Literal consecutive-pair grouping for the paired exclusion recursion.
The last group is a singleton for odd input lengths. The list and finite-set
interfaces retain the input order and prove the partition properties used
by the coarse graph construction. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairGrouping

variable {V : Type*}

/-- The upstream slices `points[i:i+2]`, for `i = 0, 2, 4, ...`. -/
def groups : List V → List (List V)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest => [a, b] :: groups rest

@[simp] theorem flatten_groups (points : List V) : (groups points).flatten = points := by
  fun_induction groups points <;> simp_all

/-- The number of groups is the integer ceiling of half the input length. -/
theorem length_groups (points : List V) : (groups points).length = (points.length + 1) / 2 := by
  fun_induction groups points <;> simp_all
  omega

theorem group_length_le (points : List V) (g : List V) (hg : g ∈ groups points) : g.length ≤ 2 := by
  fun_induction groups points <;> simp_all
  aesop

/-- The coarse recursive call strictly decreases beyond the small-block branch. -/
theorem length_groups_lt (points : List V) (h : 4 < points.length) :
    (groups points).length < points.length := by
  rw [length_groups]
  omega

theorem mem_group (points : List V) (v : V) :
    (∃ g ∈ groups points, v ∈ g) ↔ v ∈ points := by
  rw [← List.mem_flatten, flatten_groups]

theorem group_subset (points : List V) (g : List V) (hg : g ∈ groups points) : g ⊆ points :=
  fun _ hv => (mem_group points _).mp ⟨g, hg, hv⟩

theorem groups_disjoint (points : List V) (hn : points.Nodup) :
    (groups points).Pairwise List.Disjoint :=
  (List.nodup_flatten.mp (by simpa using hn : (groups points).flatten.Nodup)).2

section Finsets
variable [DecidableEq V]

/-- Ordered coarse vertices, represented by their actual fine-vertex sets. -/
def finsets (points : List V) : List (Finset V) := (groups points).map List.toFinset

@[simp] theorem length_finsets (points : List V) :
    (finsets points).length = (points.length + 1) / 2 := by
  simp [finsets, length_groups]

end Finsets
end IntegerMultBounds.Networks.PairGrouping
