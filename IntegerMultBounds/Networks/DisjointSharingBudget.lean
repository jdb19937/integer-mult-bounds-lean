module

import IntegerMultBounds.Networks.PairedCircuitBudget
import IntegerMultBounds.Networks.DisjointUnique
public import IntegerMultBounds.Networks.DAGAllocatorBudget
public import IntegerMultBounds.Networks.PairedCircuit
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Algebra.Group.Action.Defs

/-! Exact allocation accounting for persistent support interning. The cost is
zero for absent operands and for an already stored union. Stateful loops charge
against the current bank, so sharing with earlier iterations is preserved. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DisjointSharingBudget

open DisjointCircuit DisjointBuilder DisjointUnique PairedCircuit DAGAllocator

variable {ι X Y : Type*} [DecidableEq ι]

/-- Charge one only when smart addition really allocates a new support. -/
def smartAddCost (nodes : List (Node ι)) : Ref → Ref → ℕ
  | none, _ => 0
  | _, none => 0
  | some l, some r =>
    if refSupport nodes (some l) ∪ refSupport nodes (some r) ∈ nodes.map Node.support
    then 0 else 1

/-- Exact accounting includes both zero elision and support reuse. -/
theorem smartAdd_additions (nodes : List (Node ι)) (l r : Ref) :
    additionCount (smartAdd nodes l r).1 = additionCount nodes + smartAddCost nodes l r := by
  cases l with
  | none => simp [smartAdd, smartAddCost]
  | some l =>
    cases r with
    | none => simp [smartAdd, smartAddCost]
    | some r =>
      simp only [smartAdd, smartAddCost]
      unfold intern
      split
      · rename_i i hi
        have hm : refSupport nodes (some l) ∪ refSupport nodes (some r) ∈ nodes.map Node.support := by
          by_contra hn
          have hf := (findSupport_none_iff _ _).mpr hn
          simp [hf] at hi
        simp [hm]
      · rename_i hn
        have hm := (findSupport_none_iff _ _).mp hn
        simp [hm, additionCount, List.countP_append]

/-- A symbolic proof that a union was already stored discharges its cost. -/
theorem smartAdd_reuses (nodes : List (Node ι)) (l r : ℕ)
    (h : refSupport nodes (some l) ∪ refSupport nodes (some r) ∈ nodes.map Node.support) :
    additionCount (smartAdd nodes (some l) (some r)).1 = additionCount nodes := by
  rw [smartAdd_additions]
  simp [smartAddCost, h]

/-- Stateful cost fold, using precisely the banks seen by the actual loop. -/
def loopCost (f : List (Node ι) → X → List (Node ι) × Y)
    (cost : List (Node ι) → X → ℕ) (nodes : List (Node ι)) : List X → ℕ
  | [] => 0
  | x :: xs => cost nodes x + loopCost f cost (f nodes x).1 xs

/-- Number of actual operands; absent references do not consume additions. -/
def presentCount (refs : List Ref) : ℕ := refs.countP Option.isSome

private theorem smartAdd_presence (nodes : List (Node ι)) (l r : Ref) :
    ((smartAdd nodes l r).2.isSome.toNat) = max l.isSome.toNat r.isSome.toNat := by
  cases l <;> cases r <;> simp [smartAdd]

private theorem smartAdd_potential (nodes : List (Node ι)) (l r : Ref) :
    additionCount (smartAdd nodes l r).1 + (smartAdd nodes l r).2.isSome.toNat ≤
      additionCount nodes + l.isSome.toNat + r.isSome.toNat := by
  have h := PairedCircuitBudget.smartAdd_additions_le nodes l r
  cases l <;> cases r <;> simp_all [smartAdd]

/-- Prefix accounting carries one unit of potential in its final accumulator.
This charges exactly the number of present operands minus one, including zeros
at arbitrary positions, without examining their supports. -/
theorem prefixBuild_present_le (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    additionCount (prefixBuild nodes acc refs).1 +
        ((prefixBuild nodes acc refs).2.getLast?.getD none).isSome.toNat ≤
      additionCount nodes + acc.isSome.toNat + presentCount refs := by
  induction refs generalizing nodes acc with
  | nil => simp [prefixBuild, presentCount]
  | cons r rs ih =>
    have hs := smartAdd_potential nodes acc r
    have ht := ih (smartAdd nodes acc r).1 (smartAdd nodes acc r).2
    have hn : (prefixBuild (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs).2 ≠ [] := by
      have := prefixBuild_length (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs
      intro he
      simp [he] at this
    simp only [prefixBuild, List.getLast?_cons_of_ne_nil hn]
    simp only [presentCount, List.countP_cons] at ht ⊢
    unfold presentCount at *
    cases r <;> simp only [Option.isSome, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
      ite_false, ite_true] at hs ht ⊢ <;> omega

/-- Suffix accounting obeys the same potential law despite running backwards. -/
theorem suffixBuild_present_le (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (suffixBuild nodes refs).1 +
        ((suffixBuild nodes refs).2.headD none).isSome.toNat ≤
      additionCount nodes + presentCount refs := by
  induction refs with
  | nil => simp [suffixBuild, presentCount]
  | cons r rs ih =>
    have hs := smartAdd_potential (suffixBuild nodes rs).1 r
      ((suffixBuild nodes rs).2.headD none)
    simp only [suffixBuild, List.headD_cons]
    simp only [presentCount, List.countP_cons]
    cases r <;> simp_all [presentCount]
    all_goals omega

theorem prefixBuild_presence (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    ((prefixBuild nodes acc refs).2.getLast?.getD none).isSome.toNat =
      min 1 (acc.isSome.toNat + presentCount refs) := by
  induction refs generalizing nodes acc with
  | nil => cases acc <;> simp [prefixBuild, presentCount]
  | cons r rs ih =>
    have hn : (prefixBuild (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs).2 ≠ [] := by
      have := prefixBuild_length (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs
      intro he
      simp [he] at this
    simp only [prefixBuild, List.getLast?_cons_of_ne_nil hn, ih, smartAdd_presence,
      presentCount, List.countP_cons]
    cases acc <;> cases r <;> simp

theorem suffixBuild_presence (nodes : List (Node ι)) (refs : List Ref) :
    ((suffixBuild nodes refs).2.headD none).isSome.toNat = min 1 (presentCount refs) := by
  induction refs with
  | nil => simp [suffixBuild, presentCount]
  | cons r rs ih =>
    simp only [suffixBuild, List.headD_cons, smartAdd_presence, ih,
      presentCount, List.countP_cons]
    cases r <;> simp

/-- A prefix pass starting from zero allocates at most k minus one additions
for k present operands, regardless of the number and positions of zeros. -/
theorem prefixBuild_additions_le_present (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (prefixBuild nodes none refs).1 ≤
      additionCount nodes + (presentCount refs - 1) := by
  have h := prefixBuild_present_le nodes none refs
  rw [prefixBuild_presence] at h
  simp only [Option.isSome_none, Bool.toNat_false, Nat.zero_add, Nat.add_zero] at h
  omega

/-- The backwards pass has the same k minus one bound. Support interning can
only reduce it further, including reuse of the prefix pass's full total. -/
theorem suffixBuild_additions_le_present (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (suffixBuild nodes refs).1 ≤
      additionCount nodes + (presentCount refs - 1) := by
  have h := suffixBuild_present_le nodes refs
  rw [suffixBuild_presence] at h
  omega

/-- The actual interning costs of each pass remain available separately for
symbolic reuse proofs and for composing recursive construction stages. -/
def prefixCost (nodes : List (Node ι)) (acc : Ref) : List Ref → ℕ
  | [] => 0
  | r :: rs => smartAddCost nodes acc r +
      prefixCost (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs

end IntegerMultBounds.Networks.DisjointSharingBudget
