module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Split a coordinate matching around three disjoint reservoirs

An edge has only two endpoints, so it misses at least one of three disjoint
reservoirs. The computable first available choice is symmetric in its endpoints.
Restricting an involution by that choice gives three involutions, each fixing
its own reservoir, whose composition is the original matching.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [DecidableEq ι]

def reservoirChoice (banks : Fin 3 → Finset ι) (a b : ι) : Fin 3 :=
  if a ∉ banks 0 ∧ b ∉ banks 0 then 0 else
    if a ∉ banks 1 ∧ b ∉ banks 1 then 1 else 2

theorem reservoirChoice_symm (banks : Fin 3 → Finset ι) (a b : ι) :
    reservoirChoice banks a b = reservoirChoice banks b a := by
  simp only [reservoirChoice, and_comm]

theorem reservoirChoice_avoids (banks : Fin 3 → Finset ι)
    (separate : Pairwise (fun i j => Disjoint (banks i) (banks j))) (a b : ι) :
    a ∉ banks (reservoirChoice banks a b) ∧ b ∉ banks (reservoirChoice banks a b) := by
  have away (i j : Fin 3) (hne : i ≠ j) (x : ι) (hx : x ∈ banks i) : x ∉ banks j :=
    fun hj => Finset.disjoint_left.mp (separate hne) hx hj
  unfold reservoirChoice
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · by_cases ha : a ∈ banks 0
    · have ha1 := away 0 1 (by decide) a ha
      have hb1 : b ∈ banks 1 := by
        by_contra hb
        exact h1 ⟨ha1, hb⟩
      exact ⟨away 0 2 (by decide) a ha, away 1 2 (by decide) b hb1⟩
    · have hb0 : b ∈ banks 0 := by
        by_contra hb
        exact h0 ⟨ha, hb⟩
      have hb1 := away 0 1 (by decide) b hb0
      have ha1 : a ∈ banks 1 := by
        by_contra ha'
        exact h1 ⟨ha', hb1⟩
      exact ⟨away 1 2 (by decide) a ha1, away 0 2 (by decide) b hb0⟩

variable (banks : Fin 3 → Finset ι) (mate : ι → ι) (hinv : Function.Involutive mate)

def matchingClass (k : Fin 3) (x : ι) : ι :=
  if reservoirChoice banks x (mate x) = k then mate x else x

include hinv in
theorem reservoirChoice_mate (x : ι) :
    reservoirChoice banks (mate x) (mate (mate x)) = reservoirChoice banks x (mate x) := by
  rw [hinv, reservoirChoice_symm]

include hinv in
theorem matchingClass_involutive (k : Fin 3) : Function.Involutive (matchingClass banks mate k) := by
  intro x
  unfold matchingClass
  by_cases hx : reservoirChoice banks x (mate x) = k
  · rw [ite_eq_left hx, reservoirChoice_mate banks mate hinv, ite_eq_left hx, hinv]
  · rw [ite_eq_right hx, ite_eq_right hx]

def matchingClassPerm (k : Fin 3) : Equiv.Perm ι where
  toFun := matchingClass banks mate k
  invFun := matchingClass banks mate k
  left_inv := matchingClass_involutive banks mate hinv k
  right_inv := matchingClass_involutive banks mate hinv k

/-- The class assigned to a reservoir fixes every coordinate in that reservoir. -/
theorem matchingClass_fixes (separate : Pairwise (fun i j => Disjoint (banks i) (banks j)))
    (k : Fin 3) (x : ι) (hx : x ∈ banks k) : matchingClass banks mate k x = x := by
  have hne : reservoirChoice banks x (mate x) ≠ k := by
    intro he
    have h := (reservoirChoice_avoids banks separate x (mate x)).1
    rw [he] at h
    exact h hx
  exact ite_eq_right hne

include hinv in
/-- All three classes together perform exactly the original coordinate matching. -/
theorem matchingClass_comp (x : ι) :
    matchingClass banks mate 2 (matchingClass banks mate 1 (matchingClass banks mate 0 x)) = mate x := by
  have hc := reservoirChoice_symm banks (mate x) x
  have hm (j : ι) : mate (mate j) = j := hinv j
  generalize he : reservoirChoice banks x (mate x) = k
  fin_cases k <;> simp [matchingClass, he, hc, hm]

end IntegerMultBounds.MathlibTM2.Routing
