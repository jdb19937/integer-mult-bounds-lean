module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! Algebraic components of the scalar motif and common-frame argument.
Residual spaces, sparse wire counts, and network-to-tape compilation are not
established by this file. -/

@[expose] public section

namespace IntegerMultBounds.Networks

section Restoration
variable {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]

end Restoration

section TripleCoefficients
variable {α : Type*} [DecidableEq α]

theorem triple_inter_card (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (S ∩ T).card ≤ 3 ∧ ((S ∩ T).card = 3 ↔ S = T) := by
  constructor
  · simpa [hS] using Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := T))
  · constructor
    · intro h
      have hs : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have ht : S ∩ T = T := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact hs.symm.trans ht
    · rintro rfl
      simpa using hS

/-- Complex center coefficient plus the prescribed sparse side correction. -/
def complexCoefficient (S T : Finset α) : ℚ :=
  let j := (S ∩ T).card
  let center := ((j : ℚ) - 1) / 2
  center + if S ≠ T ∧ Even j then -center else 0

theorem complexCoefficient_eq (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    complexCoefficient S T = if S = T then 1 else 0 := by
  obtain ⟨hle, heq⟩ := triple_inter_card S T hS hT
  by_cases h : S = T
  · subst T
    norm_num [complexCoefficient, hS]
  · have hne : (S ∩ T).card ≠ 3 := fun hh => h (heq.mp hh)
    have hlt : (S ∩ T).card < 3 := by omega
    have hj : (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 := by omega
    rcases hj with hj | hj | hj <;> norm_num [complexCoefficient, h, hj]

def bitCoefficient (S T : Finset α) : ℕ :=
  let j := (S ∩ T).card
  (j + if j = 1 then 1 else 0) % 2

theorem bitCoefficient_eq (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    bitCoefficient S T = if S = T then 1 else 0 := by
  obtain ⟨hle, heq⟩ := triple_inter_card S T hS hT
  by_cases h : S = T
  · subst T
    norm_num [bitCoefficient, hS]
  · have hne : (S ∩ T).card ≠ 3 := fun hh => h (heq.mp hh)
    have hj : (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 := by omega
    rcases hj with hj | hj | hj <;> norm_num [bitCoefficient, h, hj]

end TripleCoefficients

section Frames
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

theorem frame_change (D E' : E ≃ₗ[R] E) (x : E) : E' (D.symm (D x)) = E' x := by simp

end Frames

end IntegerMultBounds.Networks
