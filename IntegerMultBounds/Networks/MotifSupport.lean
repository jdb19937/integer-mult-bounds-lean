module

public import IntegerMultBounds.Networks.GroupedRouting
public import Mathlib.Tactic.Linarith

/-! Exact sparse incidences of the local motif groups. In particular, no side
wire disappears under its nonzero cancelling coefficient, and each side wire
belongs to precisely its owning copy and injection groups. -/

@[expose] public section

namespace IntegerMultBounds.Networks.MotifSupport

open Circuit GroupedCircuit

theorem complex_pair_coefficient_ne_zero {h n : ℕ} {L : Fin n → Finset (Fin h)}
    (p : ComplexPair L) : centralCoeff L p.val.1 p.val.2 ≠ 0 := by
  intro hz
  have hn : ((L p.val.1 ∩ L p.val.2).card : ℚ) = 1 := by
    unfold centralCoeff at hz
    linarith
  have hn' : (L p.val.1 ∩ L p.val.2).card = 1 := by exact_mod_cast hn
  obtain ⟨k, hk⟩ := p.property.2
  omega

theorem complexInject_ne_zero {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ ComplexPair L) (s : Fin n) (p : Fin a) :
    complexInject e s p ≠ 0 ↔ (e p).val.1 = s := by
  by_cases hs : (e p).val.1 = s
  · subst s
    simp [complexInject, complex_pair_coefficient_ne_zero (e p)]
  · simp [complexInject, hs]

section Incidences
variable {R : Type*} [CommRing R] [DecidableEq R]
    {n a c s : ℕ}

theorem side_x (i : Fin a) (j : Fin n) :
    (side i : Role n a c s) ≠ x j := by simp [side, x]
/-- Each side wire is touched only in the copy group of its unique owner. -/
theorem copy_side (owner : Fin a → Fin n) (r : R) (hr : r ≠ 0) (j : Fin n) (p : Fin a) :
    (side p : Role n a c s) ∈ touched (copyGroup side x owner r side_x j) ↔ owner p = j := by
  rw [copyGroup_touched _ _ _ _ hr]
  simp [side, x]

end Incidences

end IntegerMultBounds.Networks.MotifSupport
