module

public import IntegerMultBounds.Networks.NeighborCounts
public import Mathlib.Tactic.Ring

/-! Explicit role sets for the full three-coordinate network layout. Each
invocation has its own side and central wires, including across stages. This
counts the named layout; compilation of the global gate schedule and attachment
of its nested labels are separate obligations. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Wires

open NeighborCounts

abbrev Address (h : ℕ) := Triple h × Triple h × Triple h

/-- A stage and the two fixed coordinates identify one invocation. -/
abbrev Invocation (h : ℕ) := Fin 3 × Triple h × Triple h

abbrev BitRole (h : ℕ) :=
  Address h ⊕ Address h ⊕ (Invocation h × (BitPairs h ⊕ Fin h))

abbrev ComplexRole (h : ℕ) :=
  Address h ⊕ Address h ⊕ (Invocation h × (ComplexPairs h ⊕ Fin (h + 1)))

theorem address_card (h : ℕ) : Fintype.card (Address h) = (h.choose 3) ^ 3 := by
  simp [Address, pow_succ]
  ring

theorem complex_role_card (h : ℕ) :
    Fintype.card (ComplexRole h) = 2 * (h.choose 3) ^ 3 +
      (3 * (h.choose 3) ^ 2) * (h.choose 3 * ((h - 3).choose 3 + 3 * (h - 3)) + (h + 1)) := by
  simp only [ComplexRole, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    triple_card, complex_pairs_card]
  ring

end IntegerMultBounds.Networks.Wires
