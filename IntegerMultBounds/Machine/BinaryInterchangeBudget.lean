module

-- S6 supplier seam
public import IntegerMultBounds.Machine.BinaryInterchangeRun
public import IntegerMultBounds.Machine.BinaryRadixEqualShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeBudget

/-!
# The time bound of the rectangular interchange

The supplier's uniform time bound at the exponent `Parameters.tau` of the cost chain.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryInterchangeRun

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B h d : ℕ) (hs : Fin 5 → List Bool),
    0 < P → 0 < G → 0 < B → h ≤ d+1 → d ≤ h+1 →
    (∀ i, Counter.value (hs i) = values P G B h d i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost P G B h d hs : ℝ) ≤
      C*(BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℝ)*
        ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau := by
  rw [← BinaryRadixEqualShared.supplier_tau]
  exact IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeRun.uniform_bound

end IntegerMultBounds.Machine.BinaryInterchangeRun
