module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedRoundMatch
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedDirectCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopCost

/-! Actual retuned round costs: compact bulk and explicit direct boundary rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node Filter Mult.SynthErr
noncomputable section

theorem compactRetuned_loops_le {Ka : ℕ} (ds : ComplexFramedExecution.Directions) (M : ℕ) (es : List ℕ)
    (ℓ K w l A stk : ℕ) :
    compactSynUniformLoopFCost (Ka:=Ka) ds M K es ℓ w l A stk ≤
        (∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk) + 6 * A ^ 2 + 16 * A + 4 ∧
      compactSynUniformLoopOCost (Ka:=Ka) ds M K es ℓ w l A stk ≤
        (∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk) + 6 * A ^ 2 + 16 * A + 4 := by
  have hS : ∀ f : ℕ → ℕ, (∀ j < A, f j ≤ 6 * A + 14) →
      ∑ j ∈ Finset.range A, f j ≤ 6 * A ^ 2 + 14 * A := by
    intro f hf
    calc ∑ j ∈ Finset.range A, f j ≤ ∑ j ∈ Finset.range A, (6 * A + 14) :=
          Finset.sum_le_sum fun j hj => hf j (Finset.mem_range.1 hj)
      _ = 6 * A ^ 2 + 14 * A := by simp; ring
  constructor
  · unfold compactSynUniformLoopFCost
    have e : ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + 1 +
        compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk + (2 * (A - 1 - j) + 2) + 3) =
        (∑ j ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk) +
          ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + 1 + (2 * (A - 1 - j) + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hr : ∑ j ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk =
        ∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk :=
      Finset.sum_range_reflect (fun h => compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk) A
    have := hS (fun j => (4 * (A - 1 - j) + 4) + 1 + (2 * (A - 1 - j) + 2) + 3)
      (fun j hj => by omega)
    omega
  · unfold compactSynUniformLoopOCost
    have e : ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 +
        compactSynUniformRoundOCost (Ka:=Ka) ds M K es ℓ w l j stk + (2 * j + 2) + 3) =
        (∑ j ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l j stk) +
          ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold compactSynUniformRoundFCost compactSynUniformRoundOCost; ring
    rw [e]
    have := hS (fun j => (4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) (fun j hj => by omega)
    omega

end
end IntegerMultBounds.MathlibTM2.Cost
