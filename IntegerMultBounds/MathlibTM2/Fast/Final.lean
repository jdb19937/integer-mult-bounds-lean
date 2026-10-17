module

import IntegerMultBounds.MathlibTM2.Fast.MainFinal
import IntegerMultBounds.MathlibTM2.Fast.BundleWires
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynLay
import IntegerMultBounds.MathlibTM2.Fast.DistSynCost
public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The final combination

`fast_statement_of hmr : IntegerMultBounds.MathlibTM2.Statement` from the loop-cost bound `hmr` (the step bounds
`synLoopFCost`, `synLoopOCost` of the transforms at coefficient width `dsW`, stash cost at most
`C_s (r n + (b n + 1)^k)`, are `O(totConv n)`):

* `finStash`: the stash cost `synStashCostW (dsyV₀ n) synXS + 6 nRounds + 6` of the wires `dsyV₀`
  is at most `806 (r n + (b n + 1)^2)`, from `dsyStash_le` and `nRounds ≤ ℓ n ≤ b n`;
* `finCost hmr`: the cost field of `MnLay dsW` at the layout costs `blCL`, `blCL'` and the wires
  `dsyV₀`, from `ml_lay_cost_le` (the layout costs) and `hmr` at `C_s = 806`, `k = 2`;
* `fast_statement_of hmr`: `statement_of_wires` at the bundle `blLayDs dsyV₀ dsyV₀_wires
  (finCost hmr)` and the wires program `dsyWires`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter

noncomputable section

/-- The layout cost terms of `Cost/MatchSynLay` are those of the bundle. -/
theorem finCL_eq (v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4))) (n : ℕ) :
    mlCL dsW v₀ n = blCL dsW v₀ n := rfl

/-- The layout cost terms of `Cost/MatchSynLay` are those of the bundle. -/
theorem finCL'_eq (v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4))) (n : ℕ) :
    mlCL' dsW v₀ n = blCL' dsW v₀ n := rfl

/-- **The stash cost of the wires** with the round overhead: at most `806 (r n + (b n + 1)^2)`. -/
theorem finStash : ∀ᶠ n in atTop,
    synStashCostW (dsyV₀ n) synXS + 6 * nRounds (cvAx (t n)) + 6 ≤
      806 * (r n + (b n + 1) ^ 2) := by
  filter_upwards [dsyStash_le, eventually_big] with n hs hbig
  have h1 : nRounds (cvAx (t n)) ≤ ℓ n := dsy_nRounds_le n
  have h2 : ℓ n ≤ b n := mt_ℓ_le_b hbig
  have h3 : b n + 1 ≤ (b n + 1) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The cost field of the bundle** from the layout costs (`ml_lay_cost_le`) and the loop-cost
bound `hmr`. -/
theorem finCost
    (hmr : ∀ C_s k : ℕ, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ stk ≤ C_s * (r n + (b n + 1) ^ k),
      ((synLoopFCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
          (nRounds (cvAx (t n))) stk +
        synLoopOCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
          (nRounds (cvAx (t n))) stk : ℕ) : ℝ) ≤ C * IntegerMultBounds.MathlibTM2.Cost.totConv n) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      ((mnCF n (dsW n) (blCL dsW dsyV₀ n) (dsyV₀ n) +
        mnCO n (dsW n) (blCL' dsW dsyV₀ n) (dsyV₀ n) : ℕ) : ℝ) ≤ C * IntegerMultBounds.MathlibTM2.Cost.totConv n := by
  obtain ⟨C₁, hC₁⟩ := ml_lay_cost_le
  obtain ⟨C₂, hC₂⟩ := hmr 806 2
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [hC₁, hC₂, finStash] with n h₁ h₂ hs
  have hL := h₁ dsyV₀
  rw [finCL_eq, finCL'_eq] at hL
  have hF := h₂ _ hs
  unfold mnCF mnCO
  generalize blCL dsW dsyV₀ n = cL at hL
  generalize blCL' dsW dsyV₀ n = cL' at hL
  generalize synLoopFCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
    (nRounds (cvAx (t n))) (synStashCostW (dsyV₀ n) synXS + 6 * nRounds (cvAx (t n)) + 6) = F
    at hF
  generalize synLoopOCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
    (nRounds (cvAx (t n))) (synStashCostW (dsyV₀ n) synXS + 6 * nRounds (cvAx (t n)) + 6) = O
    at hF
  generalize IntegerMultBounds.MathlibTM2.Cost.totConv n = tc at hL hF
  push_cast at hL hF ⊢
  linarith

/-- **The statement of the fast multiplier** from the loop-cost bound `hmr`. -/
theorem fast_statement_of
    (hmr : ∀ C_s k : ℕ, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ stk ≤ C_s * (r n + (b n + 1) ^ k),
      ((synLoopFCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
          (nRounds (cvAx (t n))) stk +
        synLoopOCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
          (nRounds (cvAx (t n))) stk : ℕ) : ℝ) ≤ C * IntegerMultBounds.MathlibTM2.Cost.totConv n) :
    IntegerMultBounds.MathlibTM2.Statement :=
  statement_of_wires ⟨blLayDs dsyV₀ dsyV₀_wires (finCost hmr), ⟨dsyWires⟩⟩

end

end IntegerMultBounds.MathlibTM2.Fast.Main
