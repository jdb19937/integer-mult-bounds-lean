module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRound
import IntegerMultBounds.MathlibTM2.Fast.SynFwd
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Actual hybrid loop costs and monotonicity in the saved synthetic wires. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.Networks
noncomputable section
variable {Ka : ℕ}

theorem compactSynLayerCost_mono (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynLayerCost (Ka := Ka) ds M es ℓ W l h s≤compactSynLayerCost (Ka := Ka) ds M es ℓ W l h s' := by
  unfold compactSynLayerCost
  dsimp only
  split_ifs
  · simp only [compactSynLayerRoundOverhead,compactSynLayerParkCost,compactSynLayerUnparkCost]
    omega
  · have he := synLayerStepCost_mono ds es ℓ (Mult.Sizes.K M) W l h hs
    omega

theorem compactSynRoundFCost_mono (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynRoundFCost (Ka := Ka) ds M es ℓ W l h s≤compactSynRoundFCost (Ka := Ka) ds M es ℓ W l h s' :=
  Nat.add_le_add_right (compactSynLayerCost_mono ds M es ℓ W l h hs) _

theorem compactSynRoundOCost_mono (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynRoundOCost (Ka := Ka) ds M es ℓ W l h s≤compactSynRoundOCost (Ka := Ka) ds M es ℓ W l h s' :=
  Nat.add_le_add_left (compactSynLayerCost_mono ds M es ℓ W l h hs) _

def compactSynLoopFCost (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4*(A-1-j)+4)+1+
    compactSynRoundFCost (Ka := Ka) ds M es ℓ W l (A-1-j) stk+(2*(A-1-j)+2)+3))+2*A+4

def compactSynLoopOCost (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4*(j+1)+4)+1+
    compactSynRoundOCost (Ka := Ka) ds M es ℓ W l j stk+(2*j+2)+3))+2*A+4

end
end IntegerMultBounds.MathlibTM2.Fast.Main
