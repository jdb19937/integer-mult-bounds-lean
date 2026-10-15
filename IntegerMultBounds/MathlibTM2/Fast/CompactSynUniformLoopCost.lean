module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformRound

/-! Actual hybrid loop costs and monotonicity in the saved synthetic wires. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.Networks
noncomputable section
variable {Ka : ℕ}

theorem compactSynUniformLayerCost_mono (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynUniformLayerCost (Ka := Ka) ds M K es ℓ W l h s≤compactSynUniformLayerCost (Ka := Ka) ds M K es ℓ W l h s' := by
  unfold compactSynUniformLayerCost
  dsimp only
  split_ifs
  · simp only [compactSynLayerRoundOverhead,compactSynLayerParkCost,compactSynLayerUnparkCost]
    omega
  · have he := synLayerStepCost_mono ds es ℓ K W l h hs
    omega

theorem compactSynUniformRoundFCost_mono (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynUniformRoundFCost (Ka := Ka) ds M K es ℓ W l h s≤compactSynUniformRoundFCost (Ka := Ka) ds M K es ℓ W l h s' :=
  Nat.add_le_add_right (compactSynUniformLayerCost_mono ds M K es ℓ W l h hs) _

theorem compactSynUniformRoundOCost_mono (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynUniformRoundOCost (Ka := Ka) ds M K es ℓ W l h s≤compactSynUniformRoundOCost (Ka := Ka) ds M K es ℓ W l h s' :=
  Nat.add_le_add_left (compactSynUniformLayerCost_mono ds M K es ℓ W l h hs) _

def compactSynUniformLoopFCost (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4*(A-1-j)+4)+1+
    compactSynUniformRoundFCost (Ka := Ka) ds M K es ℓ W l (A-1-j) stk+(2*(A-1-j)+2)+3))+2*A+4

def compactSynUniformLoopOCost (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4*(j+1)+4)+1+
    compactSynUniformRoundOCost (Ka := Ka) ds M K es ℓ W l j stk+(2*j+2)+3))+2*A+4

end
end IntegerMultBounds.MathlibTM2.Fast.Main
