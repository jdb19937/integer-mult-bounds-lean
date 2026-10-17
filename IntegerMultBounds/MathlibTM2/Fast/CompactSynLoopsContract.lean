module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopF
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopO
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopBody
public import IntegerMultBounds.MathlibTM2.Fast.SynFwd
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Uniform original-semantics contracts for both concrete hybrid scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

def CompactSynLoopContract (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (M : ℕ) (es : List ℕ) (ℓ W l p : ℕ) (fwd : Bool) : Prop :=
  ∀ (A : ℕ),A≤ℓ → A≤l+1 → ∀ (v : SynW → List (Fin (prime+Ka+4))),
    SynV v es ℓ (Mult.Sizes.K M) W l 0 (layPerm es ℓ (Mult.Sizes.K M)) →
    v (.p .h)=[] → v (.p .t)=[] → (v (.p .c)).length=A → blank∉v (.p .c) →
    ∀ (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)),SupLe es.sum z 1 → GridR p z →
    ∀ (R : Fin compactMnT → List (Fin (prime+Ka+4))),
    compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ (Mult.Sizes.K M)) z))) P₀) v →
    CompactSynReady R M →
    LayRuns (compactMainBody legacy ds) (if fwd then compactSynLoopF ds else compactSynLoopO ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p (layPerm es ℓ (Mult.Sizes.K M))
          (if fwd then fwdRoundsC p es A z else oppRoundsC p es A z)))))
      (if fwd then compactSynLoopFCost (Ka := Ka) ds M es ℓ W l A (synStashCostW v synXS+6*A+6)
        else compactSynLoopOCost (Ka := Ka) ds M es ℓ W l A (synStashCostW v synXS+6*A+6))

theorem compactSynLoopsContract_of_layer (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M : ℕ} {es : List ℕ} {ℓ W l p : ℕ}
    (hLayer : CompactSynLayerContract legacy ds M es ℓ W l p) (hW : p+2≤W) :
    ∀ fwd,CompactSynLoopContract legacy ds M es ℓ W l p fwd := by
  intro fwd A hAℓ hAl v hv hvh hvt hvc hcb P₀ z hz hzg R hR hr
  cases fwd
  · exact compactSynLoopO_runs legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvt hvc hcb P₀ z hz hzg R hR hr
  · exact compactSynLoopF_runs legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvt hvc hcb P₀ z hz hzg R hR hr

end
end IntegerMultBounds.MathlibTM2.Fast.Main
