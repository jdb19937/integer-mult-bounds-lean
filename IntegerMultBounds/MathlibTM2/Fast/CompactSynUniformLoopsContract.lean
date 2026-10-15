module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopF
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopO

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

def CompactSynUniformLoopContract (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) (fwd : Bool) : Prop :=
  ∀ (A : ℕ),A≤ℓ → A≤l+1 → ∀ (v : SynW → List (Fin (prime+Ka+4))),
    SynV v es ℓ K W l 0 (layPerm es ℓ K) →
    v (.p .h)=[] → v (.p .t)=[] → (v (.p .c)).length=A → blank∉v (.p .c) →
    ∀ (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)),SupLe es.sum z 1 → GridR p z →
    ∀ (R : Fin compactMnT → List (Fin (prime+Ka+4))),
    compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v →
    CompactSynReady R M →
    LayRuns (compactMainBody legacy ds) (if fwd then compactSynLoopF ds else compactSynLoopO ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p (layPerm es ℓ K)
          (if fwd then fwdRoundsC p es A z else oppRoundsC p es A z)))))
      (if fwd then compactSynUniformLoopFCost (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6)
        else compactSynUniformLoopOCost (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6))

theorem compactSynUniformLoopsContract_of_layer (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p : ℕ}
    (hLayer : CompactSynUniformLayerContract legacy ds M K es ℓ W l p) (hW : p+2≤W) :
    ∀ fwd,CompactSynUniformLoopContract legacy ds M K es ℓ W l p fwd := by
  intro fwd A hAℓ hAl v hv hvh hvt hvc hcb P₀ z hz hzg R hR hr
  cases fwd
  · exact compactSynUniformLoopO_runs legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvt hvc hcb P₀ z hz hzg R hR hr
  · exact compactSynUniformLoopF_runs legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvt hvc hcb P₀ z hz hzg R hR hr

theorem compactSynUniformLoopsContract_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in Filter.atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka)),
      (∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f)) →
    ∀ (es : List ℕ) (K ℓ W l p : ℕ),CompactSynUniformGeometry M K es ℓ W l p →
      ∀ fwd,CompactSynUniformLoopContract legacy ds M K es ℓ W l p fwd := by
  filter_upwards [compactSynUniformLayerContract_eventually hA hA9 hNW] with M hLayer
  intro ds hd hgate legacy hbody es K ℓ W l p hg
  exact compactSynUniformLoopsContract_of_layer legacy ds hbody (by omega)
    (hLayer ds hd hgate legacy hbody es K ℓ W l p hg) hg.numerator

end
end IntegerMultBounds.MathlibTM2.Fast.Main
