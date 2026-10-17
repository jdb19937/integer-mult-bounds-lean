module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerContractR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTwiddle
import IntegerMultBounds.MathlibTM2.Fast.CompactSynDirect
import IntegerMultBounds.MathlibTM2.Fast.CompactMainLegacyRuns
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Rounded forward and opposite rounds: the rounded dispatch with the unchanged twiddle step.
On records the forward round is `compactSynFQ` (`y^(-E_h)` after `compactSynLQ`) and the
opposite round is `compactSynOQ` (`compactSynLQ` after `y^(E_h)`). -/
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

theorem compactSynTwiddleR_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
      (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (fwd : Bool) (hA : 5≤prime+Ka) {es : List ℕ} {ℓ K W l h : ℕ}
    (hW : 1≤W) (hhl : h≤l) (L : Equiv.Perm (Fin es.sum))
    (v : SynW → List (Fin (prime+Ka+4))) (hv : SynV v es ℓ K W l h L)
    (P₀ : List (Fin (prime+Ka+4))) (Y : ℕ → Fin (2^l) → GaussianInt)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v) :
    LayRuns (compactMainBodyR legacy ds) (compactSynTwiddle fwd) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (fun m => twShiftZ (twEx fwd es l h (twGat (twPosL L) es.sum m)) (Y m)))))
      (1+synTwCost es l W h) := by
  have he := sg_synTwStep (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) fwd hA hW hhl L
    (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v Y
    (by simp [synIdle,lreg]) hv.hpz hv.htw hv.hN hv.hw hv.hr hv.hlr hv.hh hv.hes hv.hD
    (hv.hs 2) (hv.hs 3) (hv.hs 23) (hv.hs 25) (hv.hs 26) (hv.hs 27) (hv.hs 28)
  rw [←synG_update_out (lreg_out (by simp))] at he
  have ei := compactLegacyLayer_runs legacy (compactMainNativeTableR ds)
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) hbody he R hR
  rw [compactLegacyLayer_io_restore _ R _ hR] at ei
  exact ei

def compactSynRoundFR (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynDispatchR ds) (compactSynTwiddle true)

def compactSynRoundOR (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynTwiddle false) (compactSynDispatchR ds)

def compactSynRoundFCostR (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h stk : ℕ) : ℕ :=
  compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h stk+(1+synTwCost es l W h)

def compactSynRoundOCostR (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h stk : ℕ) : ℕ :=
  (1+synTwCost es l W h)+compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h stk

/-- The rounded forward round on records. -/
def compactSynFQ (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l p h : ℕ) (u : Recs (2^l)) : Recs (2^l) :=
  mulYInv (twE es (2^l) h (parts es h)) (compactSynLQ ds M K es ℓ W l p h u)

/-- The rounded opposite round on records. -/
def compactSynOQ (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l p h : ℕ) (u : Recs (2^l)) : Recs (2^l) :=
  compactSynLQ ds M K es ℓ W l p h (mulY (twE es (2^l) h (parts es h)) u)

variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p : ℕ}
  (hLayer : CompactSynLayerContractR legacy ds M K es ℓ W l p)
include hbody hA hLayer

theorem compactSynRoundFR_runs {h : ℕ} (hh : h+1≤ℓ) (hhl : h≤l) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l h (layPerm es ℓ K))
    (P₀ : List (Fin (prime+Ka+4))) (u : Recs (2^l)) (hu : SupLe es.sum u 1)
    (Y : ℕ → Fin (2^l) → GaussianInt) (hY : SynNum p (layPerm es ℓ K) u Y)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
    (hr : CompactSynReady R M) :
    ∃ Y',SynNum p (layPerm es ℓ K)
        (compactSynFQ ds M K es ℓ W l p h u) Y' ∧
      LayRuns (compactMainBodyR legacy ds) (compactSynRoundFR ds) R
        (Function.update R (compactMnRg (.src (.v .io)))
          (cstream (prime+Ka) W (rpStream (2^es.sum) Y')))
        (compactSynRoundFCostR (Ka := Ka) ds M K es ℓ W l h (synStashCostW v synXS)) := by
  obtain ⟨Y₁,hY₁,s1⟩ := hLayer h hh v hv P₀ u hu Y hY R hR hr
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum) Y₁))
  have s2 := compactSynTwiddleR_runs legacy ds hbody true hA (by omega) hhl
    (layPerm es ℓ K) v hv P₀ Y₁ R₁
    (compactSynView_io R _ _ P₀ v hR)
  refine ⟨_,synNum_twF es (layPerm es ℓ K) p h hY₁,?_⟩
  have he := s1.seq s2
  simpa only [compactSynRoundFR,compactSynRoundFCostR,R₁,Function.update_idem] using he

theorem compactSynRoundOR_runs {h : ℕ} (hh : h+1≤ℓ) (hhl : h≤l) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l h (layPerm es ℓ K))
    (P₀ : List (Fin (prime+Ka+4))) (u : Recs (2^l)) (hu : SupLe es.sum u 1)
    (Y : ℕ → Fin (2^l) → GaussianInt) (hY : SynNum p (layPerm es ℓ K) u Y)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
    (hr : CompactSynReady R M) :
    ∃ Y',SynNum p (layPerm es ℓ K)
        (compactSynOQ ds M K es ℓ W l p h u) Y' ∧
      LayRuns (compactMainBodyR legacy ds) (compactSynRoundOR ds) R
        (Function.update R (compactMnRg (.src (.v .io)))
          (cstream (prime+Ka) W (rpStream (2^es.sum) Y')))
        (compactSynRoundOCostR (Ka := Ka) ds M K es ℓ W l h (synStashCostW v synXS)) := by
  let Y₁ := fun m => twShiftZ (twEx false es l h (twGat (twPosL (layPerm es ℓ K)) es.sum m)) (Y m)
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum) Y₁))
  have hY₁ := synRoundO_math es (layPerm es ℓ K) p h u Y hY
  have hu₁ : SupLe es.sum (mulY (twE es (2^l) h (parts es h)) u) 1 := mulY_supLe _ hu
  have s1 := compactSynTwiddleR_runs legacy ds hbody false hA (by omega) hhl
    (layPerm es ℓ K) v hv P₀ Y R hR
  obtain ⟨Y',hY',s2⟩ := hLayer h hh v hv P₀ _ hu₁ Y₁ hY₁ R₁
    (compactSynView_io R _ _ P₀ v hR) (hr.update_io _)
  refine ⟨Y',hY',?_⟩
  have he := s1.seq s2
  simpa only [compactSynRoundOR,compactSynRoundOCostR,R₁,Function.update_idem] using he

end
end IntegerMultBounds.MathlibTM2.Fast.Main
