module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerContract
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTwiddle

/-! Actual hybrid forward and opposite rounds, with original numerator semantics. -/
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

def compactSynRoundF (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynDispatch ds) (compactSynTwiddle true)

def compactSynRoundO (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynTwiddle false) (compactSynDispatch ds)

def compactSynRoundFCost (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l h stk : ℕ) : ℕ :=
  compactSynLayerCost (Ka := Ka) ds M es ℓ W l h stk+(1+synTwCost es l W h)

def compactSynRoundOCost (ds : ComplexFramedExecution.Directions) (M : ℕ)
    (es : List ℕ) (ℓ W l h stk : ℕ) : ℕ :=
  (1+synTwCost es l W h)+compactSynLayerCost (Ka := Ka) ds M es ℓ W l h stk

variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  (hA : 5≤prime+Ka) {M : ℕ} {es : List ℕ} {ℓ W l p : ℕ}
  (hLayer : CompactSynLayerContract legacy ds M es ℓ W l p)
include hbody hA hLayer

theorem compactSynRoundF_runs {h : ℕ} (hh : h+1≤ℓ) (hhl : h≤l) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ (Mult.Sizes.K M) W l h (layPerm es ℓ (Mult.Sizes.K M)))
    (P₀ : List (Fin (prime+Ka+4))) (u : Recs (2^l)) (hu : SupLe es.sum u 1)
    (Y : ℕ → Fin (2^l) → GaussianInt) (hY : SynNum p (layPerm es ℓ (Mult.Sizes.K M)) u Y)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
    (hr : CompactSynReady R M) :
    ∃ Y',SynNum p (layPerm es ℓ (Mult.Sizes.K M)) (rdR p (fwdRound es h u)) Y' ∧
      LayRuns (compactMainBody legacy ds) (compactSynRoundF ds) R
        (Function.update R (compactMnRg (.src (.v .io)))
          (cstream (prime+Ka) W (rpStream (2^es.sum) Y')))
        (compactSynRoundFCost (Ka := Ka) ds M es ℓ W l h (synStashCostW v synXS)) := by
  let Ym := synMask (2^es.sum) Y
  let Yb := synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ (Mult.Sizes.K M))))
    (fun x c => GaussianInt.toComplex (Ym x c)))
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum) Yb))
  have s1 := hLayer h hh v hv P₀ Ym (synMask_norm hY hu) R
    (by simpa only [Ym,rpStream_synMask] using hR) hr
  have s2 := compactSynTwiddle_runs legacy ds hbody true hA (by omega) hhl
    (layPerm es ℓ (Mult.Sizes.K M)) v hv P₀ Yb R₁
    (compactSynView_io R _ _ P₀ v hR)
  refine ⟨_,synRoundF_math es (layPerm es ℓ (Mult.Sizes.K M)) p h u Ym (synNum_mask hY),?_⟩
  have he := s1.seq s2
  simpa only [compactSynRoundF,compactSynRoundFCost,R₁,Function.update_idem] using he

theorem compactSynRoundO_runs {h : ℕ} (hh : h+1≤ℓ) (hhl : h≤l) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ (Mult.Sizes.K M) W l h (layPerm es ℓ (Mult.Sizes.K M)))
    (P₀ : List (Fin (prime+Ka+4))) (u : Recs (2^l)) (hu : SupLe es.sum u 1)
    (Y : ℕ → Fin (2^l) → GaussianInt) (hY : SynNum p (layPerm es ℓ (Mult.Sizes.K M)) u Y)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
    (hr : CompactSynReady R M) :
    ∃ Y',SynNum p (layPerm es ℓ (Mult.Sizes.K M)) (rdR p (oppRound es h u)) Y' ∧
      LayRuns (compactMainBody legacy ds) (compactSynRoundO ds) R
        (Function.update R (compactMnRg (.src (.v .io)))
          (cstream (prime+Ka) W (rpStream (2^es.sum) Y')))
        (compactSynRoundOCost (Ka := Ka) ds M es ℓ W l h (synStashCostW v synXS)) := by
  let Y₁ := fun m => twShiftZ (twEx false es l h (twGat (twPosL (layPerm es ℓ (Mult.Sizes.K M))) es.sum m)) (Y m)
  let Ym := synMask (2^es.sum) Y₁
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum) Y₁))
  have hY₁ := synRoundO_math es (layPerm es ℓ (Mult.Sizes.K M)) p h u Y hY
  have hu₁ : SupLe es.sum (mulY (twE es (2^l) h (parts es h)) u) 1 := mulY_supLe _ hu
  have s1 := compactSynTwiddle_runs legacy ds hbody false hA (by omega) hhl
    (layPerm es ℓ (Mult.Sizes.K M)) v hv P₀ Y R hR
  have s2 := hLayer h hh v hv P₀ Ym (synMask_norm hY₁ hu₁) R₁
    (by simpa only [Ym,rpStream_synMask] using compactSynView_io R _ _ P₀ v hR) (hr.update_io _)
  refine ⟨_,synRoundO_math2 es (layPerm es ℓ (Mult.Sizes.K M)) p h u Ym (synNum_mask hY₁),?_⟩
  have he := s1.seq s2
  simpa only [compactSynRoundO,compactSynRoundOCost,R₁,Function.update_idem] using he

end
end IntegerMultBounds.MathlibTM2.Fast.Main
