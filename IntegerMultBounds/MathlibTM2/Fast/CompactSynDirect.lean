module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynDispatch
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainLegacyRuns

/-! The unchanged direct synthetic round runs on the expanded host and restores its frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

theorem compactLegacyLayer_io_restore
    (R₀ : Fin (nT SXReg) → List (Fin (prime+Ka+4)))
    (R : Fin compactMnT → List (Fin (prime+Ka+4))) (io : List (Fin (prime+Ka+4)))
    (hR : (R ∘ compactMnLegacyReg) ∘ mnLayE=R₀) :
    embExt compactMnLegacyReg
      (embExt mnLayE (Function.update R₀ mnLio io) (R ∘ compactMnLegacyReg)) R=
      Function.update R (compactMnRg (.src (.v .io))) io := by
  rw [←hR,←compactEmbExt_update_image mnLayE mnLayE_inj,embExt_comp,
    ←compactEmbExt_update_image compactMnLegacyReg compactMnLegacyReg_injective,
    embExt_comp,mnLayE_io,compactMnLegacyReg_rg]

theorem compactMainDirect_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
      (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 14≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4)
    (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
    {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p h : ℕ} (hh : h+1≤ℓ)
    (hpw : p+2≤w) (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K w l h (layPerm es ℓ K)) (P₀ : List (Fin (prime+Ka+4)))
    (Y : ℕ → Fin (2^l) → GaussianInt) (hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : (R ∘ compactMnLegacyReg) ∘ mnLayE=
      synG (synIdle (cstream (prime+Ka) w (rpStream (2^es.sum) Y)) P₀) v) :
    LayRuns (compactMainBody legacy ds) (compactMainDirect ds) R
      (Function.update R (compactMnRg (.src (.v .io)))
        (cstream (prime+Ka) w (rpStream (2^es.sum) (synTrunc
          (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
            (fun x c => GaussianInt.toComplex (Y x c)))))))
      (1+synLayerStepCost ds es ℓ K w l h (synStashCostW v synXS)) := by
  have he := sg_synLayerStep (U := Unit) mnQ_layer ds hd hA hA9 hNW hgate H hh hpw v hv P₀ Y hY
  have ei := compactLegacyLayer_runs legacy (compactMainNativeTable ds)
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) hbody he R hR
  have eio (io io' : List (Fin (prime+Ka+4))) :
      synG (synIdle io' P₀) v=Function.update (synG (synIdle io P₀) v) mnLio io' := by
    rw [synG_update_out (lreg_out (by simp)),synIdle_update_io]
  rw [eio (cstream (prime+Ka) w (rpStream (2^es.sum) Y)) _,
    compactLegacyLayer_io_restore _ R _ hR] at ei
  exact ei

end
end IntegerMultBounds.MathlibTM2.Fast.Main
