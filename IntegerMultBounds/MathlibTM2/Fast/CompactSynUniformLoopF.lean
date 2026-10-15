module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopFStep

/-! Execution of the actual forward scan of hybrid synthetic rounds. -/
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

theorem compactSynUniformLoopF_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p A : ℕ}
    (hLayer : CompactSynUniformLayerContract legacy ds M K es ℓ W l p)
    (hAℓ : A≤ℓ) (hAl : A≤l+1) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    (hvh : v (.p .h)=[]) (hvt : v (.p .t)=[]) (hvc : (v (.p .c)).length=A) (hcb : blank∉v (.p .c))
    (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)) (hz : SupLe es.sum z 1) (hzg : GridR p z)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBody legacy ds) (compactSynLoopF ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p (layPerm es ℓ K) (fwdRoundsC p es A z)))))
      (compactSynUniformLoopFCost (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6)) := by
  let cs := v (.p .c)
  let L := layPerm es ℓ K
  let Φ := fun j => Function.update R (compactMnRg (.src (.v .io)))
    (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synUF p es A z j))))
  let cost := fun j => (4*(A-1-j)+4)+1+compactSynUniformRoundFCost (Ka := Ka) ds M K es ℓ W l (A-1-j)
    (synStashCostW v synXS+6*A+6)+(2*(A-1-j)+2)
  have hstep : ∀ j<cs.length,LayRuns (compactMainBody legacy ds) (compactSynBodyF ds)
      (Function.update (Function.update (Φ j) (compactSynDispatchReg (.p .c)) (cs.drop (j+1)))
        (compactSynDispatchReg (.p .t)) (cs.take (j+1)).reverse)
      (Function.update (Function.update (Φ (j+1)) (compactSynDispatchReg (.p .c)) (cs.drop (j+1)))
        (compactSynDispatchReg (.p .t)) (cs.take (j+1)).reverse) (cost j) := by
    intro j hj
    exact compactSynUniformLoopF_step legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvc hcb P₀ z hz hzg R hR hr j
      (by change j<(v (.p .c)).length at hj; rwa [hvc] at hj)
  have he := layScan_exec (body := compactMainBody legacy ds)
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .c≠.p .t)) Φ cs cost hstep
  have hcs : cs.length=A := hvc
  rw [hcs] at he
  have hc : R (compactSynDispatchReg (.p .c))=cs := compactSynView_wire hR _
  have ht : R (compactSynDispatchReg (.p .t))=[] := (compactSynView_wire hR _).trans hvt
  have hstart : Function.update (Function.update (Φ 0) (compactSynDispatchReg (.p .c)) cs)
      (compactSynDispatchReg (.p .t)) []=R := by
    rw [←hc,←ht]
    rw [compactScan_restore R (compactSynDispatchReg_ne_io (.p .c)) (compactSynDispatchReg_ne_io (.p .t))]
    dsimp only [L,synUF]
    rw [←compactSynView_io_value hR,Function.update_eq_self]
  have hend : Function.update (Function.update (Φ A) (compactSynDispatchReg (.p .c)) cs)
      (compactSynDispatchReg (.p .t)) []=
      Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p L (fwdRoundsC p es A z)))) := by
    rw [←hc,←ht]
    rw [compactScan_restore R (compactSynDispatchReg_ne_io (.p .c)) (compactSynDispatchReg_ne_io (.p .t))]
    rw [fwdRoundsC_eq_synUF]
  exact lr_weaken (compactMainBody legacy ds) (lr_congr_left _ he hstart.symm) hend (by rfl)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
