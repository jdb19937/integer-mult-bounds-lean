module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopFStep

/-! One actual opposite scan iteration, including its changing synthetic counters. -/
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

theorem compactSynUniformLoopO_step (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p A : ℕ}
    (hLayer : CompactSynUniformLayerContract legacy ds M K es ℓ W l p)
    (hAℓ : A≤ℓ) (hAl : A≤l+1) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    (hvh : v (.p .h)=[]) (hvc : (v (.p .c)).length=A) (hcb : blank∉v (.p .c))
    (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)) (hz : SupLe es.sum z 1) (hzg : GridR p z)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v)
    (hr : CompactSynReady R M) (j : ℕ) (hj : j<A) :
    let L := layPerm es ℓ K
    let cs := v (.p .c)
    LayRuns (compactMainBody legacy ds) (compactSynBodyO ds)
      (compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (oppRoundsC p es j z))))
        (cs.drop (j+1)) (cs.take (j+1)).reverse)
      (compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (oppRoundsC p es (j+1) z))))
        (cs.drop (j+1)) (cs.take (j+1)).reverse)
      ((4*(j+1)+4)+1+compactSynUniformRoundOCost (Ka := Ka) ds M K es ℓ W l j
        (synStashCostW v synXS+6*A+6)+(2*j+2)) := by
  dsimp only
  let L := layPerm es ℓ K
  let cs := v (.p .c)
  let Y := synYnum p L (oppRoundsC p es j z)
  let Rj := compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) Y))
    (cs.drop (j+1)) (cs.take (j+1)).reverse
  let vj := Function.update (Function.update v (.p .c) (cs.drop (j+1))) (.p .t) (cs.take (j+1)).reverse
  let h := j
  have hcd : blank∉cs.drop (j+1) := fun hx => hcb (List.mem_of_mem_drop hx)
  have hct : blank∉(cs.take (j+1)).reverse := fun hx => hcb (List.mem_of_mem_take (List.mem_reverse.1 hx))
  have hview : compactSynView Rj=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) vj := by
    dsimp only [Rj,compactSynScanState]
    rw [compactSynView_update_wire,compactSynView_update_wire,compactSynView_io R _ _ P₀ v hR,
      synG_update,synG_update]
  have hviewH : compactSynView (Function.update Rj (compactSynDispatchReg (.p .h)) (List.replicate h tick))=
      synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀)
        (synSetH v (cs.drop (j+1)) (cs.take (j+1)).reverse h) := by
    rw [compactSynView_update_wire,hview,synG_update]
    rfl
  have hready : CompactSynReady Rj M := ((hr.update_io _).update_wire (.p .c) _).update_wire (.p .t) _
  obtain ⟨Y',hY',er⟩ := compactSynUniformRoundO_runs legacy ds hbody hA hLayer (by dsimp only [h]; omega)
    (by dsimp only [h]; omega) hW _ (hv.setH hcd hct h) P₀ (oppRoundsC p es j z)
    (oppRoundsC_supLe p es j hz) Y (synNum_ynum (oppRoundsC_grid p es j hzg)) _ hviewH (hready.update_wire (.p .h) _)
  rw [synNum_stream hY'] at er
  have hclen : (Rj (compactSynDispatchReg (.p .t))).length=h+1 := by
    rw [compactSynView_wire hview]
    simp only [vj,Function.update_self,List.length_reverse,List.length_take]
    have hcs : cs.length=A := hvc
    dsimp only [h]
    omega
  have hhs : Rj (compactSynDispatchReg (.p .h))=[] := by
    rw [compactSynView_wire hview]; simpa [vj] using hvh
  have hts : Rj (compactSynDispatchReg (.s 2))=[] := by
    rw [compactSynView_wire hview]; simpa [vj] using hv.hs 2
  have hst : synStashCostW (synSetH v (cs.drop (j+1)) (cs.take (j+1)).reverse h) synXS≤
      synStashCostW v synXS+6*A+6 := by
    have he := synStashCostW_setH v (cs.drop (j+1)) (cs.take (j+1)).reverse h
    simp only [List.length_drop,List.length_reverse,List.length_take] at he
    have hcs : cs.length=A := hvc
    dsimp only [h] at he ⊢
    omega
  have eb := compactCounterBody_runs (compactMainBody legacy ds)
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .t≠.p .h))
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .t≠.s 2))
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .h≠.s 2))
    (compactSynDispatchReg_ne_io (.p .h)) hhs hts true _
    (by simpa only [ite_true,hclen,Nat.add_sub_cancel] using er)
  apply lr_weaken (compactMainBody legacy ds) eb
  · exact compactScan_update_io R (compactSynDispatchReg_ne_io (.p .c))
      (compactSynDispatchReg_ne_io (.p .t)) _ _ _ _
  · have he := compactSynUniformRoundOCost_mono (Ka := Ka) ds M K es ℓ W l h hst
    simp only [ite_true,hclen,Nat.add_sub_cancel]
    dsimp only [h] at he ⊢
    omega

end
end IntegerMultBounds.MathlibTM2.Fast.Main
