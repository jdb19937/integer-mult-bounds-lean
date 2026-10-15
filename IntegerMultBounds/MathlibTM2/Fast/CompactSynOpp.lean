module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayoutTransport
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineCompose

/-! Concrete opposite hybrid scan followed by inverse layout, with original transform semantics. -/
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

def compactSynOppCore (ds : ComplexFramedExecution.Directions)
    (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynLoopO ds) (compactSynLayout layQ)

def compactSynOpp (ds : ComplexFramedExecution.Directions)
    (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactMnTransformPipeline (compactSynOppCore ds layQ)

variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ (Mult.Sizes.K M)) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynLoopContract legacy ds M (List.ofFn a) ℓ W l p false)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ (Mult.Sizes.K M) W l 0 (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layQ
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Y)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)))
          ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))) park) v₀) cL)
include hbody H hAl hLoop hv₀ hvh hvt hvc hcb hLay

theorem compactSynOppCore_runs (park : List (Fin (prime+Ka+4))) (hPk : Pk park)
    (V : ℕ → Fin (2^l) → GaussianInt) (hdisk : SupLe (List.ofFn a).sum (rpGrid p V) 1)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
      (fun m => V (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)) m)))) park) v₀)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBody legacy ds) (compactSynOppCore ds layQ) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (cvM a)
        (cvOppOut p l a V))))
      (compactSynLoopOCost (Ka := Ka) ds M (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL)) := by
  let L := layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)
  let Yout := synYnum p L (oppRoundsC p (List.ofFn a) (nRounds a) (rpGrid p V))
  let io := cstream (prime+Ka) W (rpStream (cvM a) Yout)
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) io
  have hview : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^(List.ofFn a).sum) (synYnum p L (rpGrid p V)))) park) v₀ := by
    rw [synYnum_rpGrid]
    exact hR
  have hs := hLoop (nRounds a) (nRounds_le H) hAl v₀ hv₀ hvh hvt hvc hcb park
    (rpGrid p V) hdisk (rpGrid_grid p V) R hview hr
  have hl := compactSynLayout_runs legacy ds hbody (hLay park hPk Yout) R₁
    (compactSynView_io R _ _ park v₀ hR)
  have hout : cstream (prime+Ka) W (rpStream (cvM a)
      (fun x => Yout ((layRec L) ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))=
      cstream (prime+Ka) W (rpStream (cvM a) (cvOppOut p l a V)) := by
    apply congrArg (cstream (prime+Ka) W)
    refine rpStream_congr fun x hx => ?_
    funext c
    simp only [Yout,synYnum,cvOppOut,cvNum]
    have hpi : synPi L ((layRec L) ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)=x := by
      rw [synPi_layRec,Equiv.symm_apply_apply]
      exact Nat.mod_eq_of_lt hx
    rw [hpi]
  dsimp only [L] at hout
  have he := hs.seq hl
  simpa only [compactSynOppCore,R₁,Function.update_idem,hout,Bool.false_eq_true,ite_false] using he

theorem compactSynOppCore_spec :
    SynOppSpec (compactMainBody legacy ds) (compactSynOppCore ds layQ) (compactMnRg (.src (.v .io)))
      (compactSynPreReady M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)))
      (compactSynLoopOCost (Ka := Ka) ds M (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL)) := by
  intro V vv S hPre hdisk hio
  obtain ⟨hleft,hr,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  exact compactSynOppCore_runs legacy ds hbody a H hAl hLoop v₀ hv₀ hvh hvt hvc hcb Pk layQ cL hLay
    park hPk V hdisk S.R hR hr vv S hleft rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
