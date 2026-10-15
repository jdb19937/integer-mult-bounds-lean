module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayoutTransport
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineCompose

/-! Forward layout followed by the concrete hybrid scan, with original transform semantics. -/
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

def compactSynFwdCore (ds : ComplexFramedExecution.Directions)
    (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynLayout layP) (compactSynLoopF ds)

def compactSynFwd (ds : ComplexFramedExecution.Directions)
    (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactMnTransformPipeline (compactSynFwdCore ds layP)

variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ (Mult.Sizes.K M)) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynLoopContract legacy ds M (List.ofFn a) ℓ W l p true)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ (Mult.Sizes.K M) W l 0 (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Z : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layP
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun m => Z (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)) m)))) park) v₀) cL)
include hbody H hAl hLoop hv₀ hvh hvt hvc hcb hLay

theorem compactSynFwdCore_runs (park : List (Fin (prime+Ka+4))) (hPk : Pk park)
    (Z : ℕ → Fin (2^l) → GaussianInt) (hdisk : SupLe (List.ofFn a).sum (rpGrid p Z) 1)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBody legacy ds) (compactSynFwdCore ds layP) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (cvM a)
        (cvFwdOut p l a (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M))) Z))))
      ((1+cL)+compactSynLoopFCost (Ka := Ka) ds M (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)) := by
  let io := cstream (prime+Ka) W (rpStream (cvM a)
    (fun m => Z (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)) m)))
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) io
  have hl := compactSynLayout_runs legacy ds hbody (hLay park hPk Z) R hR
  have hview : compactSynView R₁=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^(List.ofFn a).sum) (synYnum p (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)) (rpGrid p Z)))) park) v₀ := by
    rw [synYnum_rpGrid]
    exact compactSynView_io R _ _ park v₀ hR
  have hs := hLoop (nRounds a) (nRounds_le H) hAl v₀ hv₀ hvh hvt hvc hcb park
    (rpGrid p Z) hdisk (rpGrid_grid p Z) R₁ hview (hr.update_io _)
  have he := hl.seq hs
  have hout : synYnum p (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M))
      (fwdRoundsC p (List.ofFn a) (nRounds a) (rpGrid p Z)) =
      cvFwdOut p l a (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M))) Z := rfl
  simpa only [compactSynFwdCore,R₁,Function.update_idem,ite_true,hout] using he

theorem compactSynFwdCore_spec :
    SynFwdSpec (compactMainBody legacy ds) (compactSynFwdCore ds layP) (compactMnRg (.src (.v .io)))
      (compactSynPreReady M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)))
      ((1+cL)+compactSynLoopFCost (Ka := Ka) ds M (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)) := by
  intro Z vv S hPre hdisk hio
  obtain ⟨hleft,hr,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  exact compactSynFwdCore_runs legacy ds hbody a H hAl hLoop v₀ hv₀ hvh hvt hvc hcb Pk layP cL hLay
    park hPk Z hdisk S.R hR hr vv S hleft rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
