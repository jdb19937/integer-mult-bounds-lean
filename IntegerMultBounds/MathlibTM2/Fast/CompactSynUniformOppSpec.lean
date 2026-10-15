module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformTransformPre
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformOpp

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

variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M K d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynUniformLoopContract legacy ds M K (List.ofFn a) ℓ W l p false)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layQ
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Y)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K))
          ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))) park) v₀) cL)
variable (hM : 2≤M)
  (hp : 2≤Mult.Sizes.p M) (hd : 0<Mult.Sizes.d M)
include hbody H hAl hLoop hv₀ hvh hvt hvc hcb hLay hM hp hd

theorem compactSynUniformOpp_spec :
    SynOppSpec (compactMainBody legacy ds) (compactSynOpp ds layQ) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynUniformLoopOCost (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  intro V vv S hPre hdisk hio
  obtain ⟨hleft,hpSource,hdSource,hb,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  have hs := compactSynUniformView_scratch hv₀ hR
  have hv := (compactMnBootstrapFinal_view S.R (Mult.Sizes.p M) (Mult.Sizes.d M) hs hb).trans hR
  have hr := compactMnBootstrapFinal_ready M hM S.R hs hb
  have hc := compactSynUniformOppCore_runs legacy ds hbody a H hAl hLoop v₀ hv₀ hvh hvt hvc hcb Pk layQ cL hLay
    park hPk V hdisk (compactMnBootstrapFinal S.R (Mult.Sizes.p M) (Mult.Sizes.d M)) hv hr
  have he := compactMnTransformPipeline_from_sources (compactMainBody legacy ds)
    (compactSynOppCore ds layQ) S.R (Mult.Sizes.p M) (Mult.Sizes.d M) _ _ hp hd hpSource hdSource hs hb hc
  exact he vv S hleft rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
