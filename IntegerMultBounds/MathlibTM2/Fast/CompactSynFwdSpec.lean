module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransformPipeline
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapTransformFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwd
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

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
variable (hM : 2≤M)
  (hp : 2≤Mult.Sizes.p M) (hd : 0<Mult.Sizes.d M)
include hbody H hAl hLoop hv₀ hvh hvt hvc hcb hLay hM hp hd

theorem compactSynFwd_spec :
    SynFwdSpec (compactMainBody legacy ds) (compactSynFwd ds layP) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ (Mult.Sizes.K M)))
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynLoopFCost (Ka := Ka) ds M (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  intro Z vv S hPre hdisk hio
  obtain ⟨hleft,hpSource,hdSource,hb,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  have hs := compactSynView_scratch hv₀ hR
  have hv := (compactMnBootstrapFinal_view S.R (Mult.Sizes.p M) (Mult.Sizes.d M) hs hb).trans hR
  have hr := compactMnBootstrapFinal_ready M hM S.R hs hb
  have hc := compactSynFwdCore_runs legacy ds hbody a H hAl hLoop v₀ hv₀ hvh hvt hvc hcb Pk layP cL hLay
    park hPk Z hdisk (compactMnBootstrapFinal S.R (Mult.Sizes.p M) (Mult.Sizes.d M)) hv hr
  have he := compactMnTransformPipeline_from_sources (compactMainBody legacy ds)
    (compactSynFwdCore ds layP) S.R (Mult.Sizes.p M) (Mult.Sizes.d M) _ _ hp hd hpSource hdSource hs hb hc
  exact he vv S hleft rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
