module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformFwdSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformOppSpec
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynOpp
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwd
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

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

open Filter

theorem compactSynUniformFwd_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka))
  (_hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  (K d ℓ W l p : ℕ) (a : Fin d → ℕ)
  (_hg : CompactSynUniformGeometry M K (List.ofFn a) ℓ W l p) (_hAl : nRounds a≤l+1)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (_hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (_hvh : v₀ (.p .h)=[]) (_hvt : v₀ (.p .t)=[]) (_hvc : (v₀ (.p .c)).length=nRounds a)
  (_hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (_hLay : ∀ park,Pk park → ∀ Z : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layP
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) park) v₀) cL),
    SynFwdSpec (compactMainBody legacy ds) (compactSynFwd ds layP) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynUniformLoopFCost (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  filter_upwards [eventually_ge_atTop 2,compactSynUniformLoopsContract_eventually hA hA9 hNW]
    with M hM hloops
  intro ds hd hgate legacy hbody K d ℓ W l p a hg hAl v₀ hv₀ hvh hvt hvc hcb Pk lay cL hLay
  have hp : 2≤Mult.Sizes.p M := by
    have hb := Mult.Sizes.one_le_b hM
    unfold Mult.Sizes.p
    omega
  have hLoop := hloops ds hd hgate legacy hbody (List.ofFn a) K ℓ W l p hg true
  exact compactSynUniformFwd_spec legacy ds hbody a hg.layout hAl hLoop v₀ hv₀ hvh hvt hvc hcb
    Pk lay cL hLay hM hp hg.depth

theorem compactSynUniformOpp_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka))
  (_hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  (K d ℓ W l p : ℕ) (a : Fin d → ℕ)
  (_hg : CompactSynUniformGeometry M K (List.ofFn a) ℓ W l p) (_hAl : nRounds a≤l+1)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (_hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (_hvh : v₀ (.p .h)=[]) (_hvt : v₀ (.p .t)=[]) (_hvc : (v₀ (.p .c)).length=nRounds a)
  (_hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (_hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layQ
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Y)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K))
          ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))) park) v₀) cL),
    SynOppSpec (compactMainBody legacy ds) (compactSynOpp ds layQ) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynUniformLoopOCost (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  filter_upwards [eventually_ge_atTop 2,compactSynUniformLoopsContract_eventually hA hA9 hNW]
    with M hM hloops
  intro ds hd hgate legacy hbody K d ℓ W l p a hg hAl v₀ hv₀ hvh hvt hvc hcb Pk lay cL hLay
  have hp : 2≤Mult.Sizes.p M := by
    have hb := Mult.Sizes.one_le_b hM
    unfold Mult.Sizes.p
    omega
  have hLoop := hloops ds hd hgate legacy hbody (List.ofFn a) K ℓ W l p hg false
  exact compactSynUniformOpp_spec legacy ds hbody a hg.layout hAl hLoop v₀ hv₀ hvh hvt hvc hcb
    Pk lay cL hLay hM hp hg.depth

end
end IntegerMultBounds.MathlibTM2.Fast.Main
