module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwdSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynOppSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialLoops
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynOpp
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwd
public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain
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
open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

def compactSynInitialFwdCost (M cL : ℕ) : ℕ :=
  (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynLoopFCost (Ka := mnKa) Cost.brDirs M (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (nRounds (cvAx (t M)))
        (synStashCostW (A := prime+mnKa) (dsyV₀ M) synXS+6*nRounds (cvAx (t M))+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2))))

theorem compactSynInitialFwd_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (mainP : MnPr (prime+mnKa)) (Pk : List (Fin (prime+mnKa+4)) → Prop)
      (layP : Pr LProc (nT SXReg) mnQ (prime+mnKa) Unit) (cL : ℕ)
    (_hLay : ∀ park,Pk park → ∀ Z : ℕ → Fin (2^(Mult.Sizes.ℓ M)) → GaussianInt,
    LayRuns (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs) layP
      (synG (synIdle (cstream (prime+mnKa) (dsW M) (rpStream (cvM (cvAx (t M))) Z)) park) (dsyV₀ M))
      (synG (synIdle (cstream (prime+mnKa) (dsW M) (rpStream (cvM (cvAx (t M)))
        (fun m => Z (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)) m)))) park) (dsyV₀ M)) cL),
    SynFwdSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynFwd (Ka := mnKa) Cost.brDirs layP) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M Pk (dsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
      (compactSynInitialFwdCost M cL) := by
  filter_upwards [compactSynInitialLoops_eventually,dsyV₀_wires,Mult.Sizes.eventually_big]
    with M hloop hv hbig
  intro mainP Pk layP cL hLay
  obtain ⟨hv₀,hvh,hvt,hvc,hcb⟩ := hv
  have hAl : nRounds (cvAx (t M))≤Mult.Sizes.ℓ M+1 :=
    (nRounds_le (ds_layHyp hbig)).trans (Nat.le_succ _)
  have hp : 2≤Mult.Sizes.p M := by
    have hb := Mult.Sizes.one_le_b hbig.1
    change 2≤6*Mult.Sizes.b M
    omega
  exact compactSynFwd_spec (mnBody mnLb mainP) Cost.brDirs (mn_body_lay mainP)
    (cvAx (t M)) (ds_layHyp hbig) hAl (hloop mainP true)
    (dsyV₀ M) hv₀ hvh hvt hvc hcb Pk layP cL hLay hbig.1 hp
    (by have := hbig.one_le_d; omega)

def compactSynInitialOppCost (M cL : ℕ) : ℕ :=
  (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynLoopOCost (Ka := mnKa) Cost.brDirs M (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (nRounds (cvAx (t M)))
        (synStashCostW (A := prime+mnKa) (dsyV₀ M) synXS+6*nRounds (cvAx (t M))+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2))))

theorem compactSynInitialOpp_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (mainP : MnPr (prime+mnKa)) (Pk : List (Fin (prime+mnKa+4)) → Prop)
      (layQ : Pr LProc (nT SXReg) mnQ (prime+mnKa) Unit) (cL : ℕ)
    (_hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^(Mult.Sizes.ℓ M)) → GaussianInt,
    LayRuns (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs) layQ
      (synG (synIdle (cstream (prime+mnKa) (dsW M) (rpStream (cvM (cvAx (t M))) Y)) park) (dsyV₀ M))
      (synG (synIdle (cstream (prime+mnKa) (dsW M) (rpStream (cvM (cvAx (t M)))
        (fun x => Y ((layRec (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
          ⟨x % 2^(List.ofFn (cvAx (t M))).sum,Nat.mod_lt _ (by positivity)⟩)))) park) (dsyV₀ M)) cL),
    SynOppSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynOpp (Ka := mnKa) Cost.brDirs layQ) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M Pk (dsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
      (compactSynInitialOppCost M cL) := by
  filter_upwards [compactSynInitialLoops_eventually,dsyV₀_wires,Mult.Sizes.eventually_big]
    with M hloop hv hbig
  intro mainP Pk layQ cL hLay
  obtain ⟨hv₀,hvh,hvt,hvc,hcb⟩ := hv
  have hAl : nRounds (cvAx (t M))≤Mult.Sizes.ℓ M+1 :=
    (nRounds_le (ds_layHyp hbig)).trans (Nat.le_succ _)
  have hp : 2≤Mult.Sizes.p M := by
    have hb := Mult.Sizes.one_le_b hbig.1
    change 2≤6*Mult.Sizes.b M
    omega
  exact compactSynOpp_spec (mnBody mnLb mainP) Cost.brDirs (mn_body_lay mainP)
    (cvAx (t M)) (ds_layHyp hbig) hAl (hloop mainP false)
    (dsyV₀ M) hv₀ hvh hvt hvc hcb Pk layQ cL hLay hbig.1 hp
    (by have := hbig.one_le_d; omega)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
