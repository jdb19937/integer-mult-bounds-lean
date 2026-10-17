module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialTransforms
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Concrete forward and opposite transforms with original layout programs and complete frame restoration. -/
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

/-- The actual existing layout, hybrid scan, bootstrap, and cleanup execute together. -/
theorem compactSynConcreteFwd_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynFwdSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (dsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
      (compactSynInitialFwdCost M (blCL dsW dsyV₀ M)) := by
  filter_upwards [compactSynInitialFwd_eventually,dsyV₀_wires,Mult.Sizes.eventually_big]
    with M hspec hv hbig
  intro mainP
  have hℓ : 1≤Mult.Sizes.ℓ M := by have := hbig.K_succ_le_ℓ; omega
  have hw : 1≤dsW M := by have := ds_w_B M; omega
  obtain ⟨h1,h2,h3,h4⟩ := blW_ok dsW M
  exact hspec mainP (slyPk (blW dsW M) (blE M)) (slyFwd mnQ_layer)
    (blCL dsW dsyV₀ M)
    (slyFwd_lay (Ka := mnKa) mnQ_layer Cost.brDirs (cvAx (t M)) (ds_layHyp hbig)
      (dsyV₀ M) hv.1 bl_hA hw (blW dsW M) (blE M) (bl_ax hℓ) h4 h1 h2 h3)

/-- The actual existing layout, hybrid scan, bootstrap, and cleanup execute together. -/
theorem compactSynConcreteOpp_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynOppSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (dsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
      (compactSynInitialOppCost M (blCL' dsW dsyV₀ M)) := by
  filter_upwards [compactSynInitialOpp_eventually,dsyV₀_wires,Mult.Sizes.eventually_big]
    with M hspec hv hbig
  intro mainP
  have hℓ : 1≤Mult.Sizes.ℓ M := by have := hbig.K_succ_le_ℓ; omega
  have hw : 1≤dsW M := by have := ds_w_B M; omega
  obtain ⟨h1,h2,h3,h4⟩ := blW_ok dsW M
  exact hspec mainP (slyPk (blW dsW M) (blE M)) (slyOpp mnQ_layer)
    (blCL' dsW dsyV₀ M)
    (slyOpp_lay (Ka := mnKa) mnQ_layer Cost.brDirs (cvAx (t M)) (ds_layHyp hbig)
      (dsyV₀ M) hv.1 bl_hA hw (blW dsW M) (blE M) (bl_ax hℓ) h4 h1 h2 h3)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
