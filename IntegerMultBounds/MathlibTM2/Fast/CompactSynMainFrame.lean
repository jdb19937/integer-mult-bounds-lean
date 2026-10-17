module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynConcreteTransforms
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelinePrecision
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialTransforms
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapView
import IntegerMultBounds.MathlibTM2.Fast.CompactSynScanFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineSource
public import IntegerMultBounds.MathlibTM2.Fast.MainCorrect
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

/-- The original main invariant and distributed wire file, with the new bank blank. -/
def compactSynMainPre (M : ℕ) (S : Stacks compactMnT (prime+mnKa)) : Prop :=
  (∀ i,S.L i=[]) ∧
  (∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) ∧
  mnSynPre (mnσ (blP₀ dsW M) (dsyV₀ M)) (embStk compactMnLegacyReg S) ∧
  ∃ x y,MnMid (embStk compactMnLegacyReg S) x y M

lemma compactSynMainPre_entry (M : ℕ) (S : Stacks compactMnT (prime+mnKa))
    (h : compactSynMainPre M S) :
    compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (dsyV₀ M) S := by
  obtain ⟨hL,hb,hpre,x,y,hmid⟩ := h
  have hp := compactMnBootstrap_parameter_precision (embStk compactMnLegacyReg S) x y M hmid
  change S.R (compactMnLegacyReg (mnRg (.io .dpn)))=_ at hp
  rw [compactMnLegacyReg_rg] at hp
  obtain ⟨park,hpk,hR⟩ := synPre_R
    (mn_synPre_embPre (slyPk (blW dsW M) (blE M)) (blP₀_pk dsW M) (dsyV₀ M) _ hpre)
  have hview : compactSynView S.R=synG
      (synIdle (S.R (compactMnRg (.src (.v .io)))) park) (dsyV₀ M) := by
    change compactSynView S.R=synG
      (synIdle (S.R (compactMnLegacyReg (mnLayE (lreg .io)))) park) (dsyV₀ M) at hR
    simpa only [mnLayE_io,compactMnLegacyReg_rg] using hR
  have hd : (S.R (compactMnSyn (.p .D))).length=Mult.Sizes.d M-1 := by
    rw [compactMnSyn_dispatch,compactSynView_wire hview,compactMnBootstrap_initial_depth,List.length_replicate]
  exact ⟨hL,by rw [hp,List.length_replicate],hd,hb,park,hpk,hview⟩

theorem compactSynMainFwd_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynFwdSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynMainPre M) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
      (compactSynInitialFwdCost M (blCL dsW dsyV₀ M)) := by
  filter_upwards [compactSynConcreteFwd_eventually] with M hspec
  intro mainP
  exact mn_synFwd_mono (compactSynMainPre_entry M) (hspec mainP)

theorem compactSynMainOpp_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynOppSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynMainPre M) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.Sizes.K M)))
      (compactSynInitialOppCost M (blCL' dsW dsyV₀ M)) := by
  filter_upwards [compactSynConcreteOpp_eventually] with M hspec
  intro mainP
  exact mn_synOpp_mono (compactSynMainPre_entry M) (hspec mainP)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
