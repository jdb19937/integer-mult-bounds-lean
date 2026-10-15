module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransforms
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelinePrecision

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

lemma compactDsy_initial_depth (M : ℕ) :
    compactDsyV₀ M (.p .D)=List.replicate (Mult.Sizes.d M-1) tick := by
  change List.replicate (dsyEs M).length tick=_
  rw [ds_length_cvAx]

/-- The original main invariant and distributed wire file, with the new bank blank. -/
def compactSynRetunedMainPre (M : ℕ) (S : Stacks compactMnT (prime+mnKa)) : Prop :=
  (∀ i,S.L i=[]) ∧
  (∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) ∧
  mnSynPre (mnσ (blP₀ dsW M) (compactDsyV₀ M)) (embStk compactMnLegacyReg S) ∧
  ∃ x y,MnMid (embStk compactMnLegacyReg S) x y M

lemma compactSynRetunedMainPre_entry (M : ℕ) (S : Stacks compactMnT (prime+mnKa))
    (h : compactSynRetunedMainPre M S) :
    compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M) S := by
  obtain ⟨hL,hb,hpre,x,y,hmid⟩ := h
  have hp := compactMnBootstrap_parameter_precision (embStk compactMnLegacyReg S) x y M hmid
  change S.R (compactMnLegacyReg (mnRg (.io .dpn)))=_ at hp
  rw [compactMnLegacyReg_rg] at hp
  obtain ⟨park,hpk,hR⟩ := synPre_R
    (mn_synPre_embPre (slyPk (blW dsW M) (blE M)) (blP₀_pk dsW M) (compactDsyV₀ M) _ hpre)
  have hview : compactSynView S.R=synG
      (synIdle (S.R (compactMnRg (.src (.v .io)))) park) (compactDsyV₀ M) := by
    change compactSynView S.R=synG
      (synIdle (S.R (compactMnLegacyReg (mnLayE (lreg .io)))) park) (compactDsyV₀ M) at hR
    simpa only [mnLayE_io,compactMnLegacyReg_rg] using hR
  have hd : (S.R (compactMnSyn (.p .D))).length=Mult.Sizes.d M-1 := by
    rw [compactMnSyn_dispatch,compactSynView_wire hview,compactDsy_initial_depth,List.length_replicate]
  exact ⟨hL,by rw [hp,List.length_replicate],hd,hb,park,hpk,hview⟩

theorem compactSynRetunedMainFwd_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynFwdSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynRetunedMainPre M) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactSynRetunedFwdCost M (compactBlCL M)) := by
  filter_upwards [compactSynRetunedFwd_eventually] with M hspec
  intro mainP
  exact mn_synFwd_mono (compactSynRetunedMainPre_entry M) (hspec mainP)

theorem compactSynRetunedMainOpp_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynOppSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynRetunedMainPre M) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactSynRetunedOppCost M (compactBlCL' M)) := by
  filter_upwards [compactSynRetunedOpp_eventually] with M hspec
  intro mainP
  exact mn_synOpp_mono (compactSynRetunedMainPre_entry M) (hspec mainP)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
