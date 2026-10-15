module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedMainFrame

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

private lemma placedLeftBlank {T T' A : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (S₁ : Stacks T A) (S : Stacks T' A) (hL₁ : ∀ i,S₁.L i=[]) (hL : ∀ i,S.L i=[]) :
    ∀ i,(embOvr e S₁.get S).L i=[] := by
  intro j
  by_cases hj : ∃ i,e i=j
  · obtain ⟨i,rfl⟩ := hj
    simpa only [embOvr,Stacks.get,embExt_apply he] using hL₁ i
  · exact (embOvr_off (e := e) S₁.get S (fun i hi => hj ⟨i,hi⟩)).1.trans (hL j)

/-- A transported distribution state supplies every compact transform entry requirement. -/
theorem compactSynRetunedMainPre_placed (M x y : ℕ)
    (S₁ : Stacks mnT (prime+mnKa)) (S : Stacks compactMnT (prime+mnKa))
    (hpre : mnSynPre (mnσ (blP₀ dsW M) (compactDsyV₀ M)) S₁) (hmid : MnMid S₁ x y M)
    (hL : ∀ i,S.L i=[]) (hb : ∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) :
    compactSynRetunedMainPre M (compactMainFinalStacks S₁ S) := by
  refine ⟨placedLeftBlank compactMnLegacyReg compactMnLegacyReg_injective S₁ S hpre.1 hL,
    fun z => (compactMainFinalStacks_private S₁ S z).2.trans (hb z),?_,x,y,?_⟩
  · rw [compactMainFinalStacks_projection]
    exact hpre
  · rw [compactMainFinalStacks_projection]
    exact hmid

/-- The original distribution and main invariant derive bootstrap entry internally. -/
theorem compactSynRetunedPre_placed (M x y : ℕ)
    (S₁ : Stacks mnT (prime+mnKa)) (S : Stacks compactMnT (prime+mnKa))
    (hpre : mnSynPre (mnσ (blP₀ dsW M) (compactDsyV₀ M)) S₁) (hmid : MnMid S₁ x y M)
    (hL : ∀ i,S.L i=[]) (hb : ∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) :
    compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)
      (compactMainFinalStacks S₁ S) :=
  compactSynRetunedMainPre_entry M _ (compactSynRetunedMainPre_placed M x y S₁ S hpre hmid hL hb)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
