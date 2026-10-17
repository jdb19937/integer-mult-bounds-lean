module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedMainFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapView
import IntegerMultBounds.MathlibTM2.Fast.CompactSynScanFrame
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! A main-chain invariant framed by all main stage registers; precision is supplied by the stage file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

/-- Distribution wires and both reserved banks survive every main-stage register change. -/
def compactMainStablePre (M : ℕ) (S : Stacks compactMnT (prime+mnKa)) : Prop :=
  (∀ i,S.L i=[]) ∧
  (∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) ∧
  mnSynPre (mnσ (blP₀ dsW M) (compactDsyV₀ M)) (embStk compactMnLegacyReg S)

lemma compactMainStablePre_of_mid {M : ℕ} {S : Stacks compactMnT (prime+mnKa)}
    (h : compactSynRetunedMainPre M S) : compactMainStablePre M S :=
  ⟨h.1,h.2.1,h.2.2.1⟩

lemma compactMainStablePre_framed (M : ℕ) : SrcFramed compactMnRg (compactMainStablePre M) := by
  intro S S' ⟨hL,hb,hL₀,hι,hσ⟩ hfr
  refine ⟨fun i => by rw [hfr.2.2.1]; exact hL i,?_,?_,?_,?_⟩
  · intro z
    rw [hfr.2.2.2 _ (fun r => compactMnRg_ne_lay r _)]
    exact hb z
  · intro i
    change S'.L (compactMnLegacyReg i)=[]
    rw [hfr.2.2.1]
    exact hL _
  · intro j
    change S'.R (compactMnLegacyReg (mnι j))=[]
    rw [hfr.2.2.2 _ (fun r he => mnRg_ne_ι r j
      (compactMnLegacyReg_injective ((compactMnLegacyReg_rg r).trans he)))]
    exact hι j
  · intro x
    change S'.R (compactMnLegacyReg (mnLay x))=_
    rw [compactMnLegacyReg_lay,hfr.2.2.2 _ (fun r => compactMnRg_ne_lay r _)]
    simpa only [embStk_R,compactMnLegacyReg_lay] using hσ x

lemma compactMainStablePre_entry (M : ℕ) (S : Stacks compactMnT (prime+mnKa))
    (h : compactMainStablePre M S)
    (hp : (S.R (compactMnRg (.io .dpn))).length=Mult.Sizes.p M) :
    compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M) S := by
  obtain ⟨hL,hb,hpre⟩ := h
  obtain ⟨park,hpk,hR⟩ := synPre_R
    (mn_synPre_embPre (slyPk (blW dsW M) (blE M)) (blP₀_pk dsW M) (compactDsyV₀ M) _ hpre)
  have hview : compactSynView S.R=synG
      (synIdle (S.R (compactMnRg (.src (.v .io)))) park) (compactDsyV₀ M) := by
    change compactSynView S.R=synG
      (synIdle (S.R (compactMnLegacyReg (mnLayE (lreg .io)))) park) (compactDsyV₀ M) at hR
    simpa only [mnLayE_io,compactMnLegacyReg_rg] using hR
  refine ⟨hL,hp,?_,hb,park,hpk,hview⟩
  rw [compactMnSyn_dispatch,compactSynView_wire hview,compactDsy_initial_depth,List.length_replicate]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
