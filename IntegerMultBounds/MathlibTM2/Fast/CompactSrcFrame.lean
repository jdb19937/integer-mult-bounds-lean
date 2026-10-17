module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcMachine
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre
public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain
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
open IntegerMultBounds.MathlibTM2.Fast.Src
open IntegerMultBounds.MathlibTM2.Fast.ResampA
open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

lemma compactSynView_source_frame {A : ℕ} {S S' : Stacks compactMnT A}
    (hfr : rsaFr compactSrcM.rg S S') :
    compactSynView S'.R=compactSynView (Function.update S.R (compactMnRg (.src (.v .io)))
      (S'.R (compactMnRg (.src (.v .io))))) := by
  rw [compactSynView_update_io]
  funext i
  by_cases hi : i=mnLio
  · subst i
    simp only [Function.update_self,compactSynView,Function.comp_apply,mnLayE_io,compactMnLegacyReg_rg]
  · rw [Function.update_of_ne hi]
    change S'.R (compactMnLegacyReg (mnLayE i))=S.R (compactMnLegacyReg (mnLayE i))
    rw [mnLayE_of_ne hi,compactMnLegacyReg_lay]
    exact hfr.2.2.2 _ (fun r => by rw [compactSrcM_rg]; exact compactMnRg_ne_lay _ _)

/-- Source arithmetic preserves the transform wires, original bootstrap sources and private bank. -/
theorem compactSynPre_source_framed (M : ℕ) :
    SrcFramed compactSrcM.rg
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (dsyV₀ M)) := by
  intro S S' hpre hfr
  obtain ⟨hL,hp,hd,hb,park,hpk,hview⟩ := hpre
  have hlay (x : LReg (CompactBReg ⊕ SXReg)) : S'.R (compactMnLay x)=S.R (compactMnLay x) :=
    hfr.2.2.2 _ (fun r => by rw [compactSrcM_rg]; exact compactMnRg_ne_lay _ _)
  have hp' : S'.R (compactMnRg (.io .dpn))=S.R (compactMnRg (.io .dpn)) := by
    apply hfr.2.2.2
    intro r he
    rw [compactSrcM_rg] at he
    have := compactMnRg_injective he
    cases this
  refine ⟨fun i => by rw [hfr.2.2.1]; exact hL i,by rw [hp']; exact hp,
    ?_,fun z => (hlay _).trans (hb z),park,hpk,?_⟩
  · change (S'.R (compactMnLay (.wire (synWire (.p .D))))).length=_
    rw [hlay]
    exact hd
  · rw [compactSynView_source_frame hfr]
    exact compactSynView_io S.R _ _ park (dsyV₀ M) hview

end
end IntegerMultBounds.MathlibTM2.Fast.Main
