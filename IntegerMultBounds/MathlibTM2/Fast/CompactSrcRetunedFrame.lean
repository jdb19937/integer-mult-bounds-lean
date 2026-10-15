module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedEntrySpecs

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

/-- Source arithmetic preserves the transform wires, original bootstrap sources and private bank. -/
theorem compactSynPre_source_framed_of (M : ℕ)
    (Pk : List (Fin (prime+mnKa+4)) → Prop)
    (v : SynW → List (Fin (prime+mnKa+4))) :
    SrcFramed compactSrcM.rg
      (compactSynPre (Ka := mnKa) M Pk v) := by
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
    exact compactSynView_io S.R _ _ park v hview

end
end IntegerMultBounds.MathlibTM2.Fast.Main
