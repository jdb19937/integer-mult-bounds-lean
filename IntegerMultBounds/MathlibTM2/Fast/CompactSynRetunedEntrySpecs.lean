module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransforms
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransformCalls

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

theorem compactSynRetunedFwd_entry_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ main : CompactMnPr CompactMainProc (prime+mnKa),
    SynFwdSpec (compactMainEntryTable main) (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactSynRetunedFwdCost M (compactBlCL M)) := by
  filter_upwards [compactSynRetunedFwd_eventually] with M hspec
  intro main Z v S hpre hdisk hio
  obtain ⟨v',n,hu,hn,he⟩ := hspec (.act .done) Z v S hpre hdisk hio
  exact ⟨v',n,hu,hn,compactMainEntry_exec main (.act .done) he (compactMainFwd_calls _)⟩

theorem compactSynRetunedOpp_entry_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ main : CompactMnPr CompactMainProc (prime+mnKa),
    SynOppSpec (compactMainEntryTable main) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactSynRetunedOppCost M (compactBlCL' M)) := by
  filter_upwards [compactSynRetunedOpp_eventually] with M hspec
  intro main Z v S hpre hdisk hio
  obtain ⟨v',n,hu,hn,he⟩ := hspec (.act .done) Z v S hpre hdisk hio
  exact ⟨v',n,hu,hn,compactMainEntry_exec main (.act .done) he (compactMainOpp_calls _)⟩

end
end IntegerMultBounds.MathlibTM2.Fast.Main
