module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransformsR
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransformCalls
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainCalls
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The completed main procedure table with the placed rounded layer table, the calls of the
rounded transforms, and the rounded transforms under the main entry. -/
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

/-- The completed expanded main program is the actual main procedure. -/
def compactMainEntryTableR (main : CompactMnPr CompactMainProc (prime+mnKa)) :
    CompactMainProc → CompactMnPr CompactMainProc (prime+mnKa) :=
  fun f => match f with
  | .inl .main => main
  | .inl (.lay f) => compactMainTransport (mnLb f)
  | .inr f => compactMainNativeTableR Cost.brDirs f

@[simp] lemma compactMainEntryTableR_main (main : CompactMnPr CompactMainProc (prime+mnKa)) :
    compactMainEntryTableR main (compactMainOldProc .main)=main := rfl

/-- Calls confined to layers cannot reach the replaceable main entry. -/
lemma compactMainBodyR_layers_closed (old : MnPr (prime+mnKa)) :
    ∀ f : CompactMainProc,f≠compactMainOldProc .main →
      callsWithin (fun g => g≠compactMainOldProc .main)
        (compactMainBodyR (mnBody mnLb old) Cost.brDirs f) := by
  intro f hf
  cases f with
  | inl f =>
    cases f with
    | main => exact (hf rfl).elim
    | lay f =>
      change callsWithin _ (statePlacedPr compactMnLegacyReg compactMnQ_legacy mnQ_pos
        compactMainOldProc (mnLb f))
      rw [statePlacedPr,callsWithin_embProg_iff,callsWithin_stateLiftPr_iff]
      exact callsWithin_embProg mnLayE MnProc.lay _ (fun _ => by intro h; cases h) _
  | inr f =>
    change callsWithin _ (embProg compactMnLayerReg compactMainLayerProc _)
    exact callsWithin_embProg _ _ _ (fun _ => by intro h; cases h) _

/-- Exact layer-only executions are valid under the completed expanded procedure table. -/
theorem compactMainEntryR_exec (main : CompactMnPr CompactMainProc (prime+mnKa))
    (old : MnPr (prime+mnKa)) {prog : CompactMnPr CompactMainProc (prime+mnKa)}
    {s t : Store (HΓ (prime+mnKa)) (HS compactMnT compactMnQ (prime+mnKa) Unit)} {n : ℕ}
    (h : Exec (compactMainBodyR (mnBody mnLb old) Cost.brDirs) prog s n t)
    (hp : callsWithin (fun g => g≠compactMainOldProc .main) prog) :
    Exec (compactMainEntryTableR main) prog s n t := by
  apply exec_of_callsWithin (fun g => g≠compactMainOldProc .main) ?_
    (compactMainBodyR_layers_closed old) h hp
  intro f hf
  cases f with
  | inl f => cases f with
    | main => exact (hf rfl).elim
    | lay f => rfl
  | inr f => rfl
private lemma compare_callsR {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (a b s t : Fin T) (strict : Bool) (p q : Pr P T Q A U)
    (hp : callsWithin allowed p) (hq : callsWithin allowed q) :
    callsWithin allowed (compactSynCompare a b s t strict p q) := by
  unfold compactSynCompare synIfNE
  refine ⟨by trivial,by trivial,?_,True.intro,⟨by trivial,hp⟩,by trivial,hq⟩
  cases strict <;> trivial

lemma compactMainDispatchR_calls :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactSynDispatchR (Ka := mnKa) Cost.brDirs) := by
  unfold compactSynDispatchR compactSynDispatchWith
  apply compare_callsR
  · apply compare_callsR
    · exact compactMainStage_layer_calls _
    · exact callsWithin_embProg _ _ _ (fun _ => by intro h; cases h) _
  · exact compactMainStage_layer_calls _

private lemma counter_callsR {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (a h t : Fin T) (pred : Bool) (round : Pr P T Q A U) (hr : callsWithin allowed round) :
    callsWithin allowed (compactCounterBody a h t pred round) := by
  refine ⟨by trivial,?_,hr,by trivial⟩
  cases pred <;> trivial

private lemma scan_callsR {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (a t : Fin T) (p : Pr P T Q A U) (hp : callsWithin allowed p) :
    callsWithin allowed (scanP a t p) :=
  ⟨True.intro,⟨True.intro,hp,True.intro⟩,by trivial⟩

lemma compactMainLoopFR_calls :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactSynLoopFR (Ka := mnKa) Cost.brDirs) := by
  apply scan_callsR
  apply counter_callsR
  exact ⟨compactMainDispatchR_calls,compactMainStage_layer_calls _⟩

lemma compactMainLoopOR_calls :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactSynLoopOR (Ka := mnKa) Cost.brDirs) := by
  apply scan_callsR
  apply counter_callsR
  exact ⟨compactMainStage_layer_calls _,compactMainDispatchR_calls⟩

lemma compactMainFwdR_calls (p : Pr LayerMachine.LProc (LayerMachine.nT SXReg) mnQ (prime+mnKa) Unit) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactSynFwdR Cost.brDirs p) :=
  ⟨compactMainBootstrap_calls,⟨compactMainStage_layer_calls p,compactMainLoopFR_calls⟩,by trivial⟩

lemma compactMainOppR_calls (p : Pr LayerMachine.LProc (LayerMachine.nT SXReg) mnQ (prime+mnKa) Unit) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactSynOppR Cost.brDirs p) :=
  ⟨compactMainBootstrap_calls,⟨compactMainLoopOR_calls,compactMainStage_layer_calls p⟩,by trivial⟩


section Specs

open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem compactSynRetunedFwdR_entry_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (hg : CompactSynRetunedGeom M) (main : CompactMnPr CompactMainProc (prime+mnKa)),
    SynFwdSpecQ (compactMainEntryTableR main) (compactSynFwdR (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactRetunedFOp M hg) (compactSynRetunedFwdCostR M (compactBlCL M)) := by
  filter_upwards [compactSynRetunedFwdR_eventually] with M hspec
  intro hg main Z v S hpre hdisk hio
  obtain ⟨v',n,hu,hn,he⟩ := hspec hg (.act .done) Z v S hpre hdisk hio
  exact ⟨v',n,hu,hn,compactMainEntryR_exec main (.act .done) he (compactMainFwdR_calls _)⟩

theorem compactSynRetunedOppR_entry_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (hg : CompactSynRetunedGeom M) (main : CompactMnPr CompactMainProc (prime+mnKa)),
    SynOppSpecQ (compactMainEntryTableR main) (compactSynOppR (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactRetunedOOp M hg) (compactSynRetunedOppCostR M (compactBlCL' M)) := by
  filter_upwards [compactSynRetunedOppR_eventually] with M hspec
  intro hg main Z v S hpre hdisk hio
  obtain ⟨v',n,hu,hn,he⟩ := hspec hg (.act .done) Z v S hpre hdisk hio
  exact ⟨v',n,hu,hn,compactMainEntryR_exec main (.act .done) he (compactMainOppR_calls _)⟩
end Specs

end
end IntegerMultBounds.MathlibTM2.Fast.Main
