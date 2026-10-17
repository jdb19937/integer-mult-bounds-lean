module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainCalls
public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainLayer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The main entry runs the expanded program; both checked layer tables remain available. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

/-- The completed expanded main program is the actual main procedure. -/
def compactMainEntryTable (main : CompactMnPr CompactMainProc (prime+mnKa)) :
    CompactMainProc → CompactMnPr CompactMainProc (prime+mnKa) :=
  fun f => match f with
  | .inl .main => main
  | .inl (.lay f) => compactMainTransport (mnLb f)
  | .inr f => compactMainNativeTable Cost.brDirs f

@[simp] lemma compactMainEntryTable_main (main : CompactMnPr CompactMainProc (prime+mnKa)) :
    compactMainEntryTable main (compactMainOldProc .main)=main := rfl

/-- Calls confined to layers cannot reach the replaceable main entry. -/
lemma compactMainBody_layers_closed (old : MnPr (prime+mnKa)) :
    ∀ f : CompactMainProc,f≠compactMainOldProc .main →
      callsWithin (fun g => g≠compactMainOldProc .main)
        (compactMainBody (mnBody mnLb old) Cost.brDirs f) := by
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
theorem compactMainEntry_exec (main : CompactMnPr CompactMainProc (prime+mnKa))
    (old : MnPr (prime+mnKa)) {prog : CompactMnPr CompactMainProc (prime+mnKa)}
    {s t : Store (HΓ (prime+mnKa)) (HS compactMnT compactMnQ (prime+mnKa) Unit)} {n : ℕ}
    (h : Exec (compactMainBody (mnBody mnLb old) Cost.brDirs) prog s n t)
    (hp : callsWithin (fun g => g≠compactMainOldProc .main) prog) :
    Exec (compactMainEntryTable main) prog s n t := by
  apply exec_of_callsWithin (fun g => g≠compactMainOldProc .main) ?_
    (compactMainBody_layers_closed old) h hp
  intro f hf
  cases f with
  | inl f => cases f with
    | main => exact (hf rfl).elim
    | lay f => rfl
  | inr f => rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
