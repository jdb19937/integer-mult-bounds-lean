module
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainCalls
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynOpp
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwd
public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd


/-! Transform calls stay inside the two layer procedure tables. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

lemma compactMainBootstrap_calls :
    callsWithin (fun g : CompactMainProc => g≠compactMainOldProc .main)
      (compactMnOriginalBootstrap (A := prime+mnKa) (Q := compactMnQ) (U := Unit)) := by
  unfold compactMnOriginalBootstrap compactMnBootstrap
  refine ⟨⟨?_,?_⟩,True.intro⟩
  · simp only [compactMnBootstrapRead,ucopy,umulSym,callsWithin]
    trivial
  · exact callsWithin_embProg _ _ _ (fun f => f.elim) _

lemma compactMainStage_layer_calls (p : Pr LayerMachine.LProc (LayerMachine.nT SXReg) mnQ (prime+mnKa) Unit) :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactMainStage (embProg mnLayE MnProc.lay p)) := by
  rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff]
  refine ⟨True.intro,?_⟩
  rw [callsWithin_stateLiftPr_iff]
  exact callsWithin_embProg mnLayE MnProc.lay _ (fun _ => by intro h; cases h) p

private lemma compare_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (a b s t : Fin T) (strict : Bool) (p q : Pr P T Q A U)
    (hp : callsWithin allowed p) (hq : callsWithin allowed q) :
    callsWithin allowed (compactSynCompare a b s t strict p q) := by
  unfold compactSynCompare synIfNE
  refine ⟨by trivial,by trivial,?_,True.intro,⟨by trivial,hp⟩,by trivial,hq⟩
  cases strict <;> trivial

lemma compactMainDispatch_calls :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactSynDispatch (Ka := mnKa) Cost.brDirs) := by
  unfold compactSynDispatch compactSynDispatchWith
  apply compare_calls
  · apply compare_calls
    · exact compactMainStage_layer_calls _
    · exact callsWithin_embProg _ _ _ (fun _ => by intro h; cases h) _
  · exact compactMainStage_layer_calls _

private lemma counter_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (a h t : Fin T) (pred : Bool) (round : Pr P T Q A U) (hr : callsWithin allowed round) :
    callsWithin allowed (compactCounterBody a h t pred round) := by
  refine ⟨by trivial,?_,hr,by trivial⟩
  cases pred <;> trivial

private lemma scan_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (a t : Fin T) (p : Pr P T Q A U) (hp : callsWithin allowed p) :
    callsWithin allowed (scanP a t p) :=
  ⟨True.intro,⟨True.intro,hp,True.intro⟩,by trivial⟩

lemma compactMainLoopF_calls :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactSynLoopF (Ka := mnKa) Cost.brDirs) := by
  apply scan_calls
  apply counter_calls
  exact ⟨compactMainDispatch_calls,compactMainStage_layer_calls _⟩

lemma compactMainLoopO_calls :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactSynLoopO (Ka := mnKa) Cost.brDirs) := by
  apply scan_calls
  apply counter_calls
  exact ⟨compactMainStage_layer_calls _,compactMainDispatch_calls⟩

lemma compactMainFwd_calls (p : Pr LayerMachine.LProc (LayerMachine.nT SXReg) mnQ (prime+mnKa) Unit) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactSynFwd Cost.brDirs p) :=
  ⟨compactMainBootstrap_calls,⟨compactMainStage_layer_calls p,compactMainLoopF_calls⟩,by trivial⟩

lemma compactMainOpp_calls (p : Pr LayerMachine.LProc (LayerMachine.nT SXReg) mnQ (prime+mnKa) Unit) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactSynOpp Cost.brDirs p) :=
  ⟨compactMainBootstrap_calls,⟨compactMainLoopO_calls,compactMainStage_layer_calls p⟩,by trivial⟩


end
end IntegerMultBounds.MathlibTM2.Fast.Main
