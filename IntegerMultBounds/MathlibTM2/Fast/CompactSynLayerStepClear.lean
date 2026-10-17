module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRefresh
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRecords
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Source-copy cleanup preserves constructed records and restores the original scratch view. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactSynClearW (v : SynW → List (Fin (A+4))) :=
  Function.update (Function.update (Function.update (Function.update v (.s 0) []) (.s 1) []) (.s 7) []) (.ly 0) []

private lemma compactSynClear_record_source
    (v : SynW → List (Fin (A+4))) (h b K D d g : ℕ) (pr cf w2 : List (Fin (A+4)))
    (h0 : v (.s 0)=[]) (h1 : v (.s 1)=[]) (h7 : v (.s 7)=[]) (hrow : v (.ly 0)=[]) :
    compactSynClearW (Function.update (Function.update (Function.update
      (compactSynLayerSourceW v h b K D d g) (.p .pr) pr) (.p .cf) cf) (.p .w2) w2)=
    Function.update (Function.update (Function.update (Function.update (Function.update v
      (.p .kh) (List.replicate K tick)) (.p .rh) (List.replicate ((h-b)%K) tick))
      (.p .pr) pr) (.p .cf) cf) (.p .w2) w2 := by
  funext x
  by_cases hx0 : x=.s 0
  · subst x; simp [compactSynClearW,h0]
  by_cases hx1 : x=.s 1
  · subst x; simp [compactSynClearW,h1]
  by_cases hx7 : x=.s 7
  · subst x; simp [compactSynClearW,h7]
  by_cases hxrow : x=.ly 0
  · subst x; simp [compactSynClearW,hrow]
  simp [compactSynClearW,compactSynLayerSourceW,compactSynChunkSourceOut,
    Function.update_apply,hx0,hx1,hx7,hxrow]

/-- Scratch and the outside-row source return to their original blank contents;
only chunk metadata and the constructed records remain in the synthetic file. -/
lemma compactSynClear_recordW
    (v : SynW → List (Fin (A+4))) (h b K D G F N d g o W : ℕ)
    (h0 : v (.s 0)=[]) (h1 : v (.s 1)=[]) (h7 : v (.s 7)=[]) (hrow : v (.ly 0)=[]) :
    compactSynClearW (compactSynLayerRecordW (compactSynLayerSourceW v h b K D d g) G F N d g K D o W)=
      compactSynLayerRecordW (Function.update (Function.update v (.p .kh) (List.replicate K tick))
        (.p .rh) (List.replicate ((h-b)%K) tick)) G F N d g K D o W :=
  compactSynClear_record_source v h b K D d g _ _ _ h0 h1 h7 hrow

private lemma compactClear_legacy_update
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (x : SynW) :
    Function.update R (compactLegacyReg (sreg x)) [] ∘ compactLegacyReg=
      Function.update (R ∘ compactLegacyReg) (sreg x) [] := by
  funext i
  simp only [Function.comp_apply,Function.update_apply,compactLegacyReg_injective.eq_iff]

lemma compactSynSourceClear_projection
    (Rbig : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (hview : Rbig ∘ compactLegacyReg=synG Ro v) :
    compactSynSourceClearOut Rbig ∘ compactLegacyReg=synG Ro (compactSynClearW v) := by
  simp only [compactSynSourceClearOut,←compactSynOutsideRow_legacy,←compactSynScratch_legacy,
    compactClear_legacy_update,hview,synG_update,compactSynClearW]

/-- The cleanup projection after refresh is the original view plus metadata and records. -/
theorem compactSynLayerClear_projection
    (Rbig : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D G F N d g o W : ℕ) (values : Fin 7 → ℕ)
    (hview : Rbig ∘ compactLegacyReg=
      synG Ro (compactSynLayerRecordW (compactSynLayerSourceW v h b K D d g) G F N d g K D o W))
    (h0 : v (.s 0)=[]) (h1 : v (.s 1)=[]) (h7 : v (.s 7)=[]) (hrow : v (.ly 0)=[]) :
    compactSynSourceClearOut (compactSetupUpdate7 Rbig compactBasisRefreshDst values) ∘ compactLegacyReg=
      synG Ro (compactSynLayerRecordW (Function.update (Function.update v (.p .kh) (List.replicate K tick))
        (.p .rh) (List.replicate ((h-b)%K) tick)) G F N d g K D o W) := by
  have hp := (compactSynLayerRefresh_projection Rbig values).trans hview
  have hc := compactSynSourceClear_projection _ Ro _ hp
  rw [compactSynClear_recordW v h b K D G F N d g o W h0 h1 h7 hrow] at hc
  exact hc

end
end IntegerMultBounds.MathlibTM2.Fast
