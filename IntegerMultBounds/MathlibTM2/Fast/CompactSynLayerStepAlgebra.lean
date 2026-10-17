module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCleanup
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPrepare
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Erase obsolete legacy backgrounds before the final compact cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

/-- An embedded image overwrite hides every earlier update inside that image. -/
theorem compactEmbExt_absorb_update {T T' : ℕ} {β : Type} (e : Fin T → Fin T')
    (f : Fin T → β) (R : Fin T' → β) (i : Fin T) (v : β) :
    embExt e f (Function.update R (e i) v)=embExt e f R := by
  funext x
  cases h : embInv e x with
  | none =>
    have hx : x≠e i := (embInv_none h i).symm
    simp only [embExt,h,Function.update_of_ne hx]
  | some j => simp only [embExt,h]

lemma compactSynLayer_absorb_clear
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) :
    embExt compactLegacyReg f (compactSynSourceClearOut R)=embExt compactLegacyReg f R := by
  simp only [compactSynSourceClearOut,←compactSynOutsideRow_legacy,←compactSynScratch_legacy,
    compactEmbExt_absorb_update]

lemma compactSynLayer_absorb_sources
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D d g : ℕ) :
    embExt compactLegacyReg f (compactSynLayerSourcesOut R Ro v h b K D d g)=embExt compactLegacyReg f R := by
  simp only [compactSynLayerSourcesOut,←compactSynOutsideRow_legacy,←compactSynScratch_legacy,
    compactEmbExt_absorb_update,compactEmbExt_overwrite]

lemma compactSynLayer_absorb_records
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W h G F d g : ℕ) :
    embExt compactLegacyReg f (compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g)=
      embExt compactLegacyReg f R := by
  rw [compactSynLayerRecordsOut,compactEmbExt_overwrite,compactSynLayer_absorb_sources]

/-- After legacy restoration, only the live compact refresh fields remain above the original background. -/
theorem compactSynLayer_final_background
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G F d g : ℕ) :
    embExt compactLegacyReg f
      (compactSynSourceClearOut (compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g))=
      compactSetupUpdate7 (embExt compactLegacyReg f R) compactBasisRefreshDst
        (compactZeroTail (compactBasisSetupValues d g K es.length
          (K*((h-layB ℓ K)/K*es.length)) (2^l))) := by
  rw [compactSynLayer_absorb_clear,compactSynLayerRefreshOut,
    compactSynLayerCleanup_commute,compactSynLayer_absorb_records]

end
end IntegerMultBounds.MathlibTM2.Fast
