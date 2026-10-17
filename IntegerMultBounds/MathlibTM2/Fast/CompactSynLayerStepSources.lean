module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStep
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The actual first stage starts from SynV and initialized persistent globals. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactSynLayerSourcesOut (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D d g : ℕ) :=
  Function.update (Function.update (Function.update
    (embExt compactLegacyReg (synG Ro (compactSynChunkSourceOut v h b K D)) R)
    (compactSynScratch 0) (List.replicate d tick)) (compactSynScratch 1) (List.replicate g tick))
    compactSynOutsideRow [tick]

theorem compactSynLayerSources_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K w l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (d g : ℕ)
    (hv : SynV v es ℓ K w l h L) (hk : 1≤K)
    (hR : R ∘ compactLegacyReg=synG Ro v)
    (hd : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
    (hg : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g) :
    LayRuns body compactSynLayerSources R
      (compactSynLayerSourcesOut R Ro v h (layB ℓ K) K es.length d g)
      (compactSynChunkSourceCost h (layB ℓ K) K es.length+(((4*d+4)+(4*g+4))+1)) := by
  let v₁ := compactSynChunkSourceOut v h (layB ℓ K) K es.length
  let R₁ := embExt compactLegacyReg (synG Ro v₁) R
  have e₁ := (compactSynChunkSourcePlaced_runs body Ro v h (layB ℓ K) K es.length hk
    hv.hs hv.hkh hv.hrh hv.hh hv.hb hv.hK hv.hD).layRuns R hR
  have hwire (x : SynW) : R₁ (compactLegacyReg (sreg x))=v₁ x := by
    rw [show R₁=embExt compactLegacyReg (synG Ro v₁) R from rfl,
      embExt_apply compactLegacyReg_injective,synG_sreg]
  have hscratch (i : Fin 32) : R₁ (compactSynScratch i)=v₁ (.s i) := by
    rw [←compactSynScratch_legacy]; exact hwire (.s i)
  have hglobal (i : Fin 30) : R₁ (reg (BReg := CompactHostBReg) (.bc (.inl (.work i))))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl (.work i)))) :=
    embExt_off _ _ (fun j => compactLegacyReg_ne_compact_bc j (.work i))
  have e₂ := compactSynGlobalRead_runs body R₁ d g
    (by rw [hglobal]; exact hd) (by rw [hglobal]; exact hg)
    (by rw [hscratch]; simp [v₁,compactSynChunkSourceOut,hv.hs])
    (by rw [hscratch]; simp [v₁,compactSynChunkSourceOut,hv.hs])
    (by rw [hscratch]; simp [v₁,compactSynChunkSourceOut,hv.hs])
  have hrow : R₁ compactSynOutsideRow=[] := by
    have he : compactLegacyReg (sreg (.ly 0))=compactSynOutsideRow := by
      simp [sreg_eq,compactLegacyReg,compactMapRegName,compactSynOutsideRow]
    rw [←he,hwire]
    simp [v₁,compactSynChunkSourceOut,hv.hly]
  have hr0 : compactSynOutsideRow≠compactSynScratch 0 := reg_ne (by simp)
  have hr1 : compactSynOutsideRow≠compactSynScratch 1 := reg_ne (by simp)
  have e₃ := compactSynOutsideRowPush_runs body
    (Function.update (Function.update R₁ (compactSynScratch 0) (List.replicate d tick))
      (compactSynScratch 1) (List.replicate g tick))
    (by rw [Function.update_of_ne hr1,Function.update_of_ne hr0,hrow])
  simpa only [compactSynLayerSources,compactSynLayerSourcesOut,R₁,v₁] using e₁.seq (e₂.seq e₃)

end
end IntegerMultBounds.MathlibTM2.Fast
