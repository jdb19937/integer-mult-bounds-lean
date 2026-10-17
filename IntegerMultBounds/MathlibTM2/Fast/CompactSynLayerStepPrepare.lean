module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRefresh
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRecords
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Source computation, record construction, and five-output refresh in sequence. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Registers immediately after the real original-input constructor. -/
def compactSynLayerRecordsOut (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W h G F d g : ℕ) :=
  embExt compactLegacyReg
    (synG Ro (compactSynLayerRecordW
      (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
      G F es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W))
    (compactSynLayerSourcesOut R Ro v h (layB ℓ K) K es.length d g)

def compactSynLayerRefreshOut (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G F d g : ℕ) :=
  compactSetupUpdate7 (compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g)
    compactBasisRefreshDst (compactZeroTail
      (compactBasisSetupValues d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)))

/-- All refresh preconditions are discharged from SynV and initially blank compact outputs. -/
theorem compactSynLayerRecordsRefresh_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (G F d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hd : 0<d)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    LayRuns body compactBasisRefresh
      (compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g)
      (compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g)
      (compactBasisRefreshCost d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)) := by
  let v₂ := compactSynLayerRecordW
    (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
    G F es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W
  have hlegacy : compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g ∘ compactLegacyReg=synG Ro v₂ :=
    embExt_comp_e compactLegacyReg_injective _ _
  have hb (i : Fin 7) : compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g
      (compactBasisRefreshDst i)=[] := by
    unfold compactSynLayerRecordsOut compactBasisRefreshDst
    rw [embExt_off _ _ (fun j => compactLegacyReg_ne_compact_bc j (.work (compactBasisRefreshWork i)))]
    rw [compactSynLayerSourcesOut_compact]
    exact hblank i
  have hs (i : Fin 32) (h0 : i≠0) (h1 : i≠1) (h7 : i≠7) : v₂ (.s i)=[] := by
    simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,h0,h1,h7,hv.hs]
  exact compactSynLayerRefresh_runs body _ Ro v₂ d g K es.length
    (K*((h-layB ℓ K)/K*es.length)) (2^l) hd hk
    (by simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW])
    (by simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW])
    (by simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hK])
    (by simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hD])
    (by simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by simp [v₂,compactSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hr]) hs hlegacy hb

/-- The complete preparation prefix executes without an execution premise. -/
theorem compactSynLayerPrepare_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (G F d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hdpos : 0<d)
    (hR : R ∘ compactLegacyReg=synG Ro v)
    (hd : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
    (hg : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    let o := K*((h-layB ℓ K)/K*es.length)
    LayRuns body (compactSynLayerPrepare G F) R
      (compactSynSourceClearOut (compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g))
      ((compactSynChunkSourceCost h (layB ℓ K) K es.length+(((4*d+4)+(4*g+4))+1))+
        (compactTopOriginalCost G F es.sum d g K es.length o W 1+
          (compactBasisRefreshCost d g K es.length o (2^l)+
            (((2*d+2)+(2*g+2))+(2*o+2)+4)))) := by
  dsimp only
  have e₁ := compactSynLayerSources_runs body R Ro v es ℓ K W l h L d g hv hk hR hd hg
  have e₂ := compactSynLayerRecords_runs body R Ro v es ℓ K W l h L G F d g hv hk hdpos
  have e₃ := compactSynLayerRecordsRefresh_runs body R Ro v es ℓ K W l h L G F d g hv hk hdpos hblank
  let R₃ := compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g
  have hwire (x : SynW) : R₃ (compactLegacyReg (sreg x))=
      compactSynLayerRecordW (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
        G F es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W x := by
    dsimp only [R₃,compactSynLayerRefreshOut]
    rw [compactSynLayerRefresh_legacy]
    dsimp only [compactSynLayerRecordsOut]
    rw [embExt_apply compactLegacyReg_injective,synG_sreg]
  have hscratch (i : Fin 32) := hwire (.s i)
  simp only [compactSynScratch_legacy] at hscratch
  have e₄ := compactSynSourceClear_runs body R₃ d g (K*((h-layB ℓ K)/K*es.length))
    (by rw [hscratch]; simp [compactSynLayerRecordW,compactSynLayerSourceW])
    (by rw [hscratch]; simp [compactSynLayerRecordW,compactSynLayerSourceW])
    (by rw [hscratch]; simp [compactSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by rw [←compactSynOutsideRow_legacy,hwire]; simp [compactSynLayerRecordW,compactSynLayerSourceW])
  exact e₁.seq (e₂.seq (e₃.seq e₄))

end
end IntegerMultBounds.MathlibTM2.Fast
