module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRefresh
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedSynLayerRecords
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry

/-! Source computation, record construction, and five-output refresh in sequence. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactStoppedSynLayerPrepare (ds : Networks.ComplexFramedExecution.Directions) :
    Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynLayerSources
    (.seq (compactStoppedTopPlaced ds (.ly 0))
      (.seq compactBasisRefresh compactSynSourceClear))

/-- Registers immediately after the real original-input constructor. -/
def compactStoppedSynLayerRecordsOut (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W h : ℕ) (ds : Networks.ComplexFramedExecution.Directions) (d g : ℕ) :=
  embExt compactLegacyReg
    (synG Ro (compactStoppedSynLayerRecordW
      (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
      ds es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W))
    (compactSynLayerSourcesOut R Ro v h (layB ℓ K) K es.length d g)

def compactStoppedSynLayerRefreshOut (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (ds : Networks.ComplexFramedExecution.Directions) (d g : ℕ) :=
  compactSetupUpdate7 (compactStoppedSynLayerRecordsOut R Ro v es ℓ K W h ds d g)
    compactBasisRefreshDst (compactZeroTail
      (compactBasisSetupValues d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)))

/-- All refresh preconditions are discharged from SynV and initially blank compact outputs. -/
theorem compactStoppedSynLayerRecordsRefresh_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (ds : Networks.ComplexFramedExecution.Directions) (d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hd : 0<d)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    LayRuns body compactBasisRefresh
      (compactStoppedSynLayerRecordsOut R Ro v es ℓ K W h ds d g)
      (compactStoppedSynLayerRefreshOut R Ro v es ℓ K W l h ds d g)
      (compactBasisRefreshCost d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)) := by
  let v₂ := compactStoppedSynLayerRecordW
    (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
    ds es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W
  have hlegacy : compactStoppedSynLayerRecordsOut R Ro v es ℓ K W h ds d g ∘ compactLegacyReg=synG Ro v₂ :=
    embExt_comp_e compactLegacyReg_injective _ _
  have hb (i : Fin 7) : compactStoppedSynLayerRecordsOut R Ro v es ℓ K W h ds d g
      (compactBasisRefreshDst i)=[] := by
    unfold compactStoppedSynLayerRecordsOut compactBasisRefreshDst
    rw [embExt_off _ _ (fun j => compactLegacyReg_ne_compact_bc j (.work (compactBasisRefreshWork i)))]
    rw [compactSynLayerSourcesOut_compact]
    exact hblank i
  have hs (i : Fin 32) (h0 : i≠0) (h1 : i≠1) (h7 : i≠7) : v₂ (.s i)=[] := by
    simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,h0,h1,h7,hv.hs]
  exact compactSynLayerRefresh_runs body _ Ro v₂ d g K es.length
    (K*((h-layB ℓ K)/K*es.length)) (2^l) hd hk
    (by simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW])
    (by simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW])
    (by simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hK])
    (by simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hD])
    (by simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by simp [v₂,compactStoppedSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hr]) hs hlegacy hb

/-- The complete preparation prefix executes without an execution premise. -/
theorem compactStoppedSynLayerPrepare_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (ds : Networks.ComplexFramedExecution.Directions) (d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hdpos : 0<d) (hgpos : 0<g)
    (hcap : CompactReservationFits d g K es.length)
    (hR : R ∘ compactLegacyReg=synG Ro v)
    (hd : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
    (hg : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    let o := K*((h-layB ℓ K)/K*es.length)
    LayRuns body (compactStoppedSynLayerPrepare ds) R
      (compactSynSourceClearOut (compactStoppedSynLayerRefreshOut R Ro v es ℓ K W l h ds d g))
      ((compactSynChunkSourceCost h (layB ℓ K) K es.length+(((4*d+4)+(4*g+4))+1))+
        (compactStoppedTopOriginalCost ds es.sum d g K es.length o W 1+
          (compactBasisRefreshCost d g K es.length o (2^l)+
            (((2*d+2)+(2*g+2))+(2*o+2)+4)))) := by
  dsimp only
  have hB := (CompactGadgetReservationCapacity.capacities d g K (by omega)).2
  change d*g≤CompactGadgetReservationCapacity.backChunks d g K*K at hB
  have hDpos : 0<es.length := by
    have hp := Nat.mul_pos hdpos hgpos
    unfold CompactReservationFits at hcap
    by_contra hz
    have hz' : es.length=0 := by omega
    have hb : CompactGadgetReservationCapacity.backChunks d g K=0 := by omega
    simp [hb] at hB
    omega
  have e₁ := compactSynLayerSources_runs body R Ro v es ℓ K W l h L d g hv hk hR hd hg
  have e₂ := compactStoppedSynLayerRecords_runs body R Ro v es ℓ K W l h L ds d g hDpos hv hk hdpos
  have e₃ := compactStoppedSynLayerRecordsRefresh_runs body R Ro v es ℓ K W l h L ds d g hv hk hdpos hblank
  let R₃ := compactStoppedSynLayerRefreshOut R Ro v es ℓ K W l h ds d g
  have hwire (x : SynW) : R₃ (compactLegacyReg (sreg x))=
      compactStoppedSynLayerRecordW (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
        ds es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W x := by
    dsimp only [R₃,compactStoppedSynLayerRefreshOut]
    rw [compactSynLayerRefresh_legacy]
    dsimp only [compactStoppedSynLayerRecordsOut]
    rw [embExt_apply compactLegacyReg_injective,synG_sreg]
  have hscratch (i : Fin 32) := hwire (.s i)
  simp only [compactSynScratch_legacy] at hscratch
  have e₄ := compactSynSourceClear_runs body R₃ d g (K*((h-layB ℓ K)/K*es.length))
    (by rw [hscratch]; simp [compactStoppedSynLayerRecordW,compactSynLayerSourceW])
    (by rw [hscratch]; simp [compactStoppedSynLayerRecordW,compactSynLayerSourceW])
    (by rw [hscratch]; simp [compactStoppedSynLayerRecordW,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by rw [←compactSynOutsideRow_legacy,hwire]; simp [compactStoppedSynLayerRecordW,compactSynLayerSourceW])
  exact e₁.seq (e₂.seq (e₃.seq e₄))

end
end IntegerMultBounds.MathlibTM2.Fast
