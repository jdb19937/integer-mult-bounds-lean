module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepProjection
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedTopPlaced

/-! Actual original-input record construction after round source staging. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactStoppedSynLayerRecordW (v : SynW → List (Fin (A+4))) (ds : Networks.ComplexFramedExecution.Directions) (N d g K D o W : ℕ) :=
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  let E := b+((synPcs K 0 active (o+K*b) (CompactGlobalRowPadding.depth m d) active).map (compactStoppedPiece (compactGlobalCutoff D)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)
  let a := N-(o+K*(D-q))
  let shift := (D+1)/2+(q+f)+E
  Function.update (Function.update (Function.update v (.p .pr)
    (topRec (topPcRec K (compactStoppedReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active D)))) (.p .cf)
    (topRec (topCfg W shift a 1 (compactTopRows d 1 a) (q+f)
      (o+K*(b+active)) K o D)).reverse) (.p .w2) (List.replicate (W+shift+D) tick)

/-- Every scalar and blank-source condition comes from the existing round invariant
and the concrete source stage, rather than a supplied constructor execution. -/
theorem compactStoppedSynLayerRecords_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (ds : Networks.ComplexFramedExecution.Directions) (d g : ℕ)
    (hDpos : 0<es.length) (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hd : 0<d) :
    let o := K*((h-layB ℓ K)/K*es.length)
    let v₁ := compactSynLayerSourceW v h (layB ℓ K) K es.length d g
    let R₁ := compactSynLayerSourcesOut R Ro v h (layB ℓ K) K es.length d g
    LayRuns body (compactStoppedTopPlaced ds (.ly 0)) R₁
      (embExt compactLegacyReg (synG Ro (compactStoppedSynLayerRecordW v₁ ds es.sum d g K es.length o W)) R₁)
      (compactStoppedTopOriginalCost ds es.sum d g K es.length o W 1) := by
  dsimp only
  let v₁ := compactSynLayerSourceW v h (layB ℓ K) K es.length d g
  have hs (i : Fin 32) (h0 : i≠0) (h1 : i≠1) (h7 : i≠7) : v₁ (.s i)=[] := by
    simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,h0,h1,h7,hv.hs]
  have e := compactStoppedTopPlaced_runs body Ro v₁ (.ly 0) (by intro i; simp) (by simp) (by simp) (by simp)
    ds es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W 1 hDpos hd hk
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hN])
    (by simp [v₁,compactSynLayerSourceW])
    (by simp [v₁,compactSynLayerSourceW])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hK])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hD])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hw])
    (by simp [v₁,compactSynLayerSourceW])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hpr])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hcf])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hw2]) hs
  exact e.layRuns _ (compactSynLayerSourcesOut_projection R Ro v h (layB ℓ K) K es.length d g)

end
end IntegerMultBounds.MathlibTM2.Fast
