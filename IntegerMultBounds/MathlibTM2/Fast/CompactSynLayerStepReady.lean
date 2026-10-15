module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPrepare
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepClear
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepWires

/-! The actual preparation output is precisely the five-output view consumed by parking. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {A : ℕ}

theorem compactSynLayerPrepare_projection
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum))
    (hv : SynV v es ℓ K W l h L) (G F d g : ℕ) :
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let shift := (D+1)/2+(q+f)+(b+synE G F active active)
    let a := es.sum-(o+K*(D-q))
    compactSynSourceClearOut (compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g) ∘ compactLegacyReg=
      synG Ro (compactSynPreparedW v K ((h-layB ℓ K)%K) (W+shift+D)
        (topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b) (CompactGlobalRowPadding.depth m d) active)))
        (topRec (topCfg W shift a 1 (compactTopRows d 1 a) (q+f) (o+K*(b+active)) K o D)).reverse) := by
  dsimp only
  have he := compactSynLayerClear_projection
    (compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g) Ro v
    h (layB ℓ K) K es.length G F es.sum d g (K*((h-layB ℓ K)/K*es.length)) W
    (compactZeroTail (compactBasisSetupValues d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)))
    (embExt_comp_e compactLegacyReg_injective _ _) (hv.hs 0) (hv.hs 1) (hv.hs 7) (hv.hly 0)
  simpa only [compactSynLayerRecordW,compactSynPreparedW,compactSynLayerRefreshOut] using he

end
end IntegerMultBounds.MathlibTM2.Fast
