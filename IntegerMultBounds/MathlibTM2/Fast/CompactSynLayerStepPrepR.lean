module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepAlgebra
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepBasis
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopOriginalR
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCleanup
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepClear
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepWires
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRefresh
import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshRest
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The preparation of a rounded chunk round: the rounded original-input constructor
(`compactTopPlacedR`) in place of the exact one. The synthetic view after preparation is
`compactSynLayerRecordWR`: the piece record, the rounded configuration `topCfgR` and the
rounded working width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- The preparation of a rounded round. -/
def compactSynLayerPrepareR (G cG : ℕ) : Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynLayerSources
    (.seq (compactTopPlacedR G cG (.ly 0))
      (.seq compactBasisRefresh compactSynSourceClear))

/-- The synthetic wires after the rounded original-input constructor: the piece record, the
rounded configuration and the working width. -/
def compactSynLayerRecordWR (v : SynW → List (Fin (A+4))) (G cG N d g K D o W l : ℕ) :=
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  let E := b+synE G 0 active active
  let gb := guardG cG N l D
  let a := N-(o+K*(D-q))
  let shift := (D+1)/2+(q+f)+(gb+E)
  Function.update (Function.update (Function.update v (.p .pr)
    (topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active)))) (.p .cf)
    (topRec (topCfgR W shift a 1 (compactTopRows d 1 a) (q+f)
      (o+K*(b+active)) K o D gb (gb+E-5) 1)).reverse) (.p .w2)
    (List.replicate (W+shift+D+guardKc cG N l D+G+m+4) tick)
/-- Every scalar and blank-source condition comes from the existing round invariant
and the concrete source stage, rather than a supplied constructor execution. -/
theorem compactSynLayerRecordsR_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (G cG d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hd : 0<d) :
    let o := K*((h-layB ℓ K)/K*es.length)
    let v₁ := compactSynLayerSourceW v h (layB ℓ K) K es.length d g
    let R₁ := compactSynLayerSourcesOut R Ro v h (layB ℓ K) K es.length d g
    LayRuns body (compactTopPlacedR G cG (.ly 0)) R₁
      (embExt compactLegacyReg (synG Ro (compactSynLayerRecordWR v₁ G cG es.sum d g K es.length o W l)) R₁)
      (compactTopOriginalRCost G cG es.sum d g K es.length o W 1 l) := by
  dsimp only
  let v₁ := compactSynLayerSourceW v h (layB ℓ K) K es.length d g
  have hs (i : Fin 32) (h0 : i≠0) (h1 : i≠1) (h7 : i≠7) : v₁ (.s i)=[] := by
    simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,h0,h1,h7,hv.hs]
  have e := compactTopPlacedR_runs body Ro v₁ (.ly 0) (by intro i; simp) (by simp) (by simp)
    (by simp) (by simp)
    G cG es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W 1 l hd hk
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hN])
    (by simp [v₁,compactSynLayerSourceW])
    (by simp [v₁,compactSynLayerSourceW])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hK])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hD])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hw])
    (by simp [v₁,compactSynLayerSourceW])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hlr])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hpr])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hcf])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hw2])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hly])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hly])
    (by simp [v₁,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hly]) hs
  exact e.layRuns _ (compactSynLayerSourcesOut_projection R Ro v h (layB ℓ K) K es.length d g)


/-- Registers immediately after the real original-input constructor. -/
def compactSynLayerRecordsOutR (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G cG d g : ℕ) :=
  embExt compactLegacyReg
    (synG Ro (compactSynLayerRecordWR
      (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
      G cG es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W l))
    (compactSynLayerSourcesOut R Ro v h (layB ℓ K) K es.length d g)

def compactSynLayerRefreshOutR (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G cG d g : ℕ) :=
  compactSetupUpdate7 (compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g)
    compactBasisRefreshDst (compactZeroTail
      (compactBasisSetupValues d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)))

/-- All refresh preconditions are discharged from SynV and initially blank compact outputs. -/
theorem compactSynLayerRecordsRefreshR_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (G cG d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hd : 0<d)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    LayRuns body compactBasisRefresh
      (compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g)
      (compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g)
      (compactBasisRefreshCost d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)) := by
  let v₂ := compactSynLayerRecordWR
    (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
    G cG es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W l
  have hlegacy : compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g ∘ compactLegacyReg=synG Ro v₂ :=
    embExt_comp_e compactLegacyReg_injective _ _
  have hb (i : Fin 7) : compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g
      (compactBasisRefreshDst i)=[] := by
    unfold compactSynLayerRecordsOutR compactBasisRefreshDst
    rw [embExt_off _ _ (fun j => compactLegacyReg_ne_compact_bc j (.work (compactBasisRefreshWork i)))]
    rw [compactSynLayerSourcesOut_compact]
    exact hblank i
  have hs (i : Fin 32) (h0 : i≠0) (h1 : i≠1) (h7 : i≠7) : v₂ (.s i)=[] := by
    simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW,compactSynChunkSourceOut,h0,h1,h7,hv.hs]
  exact compactSynLayerRefresh_runs body _ Ro v₂ d g K es.length
    (K*((h-layB ℓ K)/K*es.length)) (2^l) hd hk
    (by simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW])
    (by simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW])
    (by simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hK])
    (by simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hD])
    (by simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by simp [v₂,compactSynLayerRecordWR,compactSynLayerSourceW,compactSynChunkSourceOut,hv.hr]) hs hlegacy hb

/-- The complete preparation prefix executes without an execution premise. -/
theorem compactSynLayerPrepareR_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum)) (G cG d g : ℕ)
    (hv : SynV v es ℓ K W l h L) (hk : 1≤K) (hdpos : 0<d)
    (hR : R ∘ compactLegacyReg=synG Ro v)
    (hd : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
    (hg : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    let o := K*((h-layB ℓ K)/K*es.length)
    LayRuns body (compactSynLayerPrepareR G cG) R
      (compactSynSourceClearOut (compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g))
      ((compactSynChunkSourceCost h (layB ℓ K) K es.length+(((4*d+4)+(4*g+4))+1))+
        (compactTopOriginalRCost G cG es.sum d g K es.length o W 1 l+
          (compactBasisRefreshCost d g K es.length o (2^l)+
            (((2*d+2)+(2*g+2))+(2*o+2)+4)))) := by
  dsimp only
  have e₁ := compactSynLayerSources_runs body R Ro v es ℓ K W l h L d g hv hk hR hd hg
  have e₂ := compactSynLayerRecordsR_runs body R Ro v es ℓ K W l h L G cG d g hv hk hdpos
  have e₃ := compactSynLayerRecordsRefreshR_runs body R Ro v es ℓ K W l h L G cG d g hv hk hdpos hblank
  let R₃ := compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g
  have hwire (x : SynW) : R₃ (compactLegacyReg (sreg x))=
      compactSynLayerRecordWR (compactSynLayerSourceW v h (layB ℓ K) K es.length d g)
        G cG es.sum d g K es.length (K*((h-layB ℓ K)/K*es.length)) W l x := by
    dsimp only [R₃,compactSynLayerRefreshOutR]
    rw [compactSynLayerRefresh_legacy]
    dsimp only [compactSynLayerRecordsOutR]
    rw [embExt_apply compactLegacyReg_injective,synG_sreg]
  have hscratch (i : Fin 32) := hwire (.s i)
  simp only [compactSynScratch_legacy] at hscratch
  have e₄ := compactSynSourceClear_runs body R₃ d g (K*((h-layB ℓ K)/K*es.length))
    (by rw [hscratch]; simp [compactSynLayerRecordWR,compactSynLayerSourceW])
    (by rw [hscratch]; simp [compactSynLayerRecordWR,compactSynLayerSourceW])
    (by rw [hscratch]; simp [compactSynLayerRecordWR,compactSynLayerSourceW,compactSynChunkSourceOut])
    (by rw [←compactSynOutsideRow_legacy,hwire]; simp [compactSynLayerRecordWR,compactSynLayerSourceW])
  exact e₁.seq (e₂.seq (e₃.seq e₄))
private lemma compactSynClear_record_sourceR
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
lemma compactSynClear_recordWR
    (v : SynW → List (Fin (A+4))) (h b K D G cG N d g o W l : ℕ)
    (h0 : v (.s 0)=[]) (h1 : v (.s 1)=[]) (h7 : v (.s 7)=[]) (hrow : v (.ly 0)=[]) :
    compactSynClearW (compactSynLayerRecordWR (compactSynLayerSourceW v h b K D d g) G cG N d g K D o W l)=
      compactSynLayerRecordWR (Function.update (Function.update v (.p .kh) (List.replicate K tick))
        (.p .rh) (List.replicate ((h-b)%K) tick)) G cG N d g K D o W l :=
  compactSynClear_record_sourceR v h b K D d g _ _ _ h0 h1 h7 hrow

/-- The cleanup projection after refresh is the original view plus metadata and records. -/
theorem compactSynLayerClearR_projection
    (Rbig : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D G cG N d g o W l : ℕ) (values : Fin 7 → ℕ)
    (hview : Rbig ∘ compactLegacyReg=
      synG Ro (compactSynLayerRecordWR (compactSynLayerSourceW v h b K D d g) G cG N d g K D o W l))
    (h0 : v (.s 0)=[]) (h1 : v (.s 1)=[]) (h7 : v (.s 7)=[]) (hrow : v (.ly 0)=[]) :
    compactSynSourceClearOut (compactSetupUpdate7 Rbig compactBasisRefreshDst values) ∘ compactLegacyReg=
      synG Ro (compactSynLayerRecordWR (Function.update (Function.update v (.p .kh) (List.replicate K tick))
        (.p .rh) (List.replicate ((h-b)%K) tick)) G cG N d g K D o W l) := by
  have hp := (compactSynLayerRefresh_projection Rbig values).trans hview
  have hc := compactSynSourceClear_projection _ Ro _ hp
  rw [compactSynClear_recordWR v h b K D G cG N d g o W l h0 h1 h7 hrow] at hc
  exact hc


theorem compactSynLayerPrepareR_projection
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum))
    (hv : SynV v es ℓ K W l h L) (G cG d g : ℕ) :
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let E := b+synE G 0 active active
    let gb := guardG cG es.sum l D
    let shift := (D+1)/2+(q+f)+(gb+E)
    let a := es.sum-(o+K*(D-q))
    compactSynSourceClearOut (compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g) ∘ compactLegacyReg=
      synG Ro (compactSynPreparedW v K ((h-layB ℓ K)%K) (W+shift+D+guardKc cG es.sum l D+G+m+4)
        (topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b) (CompactGlobalRowPadding.depth m d) active)))
        (topRec (topCfgR W shift a 1 (compactTopRows d 1 a) (q+f) (o+K*(b+active)) K o D
          gb (gb+E-5) 1)).reverse) := by
  dsimp only
  have he := compactSynLayerClearR_projection
    (compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g) Ro v
    h (layB ℓ K) K es.length G cG es.sum d g (K*((h-layB ℓ K)/K*es.length)) W l
    (compactZeroTail (compactBasisSetupValues d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)))
    (embExt_comp_e compactLegacyReg_injective _ _) (hv.hs 0) (hv.hs 1) (hv.hs 7) (hv.hly 0)
  simpa only [compactSynLayerRecordWR,compactSynPreparedW,compactSynLayerRefreshOutR] using he

lemma compactSynLayer_absorb_recordsR
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G cG d g : ℕ) :
    embExt compactLegacyReg f (compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g)=
      embExt compactLegacyReg f R := by
  rw [compactSynLayerRecordsOutR,compactEmbExt_overwrite,compactSynLayer_absorb_sources]

/-- After legacy restoration, only the live compact refresh fields remain above the original background. -/
theorem compactSynLayer_final_backgroundR
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G cG d g : ℕ) :
    embExt compactLegacyReg f
      (compactSynSourceClearOut (compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g))=
      compactSetupUpdate7 (embExt compactLegacyReg f R) compactBasisRefreshDst
        (compactZeroTail (compactBasisSetupValues d g K es.length
          (K*((h-layB ℓ K)/K*es.length)) (2^l))) := by
  rw [compactSynLayer_absorb_clear,compactSynLayerRefreshOutR,
    compactSynLayerCleanup_commute,compactSynLayer_absorb_recordsR]
lemma compactSynLayerRecordsOutR_compact
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G cG d g : ℕ) (z : CompactBReg) :
    compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g
      (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) := by
  unfold compactSynLayerRecordsOutR
  rw [embExt_off _ _ (fun i => compactLegacyReg_ne_compact_bc i z)]
  exact compactSynLayerSourcesOut_compact R Ro v h (layB ℓ K) K es.length d g z

def compactSynLayerPrepareRCost (G cG N d g K D o W r h b l : ℕ) :=
  (compactSynChunkSourceCost h b K D+(((4*d+4)+(4*g+4))+1))+
    (compactTopOriginalRCost G cG N d g K D o W 1 l+
      (compactBasisRefreshCost d g K D o r+(((2*d+2)+(2*g+2))+(2*o+2)+4)))

/-- The unpark cost of a rounded round: the configuration has `13` fields. -/
def compactSynLayerUnparkCostR (N r working K ρ prLen cfgLen stash : ℕ) :=
  ((2*cfgLen+14)+(2*cfgLen+2))+((stash+1)+synRestDownCost N r working K ρ prLen)

def compactSynLayerRoundOverheadR (G cG N d g K D o W r h b l ρ working prLen cfgLen stash : ℕ) :=
  compactSynLayerPrepareRCost G cG N d g K D o W r h b l+
    (compactSynLayerParkCost N r working K ρ prLen cfgLen stash+
      (compactSynLayerUnparkCostR N r working K ρ prLen cfgLen stash+
        compactClear7Cost (compactZeroTail (compactBasisSetupValues d g K D o r))))

end
end IntegerMultBounds.MathlibTM2.Fast
