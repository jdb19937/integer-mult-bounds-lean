module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCompose
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCost
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepAlgebra
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUniformRuntime
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCleanup
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepReady
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepBasis
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStep
public import IntegerMultBounds.MathlibTM2.Fast.CompactPieceGeometry
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! A whole actual chunk round, from existing synthetic state and initialized
original globals, through the real compact top, back to the original register file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Cost
open CompactGadgetReservationCapacity
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q Ka : ℕ} {U : Type}
open Filter

theorem compactSynLayerStep_uniform_eventually_exec_Hl (hQ : compactRuntimeStates≤Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
      (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (es : List ℕ) (K ℓ W l h p : ℕ),
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let ρ := (h-layB ℓ K)%K
    let r := 2^l
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := es.sum-n
    ∀ (_hlo : Mult.Sizes.K M≤K) (_hhi : K≤d) (_hdpos : 0<d) (hKpos : 1≤K) (_hchunk : synChunk ℓ K h)
      (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (_haddr : o+K*D≤es.sum)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤r) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W),
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let s := (D+1)/2+q+(backChunks d g K+
      synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let working := W+s+D
    let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W s a 1 R₂ q aT K o D
    let pfs := topPcRec K pcs
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    ∀ (v : SynW → List (Fin (prime+Ka+4))) (L : Equiv.Perm (Fin es.sum))
      (_hv : SynV v es ℓ K W l h L) (P₀ : List (Fin (prime+Ka+4)))
      (Z : ZArr (Fin 1 × Fin r) (n+a))
      (_hZ : ∀ z,‖GaussianInt.toComplex (Z z)‖≤2^p)
      (R : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hlegacy : R ∘ compactLegacyReg=synG (synIdle (encZ (prime+Ka) W Z) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g),
    LayRuns (compactPlacedLayerTable (Ka := Ka) (U := U) hQ ds) (compactSynLayerStep ds) R
      (Function.update R (reg (BReg := CompactHostBReg) .io) (encZ (prime+Ka) W
        (fun z => (⟨truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).re,
          truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).im⟩ : GaussianInt))))
      (compactSynLayerRoundOverhead (gateCount (program ds)) (factorCount (program ds))
        es.sum d g K D o W r h (layB ℓ K) ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCost W working s n a 1 r K ρ q aT o D R₂ pcs
          (compactTopCallCost ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCost ds shape 1 n o r working ρ)) := by
  filter_upwards [compactSynParkedRuntime_uniform_eventually_exec_Hl (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with M htopRuntime
  intro ds hd hgate es K ℓ W l h p
  dsimp only
  intro hlo hhi hdpos hKpos hchunk hcap hD haddr ha hprecision hrun hwrun hW v L hv P₀ Z hZ R hlegacy hblank hdepth hguard
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let D := es.length
  let o := K*((h-layB ℓ K)/K*D)
  let ρ := (h-layB ℓ K)%K
  let r := 2^l
  let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
  let a := es.sum-n
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D o
  let R₂ := compactTopRows d 1 a
  let s := (D+1)/2+q+(backChunks d g K+
    synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive d g K D) (compactReservationActive d g K D))
  let working := W+s+D
  let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
  let pcs := compactTopPcs d g K D o R₂
  let cfg := topCfg W s a 1 R₂ q aT K o D
  let pfs := topPcRec K pcs
  have hρ : ρ<K := Nat.mod_lt _ (by omega)
  have hn : n≤es.sum := by
    have hm := Nat.mul_le_mul_left K (Nat.sub_le D (CompactGlobalRowPadding.rowAxes NW m d))
    exact (Nat.add_le_add_left hm o).trans haddr
  have htotal : n+a=es.sum := Nat.add_sub_of_le hn
  let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
  let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
  let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
  let io := encZ (prime+Ka) W Z
  let io' := encZ (prime+Ka) W (fun z => (⟨
    truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).re,
    truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).im⟩ : GaussianInt))
  let Ro := synIdle io P₀
  let body := compactPlacedLayerTable (Ka := Ka) (U := U) hQ ds
  let G := gateCount (program ds)
  let F := factorCount (program ds)
  let Rsrc := compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g
  let Rready := compactSynSourceClearOut (compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g)
  let park := synStkW v blank synXS ++ blank :: P₀
  let Rpark := compactSynParkedFile Rready io park es.sum r working K ρ cfg pfs
  let Rdone := compactSynParkedFile Rready io' park es.sum r working K ρ cfg pfs
  let restored := synG (synIdle io' P₀) v
  let Rrest := embExt compactLegacyReg restored Rdone
  let values := compactBasisSetupValues d g K D o r
  let prepCost := compactSynLayerPrepareCost G F es.sum d g K D o W r h (layB ℓ K)
  let parkCost := compactSynLayerParkCost es.sum r working K ρ
    (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length (synStashCostW v synXS)
  let topCost := compactTopCost W working s n a 1 r K ρ q aT o D R₂ pcs
    (compactTopCallCost ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
    (compactTopCallCost ds shape 1 n o r working ρ)
  let unparkCost := compactSynLayerUnparkCost es.sum r working K ρ
    (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length (synStashCostW v synXS)
  let cleanCost := compactClear7Cost (compactZeroTail values)
  have hblankDst (i : Fin 7) : R (compactBasisRefreshDst i)=[] := by
    apply hblank (.work (compactBasisRefreshWork i)) <;> fin_cases i <;> decide
  have ep : LayRuns body (compactSynLayerPrepare G F) R Rready prepCost :=
    compactSynLayerPrepare_runs body R Ro v es ℓ K W l h L G F d g hv hKpos hdpos hlegacy hdepth hguard hblankDst
  have hview : Rready ∘ compactLegacyReg=synG Ro
      (compactSynPreparedW v K ρ working (topRec pfs) (topRec cfg).reverse) := by
    have he := compactSynLayerPrepare_projection R Ro v es ℓ K W l h L hv G F d g
    simpa only [Rready,working,s,q,aT,cfg,pfs,pcs,compactTopPcs,compactRebasePc_record,
      compactTopKernelCount,compactTopKernelOffset,compactReservationActive,d,g,D,o,ρ,r,n,a,G,F,R₂] using he
  have ek : LayRuns body compactSynLayerPark Rready Rpark parkCost :=
    compactSynLayerPark_runs body Rready v es ℓ K W l h L hv ρ working (topRec pfs) cfg io P₀ hview
  have hoff (z : CompactBReg) : Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) :=
    compactSynLayerRecordsOut_compact R Ro v es ℓ K W h G F d g z
  have hprec : 0+(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)+a)+1≤Mult.Sizes.p M := by
    rw [Nat.zero_add]
    change n+a+1≤Mult.Sizes.p M
    rw [htotal]
    exact hprecision
  have et : LayRuns body (compactTopProg (.call .layer)) Rpark Rdone topCost := by
    intro vb S hL hR
    obtain ⟨vb',c,hu,hc,he⟩ := htopRuntime ds hd hgate K D o a 1 0 r W p ρ hlo hhi hcap hD hρ
      (by omega) (by change 1≤2^l; exact Nat.one_le_two_pow) hW (by simp) ha hprec
      hrun hwrun Rsrc
      (by intro z h13 h14; rw [hoff]; exact hblank z h13 h14)
      (by rw [hoff]; exact hdepth) (by rw [hoff]; exact hguard) park Z hZ vb S hL
      (by rw [hR]; change Rpark=compactSynParkedFile Rready io park (n+a) r working K ρ cfg pfs; rw [htotal])
    rw [hR] at he
    have hi : Function.update Rpark (reg (BReg := CompactHostBReg) .io) io'=Rdone :=
      compactSynParkedFile_io_update Rready io io' park es.sum r working K ρ cfg pfs
    rw [hi] at he
    exact ⟨vb',c,hu,hc,he⟩
  have eu : LayRuns body compactSynLayerUnpark Rdone Rrest unparkCost :=
    compactSynLayerUnpark_runs body Rready v es ℓ K W l h L hv ρ working pfs cfg
      (by simp [cfg,topCfg]) io' P₀
  have erest : Rrest=embExt compactLegacyReg restored
      (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values)) := by
    unfold Rrest Rdone compactSynParkedFile
    rw [compactEmbExt_overwrite]
    -- The preparation changes only its explicit refresh counters outside the legacy image.
    dsimp only [Rready]
    rw [compactSynLayer_final_background]
    exact (compactSynLayerCleanup_commute restored R (compactZeroTail values)).symm
  have ec : LayRuns body compactBasisRefreshCleanup Rrest
      (Function.update R (reg (BReg := CompactHostBReg) .io) io') cleanCost := by
    rw [erest]
    have he := compactSynLayerCleanup_runs body restored R values hblankDst
    rw [compactSynRestored_io_update R io io' P₀ v hlegacy] at he
    exact he
  have eall := compactSynLayerStep_compose body ds R Rready Rpark Rdone Rrest
    (Function.update R (reg (BReg := CompactHostBReg) .io) io') prepCost parkCost topCost unparkCost cleanCost ep ek et eu ec
  apply eall.mono
  change prepCost+(parkCost+(topCost+(unparkCost+cleanCost)))≤
    (prepCost+(parkCost+(unparkCost+cleanCost)))+topCost
  omega

end
end IntegerMultBounds.MathlibTM2.Fast
