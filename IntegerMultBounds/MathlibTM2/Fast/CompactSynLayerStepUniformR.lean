module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepR
import IntegerMultBounds.MathlibTM2.Fast.CompactTopUniformRuntimeExecutionR
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCompose
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCleanup
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepBasis
import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshRest
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The rounded chunk round for every chunk width `K` between `Mult.Sizes.K M` and `d`: the
uniform twins of the parked runtime, the round execution and its stream form. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Rounds
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q Ka : ℕ} {U : Type}
open Filter

theorem compactSynParkedRuntimeR_uniform_eventually_exec (hQ : compactRuntimeStates ≤ Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ N : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
      (_hgate : ∀ g, Instr.gate g∈program ds →
        (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (K D o a R rBits r W p ρ gb s' k w : ℕ)
      (_hlo : Mult.Sizes.K N≤K) (_hhi : K≤Mult.Sizes.d N)
      (h : CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D) (hD : D≤Mult.Sizes.d N)
      (hρ : ρ<K) (hR : 1≤R) (_hr : 1≤r) (_hW : p+2≤W)
      (_hRbits : R≤2^rBits)
      (ha : CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)*K≤a)
      (_hprecision : rBits+(o+K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a)+1≤Mult.Sizes.p N)
      (_hrun : Mult.Sizes.r N≤r) (_hwrun : Mult.Sizes.p N≤W),
    let d := Mult.Sizes.d N
    let g := CompactReservationGrowth.guard N
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d R a
    let s := (D+1)/2+q+(gb+(backChunks d g K+
      synE (gateCount (program ds)) 0
        (compactReservationActive d g K D) (compactReservationActive d g K D)))
    let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
    let pcs := compactTopPcs d g K D o R₂
    let hfitT := (compactTopKernel_geometry (o := o) h hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    ∀ (_hww : W+s+D≤w) (_hs' : s'≤s)
      (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<w)
      (Rsrc : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
      (park : List (Fin (prime+Ka+4)))
      (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖≤2^p)
      (_hX : ∀ z, TopFitsZ w (topPreRW ds w a low (topTop aT ρ K q (n+a) hfitT)
        (compactTopRows_bounds (by omega) hR ha).1 Ps gb Z z))
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hfile : S.R=compactSynParkedFile
        (compactSynSourceClearOut (compactSetupUpdate7 Rsrc compactBasisRefreshDst
          (compactZeroTail (compactBasisSetupValues d g K D o r))))
        (encZ (prime+Ka) W Z) park (n+a) r w K ρ
        (topCfgR W s a R R₂ q aT K o D gb s' k) (topPcRec K pcs)),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCostR W w s n a R r K ρ q aT o D R₂ gb s' k pcs
        (compactTopCallCostR ds shape 1 (n+a) o r w ρ ⟨0,q,R,aT⟩)
        (compactTopCallCostR ds shape 1 n o r w ρ) ∧
      Exec (compactPlacedLayerTableR hQ ds) (compactTopProgR (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ
                (prime+Ka) W (topRSW ds w a low (topTop aT ρ K q (n+a) hfitT)
                  (compactTopRows_bounds (by omega) hR ha).1 Ps gb s (k*2^s') Z))}) := by
  filter_upwards [compactTopRuntimeR_uniform_eventually_exec (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with N hrunTop
  intro ds hgate K D o a R rBits r W p ρ gb s' k w hlo hhi h hD hρ hR hr hW hRbits ha hprecision hrun hwrun
  dsimp only
  intro hww hs' hscale Rsrc hblank hdepth hguard park Z hZ hX v S hL hfile
  have hK : 0<K := by omega
  let working := w
  let shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
    K D (2^o*(3*(r*working)))
  have hb := compactBasisRefresh_actual_rest (shape := shape) Rsrc (Mult.Sizes.d N)
    (CompactReservationGrowth.guard N) K D o r hblank hdepth hguard
    (compactReservation_back _ _ _ _ _ hK) rfl (compactReservation_bits hK h) rfl rfl
  have hbclear (z : CompactBReg) : compactBasisRest shape o r z
      (compactSynSourceClearOut (compactSetupUpdate7 Rsrc compactBasisRefreshDst
        (compactZeroTail (compactBasisSetupValues (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
          K D o r)))
        (reg (BReg := CompactHostBReg) (.bc (.inl z)))) := by
    rw [compactSynSourceClear_compact]
    exact hb (.inl z)
  apply hrunTop ds hgate K D o a R rBits r W p ρ gb s' k w hlo hhi h hD hρ hR hr hW hRbits ha hprecision
    hrun hwrun hww hs' hscale Z hZ hX v S hL
  · rw [hfile]
    exact compactSynParkedFile_topRegs _ _ _ _ _ _ _ _ _ _ shape o hbclear
  · rw [hfile]
    exact compactSynParkedFile_topIn _ _ _ _ _ _ _ _ _ _
  · rw [hfile]
    unfold compactSynParkedFile
    have he : compactLegacyReg (lreg .io)=reg (BReg := CompactHostBReg) .io := by
      simp [lreg,compactLegacyReg,compactMapRegName]
    rw [←he,embExt_apply compactLegacyReg_injective,synG_of_ne (lreg_out (by simp))]
    simp [synRestFile,synIdle,lreg]

theorem compactSynLayerStepR_uniform_eventually_exec (hQ : compactRuntimeStates≤Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
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
    let E := backChunks d g K+
      synE (gateCount (program ds)) 0
        (compactReservationActive d g K D) (compactReservationActive d g K D)
    let gb := guardG (cGain ds) es.sum l D
    let s := (D+1)/2+q+(gb+E)
    let s' := gb+E-5
    let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
    let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
    let pfs := topPcRec K pcs
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
    ∀ (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<working)
      (v : SynW → List (Fin (prime+Ka+4))) (L : Equiv.Perm (Fin es.sum))
      (_hv : SynV v es ℓ K W l h L) (P₀ : List (Fin (prime+Ka+4)))
      (Z : ZArr (Fin 1 × Fin r) (n+a))
      (_hZ : ∀ z,‖GaussianInt.toComplex (Z z)‖≤2^p)
      (_hX : ∀ z, TopFitsZ working (topPreRW ds working a low (topTop aT ρ K q (n+a) hfitT)
        hR₂ Ps gb Z z))
      (R : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hlegacy : R ∘ compactLegacyReg=synG (synIdle (encZ (prime+Ka) W Z) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g),
    LayRuns (compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds) (compactSynLayerStepR ds) R
      (Function.update R (reg (BReg := CompactHostBReg) .io) (encZ (prime+Ka) W
        (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps gb s (1*2^s') Z)))
      (compactSynLayerRoundOverheadR (gateCount (program ds)) (cGain ds)
        es.sum d g K D o W r h (layB ℓ K) l ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
          (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCostR ds shape 1 n o r working ρ)) := by
  filter_upwards [compactSynParkedRuntimeR_uniform_eventually_exec (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with M htopRuntime
  intro ds hgate es K ℓ W l h p
  dsimp only
  intro hlo hhi hdpos hKpos hchunk hcap hD haddr ha hprecision hrun hwrun hW hscale v L hv P₀ Z hZ hX R hlegacy hblank hdepth hguard
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
  let E := backChunks d g K+
    synE (gateCount (program ds)) 0
      (compactReservationActive d g K D) (compactReservationActive d g K D)
  let gb := guardG (cGain ds) es.sum l D
  let s := (D+1)/2+q+(gb+E)
  let s' := gb+E-5
  let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
  let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
  let pcs := compactTopPcs d g K D o R₂
  let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
  let pfs := topPcRec K pcs
  have hρ : ρ<K := Nat.mod_lt _ (by omega)
  have hn : n≤es.sum := by
    have hm := Nat.mul_le_mul_left K (Nat.sub_le D (CompactGlobalRowPadding.rowAxes NW m d))
    exact (Nat.add_le_add_left hm o).trans haddr
  have htotal : n+a=es.sum := Nat.add_sub_of_le hn
  let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
  let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
  let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
  let Ps := topPiecesR hρ pcs hpcsR
  let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
  let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
  let io := encZ (prime+Ka) W Z
  let io' := encZ (prime+Ka) W
    (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps gb s (1*2^s') Z)
  let Ro := synIdle io P₀
  let body := compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds
  let G := gateCount (program ds)
  let cG := cGain ds
  let Rsrc := compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g
  let Rready := compactSynSourceClearOut (compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g)
  let park := synStkW v blank synXS ++ blank :: P₀
  let Rpark := compactSynParkedFile Rready io park es.sum r working K ρ cfg pfs
  let Rdone := compactSynParkedFile Rready io' park es.sum r working K ρ cfg pfs
  let restored := synG (synIdle io' P₀) v
  let Rrest := embExt compactLegacyReg restored Rdone
  let values := compactBasisSetupValues d g K D o r
  let prepCost := compactSynLayerPrepareRCost G cG es.sum d g K D o W r h (layB ℓ K) l
  let parkCost := compactSynLayerParkCost es.sum r working K ρ
    (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length (synStashCostW v synXS)
  let topCost := compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
    (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
    (compactTopCallCostR ds shape 1 n o r working ρ)
  let unparkCost := compactSynLayerUnparkCostR es.sum r working K ρ
    (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length (synStashCostW v synXS)
  let cleanCost := compactClear7Cost (compactZeroTail values)
  have hblankDst (i : Fin 7) : R (compactBasisRefreshDst i)=[] := by
    apply hblank (.work (compactBasisRefreshWork i)) <;> fin_cases i <;> decide
  have ep : LayRuns body (compactSynLayerPrepareR G cG) R Rready prepCost :=
    compactSynLayerPrepareR_runs body R Ro v es ℓ K W l h L G cG d g hv hKpos hdpos hlegacy hdepth hguard hblankDst
  have hview : Rready ∘ compactLegacyReg=synG Ro
      (compactSynPreparedW v K ρ working (topRec pfs) (topRec cfg).reverse) := by
    have he := compactSynLayerPrepareR_projection R Ro v es ℓ K W l h L hv G cG d g
    simpa only [Rready,working,s,s',gb,E,q,aT,cfg,pfs,pcs,compactTopPcs,compactRebasePc_record,
      compactTopKernelCount,compactTopKernelOffset,compactReservationActive,d,g,D,o,ρ,r,n,a,G,cG,R₂] using he
  have ek : LayRuns body compactSynLayerPark Rready Rpark parkCost :=
    compactSynLayerPark_runs body Rready v es ℓ K W l h L hv ρ working (topRec pfs) cfg io P₀ hview
  have hoff (z : CompactBReg) : Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) :=
    compactSynLayerRecordsOutR_compact R Ro v es ℓ K W l h G cG d g z
  have hprec : 0+(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)+a)+1≤Mult.Sizes.p M := by
    rw [Nat.zero_add]
    change n+a+1≤Mult.Sizes.p M
    rw [htotal]
    exact hprecision
  have et : LayRuns body (compactTopProgR (.call .layer)) Rpark Rdone topCost := by
    intro vb S hL hR
    obtain ⟨vb',c,hu,hc,he⟩ := htopRuntime ds hgate K D o a 1 0 r W p ρ gb s' 1 working hlo hhi hcap hD hρ
      (by omega) (by change 1≤2^l; exact Nat.one_le_two_pow) hW (by simp) ha hprec
      hrun hwrun (by simp only [working, s, E, gb, q, d, g, D]; omega)
      (by simp only [s', E, gb, d, g, D]; omega) hscale Rsrc
      (by intro z h13 h14; rw [hoff]; exact hblank z h13 h14)
      (by rw [hoff]; exact hdepth) (by rw [hoff]; exact hguard) park Z hZ hX vb S hL
      (by rw [hR]; change Rpark=compactSynParkedFile Rready io park (n+a) r working K ρ cfg pfs; rw [htotal])
    rw [hR] at he
    have hi : Function.update Rpark (reg (BReg := CompactHostBReg) .io) io'=Rdone :=
      compactSynParkedFile_io_update Rready io io' park es.sum r working K ρ cfg pfs
    rw [hi] at he
    exact ⟨vb',c,hu,hc,he⟩
  have eu : LayRuns body compactSynLayerUnparkR Rdone Rrest unparkCost :=
    compactSynLayerUnparkR_runs body Rready v es ℓ K W l h L hv ρ working pfs cfg
      (by simp [cfg,topCfgR,topCfg]) io' P₀
  have erest : Rrest=embExt compactLegacyReg restored
      (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values)) := by
    unfold Rrest Rdone compactSynParkedFile
    rw [compactEmbExt_overwrite]
    -- The preparation changes only its explicit refresh counters outside the legacy image.
    dsimp only [Rready]
    rw [compactSynLayer_final_backgroundR]
    exact (compactSynLayerCleanup_commute restored R (compactZeroTail values)).symm
  have ec : LayRuns body compactBasisRefreshCleanup Rrest
      (Function.update R (reg (BReg := CompactHostBReg) .io) io') cleanCost := by
    rw [erest]
    have he := compactSynLayerCleanup_runs body restored R values hblankDst
    rw [compactSynRestored_io_update R io io' P₀ v hlegacy] at he
    exact he
  have eall := compactSynLayerStepR_compose body ds R Rready Rpark Rdone Rrest
    (Function.update R (reg (BReg := CompactHostBReg) .io) io') prepCost parkCost topCost unparkCost cleanCost ep ek et eu ec
  apply eall.mono
  change prepCost+(parkCost+(topCost+(unparkCost+cleanCost)))≤
    (prepCost+(parkCost+(unparkCost+cleanCost)))+topCost
  omega

theorem compactSynLayerStepR_uniform_eventually_exec_stream (hQ : compactRuntimeStates≤Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
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
    ∀ (_hlo : Mult.Sizes.K M≤K) (_hhi : K≤d) (_hdpos : 0<d) (hKpos : 1≤K) (_hchunk : synChunk ℓ K h) (_H : LayHyp es ℓ K)
      (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (_haddr : o+K*D≤es.sum)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤r) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W),
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let E := backChunks d g K+
      synE (gateCount (program ds)) 0
        (compactReservationActive d g K D) (compactReservationActive d g K D)
    let gb := guardG (cGain ds) es.sum l D
    let s := (D+1)/2+q+(gb+E)
    let s' := gb+E-5
    let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
    let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
    let pfs := topPcRec K pcs
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
    ∀ (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<working)
      (v : SynW → List (Fin (prime+Ka+4))) (L : Equiv.Perm (Fin es.sum))
      (_hv : SynV v es ℓ K W l h L) (P₀ : List (Fin (prime+Ka+4)))
      (Y : ℕ → Fin r → GaussianInt)
      (_hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      (_hX : ∀ z, TopFitsZ working (topPreRW ds working a low (topTop aT ρ K q (n+a) hfitT)
        hR₂ Ps gb (synZ (n+a) Y) z))
      (R : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hlegacy : R ∘ compactLegacyReg=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g),
    LayRuns (compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds) (compactSynLayerStepR ds) R
      (Function.update R (reg (BReg := CompactHostBReg) .io) (cstream (prime+Ka) W
        (rpStream (2^es.sum) (synRd (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps
          gb s (1*2^s') (synZ (n+a) Y))))))
      (compactSynLayerRoundOverheadR (gateCount (program ds)) (cGain ds)
        es.sum d g K D o W r h (layB ℓ K) l ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
          (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCostR ds shape 1 n o r working ρ)) := by
  filter_upwards [compactSynLayerStepR_uniform_eventually_exec (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with M hexec
  intro ds hgate es K ℓ W l h p
  dsimp only
  intro hlo hhi hdpos hKpos hchunk H hcap hD haddr ha hprecision hrun hwrun hW hscale v L hv P₀ Y hY hX R hlegacy hblank hdepth hguard
  have hn : K*((h-layB ℓ K)/K*es.length)+
      K*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))≤es.sum := by
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _).trans haddr
  have hna := Nat.add_sub_of_le hn
  let n := K*((h-layB ℓ K)/K*es.length)+
      K*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))
  have hinput : R ∘ compactLegacyReg=synG (synIdle
      (encZ (prime+Ka) W (synZ (n+(es.sum-n)) Y)) P₀) v := by
    rw [encZ_synZ,hna]
    exact hlegacy
  have he := hexec ds hgate es K ℓ W l h p hlo hhi hdpos hKpos hchunk hcap hD haddr ha
    hprecision hrun hwrun hW hscale v L hv P₀ (synZ _ Y) (fun z => hY _ _) hX R
    hinput hblank hdepth hguard
  have hpow : (2:ℕ)^(n+(es.sum-n))=2^es.sum := by rw [hna]
  rw [encZ_eq_synRd, hpow] at he
  exact he

end
end IntegerMultBounds.MathlibTM2.Fast
