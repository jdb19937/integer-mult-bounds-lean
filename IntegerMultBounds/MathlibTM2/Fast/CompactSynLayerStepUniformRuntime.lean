module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepTopRegs
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepBasis
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopUniformRuntimeExecution

/-! Actual compact top execution from the concrete refreshed and parked state.
All top register predicates and recursive readiness are derived internally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Cost
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q Ka : ℕ} {U : Type}
open Filter

theorem compactSynParkedRuntime_uniform_eventually_exec_Hl (hQ : compactRuntimeStates ≤ Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ N : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (_hd : ComplexPhaseBudget.Realizes ds)
      (_hgate : ∀ g, Instr.gate g∈program ds →
        (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (K D o a R rBits r W p ρ : ℕ)
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
    let s := (D+1)/2+q+(backChunks d g K+
      synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let w := W+s+D
    let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
    let pcs := compactTopPcs d g K D o R₂
    let hfitT := (compactTopKernel_geometry (o := o) h hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W)
    let Ps := topPieces hρ pcs hpcs
    let low := Ps.flatMap Piece.bitsList
    ∀ (Rsrc : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
      (park : List (Fin (prime+Ka+4)))
      (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖≤2^p)
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hfile : S.R=compactSynParkedFile
        (compactSynSourceClearOut (compactSetupUpdate7 Rsrc compactBasisRefreshDst
          (compactZeroTail (compactBasisSetupValues d g K D o r))))
        (encZ (prime+Ka) W Z) park (n+a) r w K ρ
        (topCfg W s a R R₂ q aT K o D) (topPcRec K pcs)),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCost W w s n a R r K ρ q aT o D R₂ pcs
        (compactTopCallCost ds shape 1 (n+a) o r w ρ ⟨0,q,R,aT⟩)
        (compactTopCallCost ds shape 1 n o r w ρ) ∧
      Exec (compactPlacedLayerTable hQ ds) (compactTopProg (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ (prime+Ka) W
          (fun z => (⟨truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).re,
            truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).im⟩ : GaussianInt)))}) := by
  filter_upwards [compactTopRuntime_uniform_eventually_exec_Hl (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with N hrunTop
  intro ds hd hgate K D o a R rBits r W p ρ hlo hhi h hD hρ hR hr hW hRbits ha hprecision hrun hwrun
  dsimp only
  intro Rsrc hblank hdepth hguard park Z hZ v S hL hfile
  have hK : 0<K := by omega
  let working := W+((D+1)/2+compactTopKernelCount (Mult.Sizes.d N)
    (CompactReservationGrowth.guard N) K+
    (backChunks (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K+
    synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K D)
      (compactReservationActive (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K D)))+D
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
  apply hrunTop ds hd hgate K D o a R rBits r W p ρ hlo hhi h hD hρ hR hr hW hRbits ha hprecision hrun hwrun
    Z hZ v S hL
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

end
end IntegerMultBounds.MathlibTM2.Fast
