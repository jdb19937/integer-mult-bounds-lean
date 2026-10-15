module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
public import IntegerMultBounds.MathlibTM2.Cost.CompactPieceUniformPacking
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformReadiness
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
public import IntegerMultBounds.MathlibTM2.Cost.CompactLayerReady
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPrecision

/-! The reserved top transform running the actual placed recursive layer table.
The remaining recursive readiness predicate describes geometry and packing only. -/
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

/-- For actual runtime parameters, every reserved top call is executable from
original precision and geometric capacity; no per-piece readiness premise remains. -/
theorem compactTopRuntime_uniform_eventually_exec_Hl (hQ : compactRuntimeStates ≤ Q)
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
    ∀ (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖≤2^p)
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hT : CompactTopRegs (compactHostBasisRest shape o r) S.R (n+a) r w K ρ)
      (_hI : CompactTopIn (BReg := CompactHostBReg) S.R (topCfg W s a R R₂ q aT K o D)
        (topPcRec K pcs))
      (_hio : S.R (reg (BReg := CompactHostBReg) .io)=encZ (prime+Ka) W Z),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCost W w s n a R r K ρ q aT o D R₂ pcs
        (compactTopCallCost ds shape 1 (n+a) o r w ρ ⟨0,q,R,aT⟩)
        (compactTopCallCost ds shape 1 n o r w ρ) ∧
      Exec (compactPlacedLayerTable hQ ds) (compactTopProg (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ (prime+Ka) W
          (fun z => (⟨truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).re,
            truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).im⟩ : GaussianInt)))}) := by
  filter_upwards [compactPiece_uniform_eventually_ready,compactCaller_uniform_eventually_shape] with N hp hshape
  intro ds hd hgate K D o a R rBits r W p ρ hlo hhi h hD hρ hR hr hW hRbits ha hprecision hrun hwrun
  dsimp only
  intro Z hZ v S hL hT hI hio
  have hgeom := compactTopKernel_geometry (o := o) h hρ ha
  have haddress : o+K*D≤
      o+K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a := by
    rw [←compactTopKernel_end h o]
    exact hgeom.2
  let working := W+((D+1)/2+compactTopKernelCount (Mult.Sizes.d N)
    (CompactReservationGrowth.guard N) K+
    (backChunks (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K+
    synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K D)
      (compactReservationActive (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K D)))+D
  obtain ⟨hG,hGK,hrecord⟩ := hshape K D o r working hlo hhi hD h hrun (hwrun.trans (by dsimp [working]; omega))
  refine compactTopActual_exec_Hl (Q := Q) (Ka := Ka) (U := U)
    (shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*working))))
    (d := Mult.Sizes.d N) (g := CompactReservationGrowth.guard N)
    (D := D) (oS := o) (o := o) (a := a) (R := R) (r := r) (W := W) (p := p) (ρ := ρ) (packD := 1)
    hQ ds hd hA hA9 hNW hgate h hD hρ hR hr hW (le_refl o)
    ha hG hGK hrecord hgeom.1 hgeom.2 rfl ?_ ?_ Z hZ v S hL hT hI hio
  · exact fun pc hpc => compactTopPcs_offset hpc
  · intro pc hpc
    have hc : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*working)))).chunk=K := rfl
    rw [hc] at hpc
    have hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W) (oS := o)
    have hh := hp ds K D o
      (o+K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a)
      R rBits r working ρ Ka hlo hhi hD h hρ hR hRbits haddress hprecision hrun
      (hwrun.trans (by omega)) hG hGK hrecord pc
    simp only [Nat.add_sub_cancel_left] at hh
    simpa only [hc,Nat.add_sub_cancel_left, Nat.add_sub_cancel_right] using hh hpc (hpcs pc hpc)

end
end IntegerMultBounds.MathlibTM2.Fast
