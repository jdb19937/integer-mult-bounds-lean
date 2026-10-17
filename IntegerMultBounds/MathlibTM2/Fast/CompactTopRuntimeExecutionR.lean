module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecutionR
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRuntimeExecution

/-! The reserved rounded top transform at actual runtime parameters: readiness of every
rounded piece follows from original precision and geometric capacity
(`compactPiece_eventually_readyR`), and the transform leaves the stream of `topRSW` with the
working width width `w ≥ W + s + D`, `s = ⌈D/2⌉ + q + gb + E_R`, `E_R` the scale sum of the pieces. -/
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

/-- `compactPiece_eventually_ready` for rounded pieces. -/
theorem compactPiece_eventually_readyR : ∀ᶠ N : ℕ in atTop,
    ∀ (D o address R rBits r w ρ Ka : ℕ),
    let d := Mult.Sizes.d N
    let g := CompactReservationGrowth.guard N
    let K := Mult.Sizes.K N
    let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
    let n := K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let R₂ := compactTopRows d R (address-(o+n))
    ∀ (_hD : D≤d) (_hfit : CompactReservationFits d g K D)
      (_hρ : ρ<K) (_hR : 0<R) (_hRbits : R≤2^rBits) (_haddress : o+K*D≤address)
      (_hprecision : rBits+address+1≤Mult.Sizes.p N)
      (_hr : Mult.Sizes.r N≤r) (_hw : Mult.Sizes.p N≤w)
      (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
      (hrecord : shape.bits+1≤shape.payload)
      (pc : TopPc) (_hpc : pc∈compactTopPcs d g K D o R₂)
      (hok : pc.OkR K (o+n) R₂),
    CompactLayerReady shape n o pc.u ρ pc.R₀ r w Ka 1 hok.hR₀ hG hGK hrecord
      (compactLayerBasisBudget (nT CompactBReg) 1 shape pc.u pc.R₀ n) pc.j (pc.a₀-o) := by
  filter_upwards [compactPiece_eventually_packed] with N hp
  intro D o address R rBits r w ρ Ka
  dsimp only
  intro hD hfit hρ hR hRbits haddress hprecision hr hw hG hGK hrecord pc hpc hok
  cases hj : pc.j with
  | zero => simp only [CompactLayerReady]
  | succ j =>
    obtain ⟨left,right,layout⟩ := compactTopPcs_layout (by omega) hfit hD hρ hpc hj
    have hroot : rowsAt pc.R₀ pc.j = compactTopRows (Mult.Sizes.d N) R
        (address-(o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))) :=
      hok.hR.symm
    have hh := compactLayerReady_canonical (Ka := Ka) (D := 1) hok.hu hok.hR₀ hG hGK hrecord rfl
      (j := j) (a := pc.a₀-o) (layout := layout)
    apply hh
    intro i hi a left right layout x y hxy _
    apply hp D o address R rBits r w (rowsAt pc.R₀ i) a (bits pc.u i) ρ left right
      hD hfit hG hGK hrecord (rowsAt_pos hok.hR₀ i) layout hR hRbits haddress
    · rw [←hroot]
      apply compactPiece_descendant_rows
      omega
    · exact hprecision
    · exact hr
    · exact hw

/-- **The rounded top at runtime.** For actual runtime parameters, the reserved rounded top
with guard `gb`, cut `s' ≤ s`, final shift `s - s'` and `k` shrinks, working width
width `w ≥ W + s + D`, `s = ⌈D/2⌉ + q + gb + E_R`, leaves on `io` the stream of
`topRSW … gb s (k 2^s') Z`. The array before the shifts must fit the working width (`hX`) and
every child level of every piece must truncate by fewer bits than the working width
(`hscale`). -/
theorem compactTopRuntimeR_eventually_exec (hQ : compactRuntimeStates ≤ Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ N : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
      (_hgate : ∀ g, Instr.gate g∈program ds →
        (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (D o a R rBits r W p ρ gb s' k w : ℕ)
      (h : CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D) (hD : D≤Mult.Sizes.d N)
      (hρ : ρ<Mult.Sizes.K N) (hR : 1≤R) (_hr : 1≤r) (_hW : p+2≤W)
      (_hRbits : R≤2^rBits)
      (ha : CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)*Mult.Sizes.K N≤a)
      (_hprecision : rBits+(o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a)+1≤Mult.Sizes.p N)
      (_hrun : Mult.Sizes.r N≤r) (_hwrun : Mult.Sizes.p N≤W),
    let d := Mult.Sizes.d N
    let g := CompactReservationGrowth.guard N
    let K := Mult.Sizes.K N
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
      (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖≤2^p)
      (_hX : ∀ z, TopFitsZ w (topPreRW ds w a low (topTop aT ρ K q (n+a) hfitT)
        (compactTopRows_bounds (by omega) hR ha).1 Ps gb Z z))
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hT : CompactTopRegs (compactHostBasisRest shape o r) S.R (n+a) r w K ρ)
      (_hI : CompactTopIn (BReg := CompactHostBReg) S.R (topCfgR W s a R R₂ q aT K o D gb s' k)
        (topPcRec K pcs))
      (_hio : S.R (reg (BReg := CompactHostBReg) .io)=encZ (prime+Ka) W Z),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCostR W w s n a R r K ρ q aT o D R₂ gb s' k pcs
        (compactTopCallCostR ds shape 1 (n+a) o r w ρ ⟨0,q,R,aT⟩)
        (compactTopCallCostR ds shape 1 n o r w ρ) ∧
      Exec (compactPlacedLayerTableR hQ ds) (compactTopProgR (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ
                (prime+Ka) W (topRSW ds w a low (topTop aT ρ K q (n+a) hfitT)
                  (compactTopRows_bounds (by omega) hR ha).1 Ps gb s (k*2^s') Z))}) := by
  filter_upwards [compactPiece_eventually_readyR, compactCaller_runtime_eventually_shape] with N hp hshape
  intro ds hgate D o a R rBits r W p ρ gb s' k w h hD hρ hR hr hW hRbits ha hprecision hrun hwrun
  dsimp only
  intro hww hs' hscale Z hZ hX v S hL hT hI hio
  have hgeom := compactTopKernel_geometry (o := o) h hρ ha
  have haddress : o+Mult.Sizes.K N*D≤
      o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a := by
    rw [←compactTopKernel_end h o]
    exact hgeom.2
  set sR := (D+1)/2+compactTopKernelCount (Mult.Sizes.d N)
    (CompactReservationGrowth.guard N) (Mult.Sizes.K N)+
    (gb+(backChunks (Mult.Sizes.d N) (CompactReservationGrowth.guard N) (Mult.Sizes.K N)+
    synE (gateCount (program ds)) 0
      (compactReservationActive (Mult.Sizes.d N) (CompactReservationGrowth.guard N) (Mult.Sizes.K N) D)
      (compactReservationActive (Mult.Sizes.d N) (CompactReservationGrowth.guard N) (Mult.Sizes.K N) D)))
    with hsR
  set working := w with hworking
  obtain ⟨hG,hGK,hrecord⟩ := hshape D o r working hD h hrun (hwrun.trans (by omega))
  refine compactTopActualR_exec (Q := Q) (Ka := Ka) (U := U)
    (shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) D (2^o*(3*(r*working))))
    (d := Mult.Sizes.d N) (g := CompactReservationGrowth.guard N)
    (D := D) (oS := o) (o := o) (a := a) (R := R) (r := r) (W := W) (ρ := ρ) (packD := 1)
    (w' := working) (gb := gb) (s := sR) (s' := s') (k := k)
    hQ ds hA hA9 hNW hgate h hD hρ hR hr (by omega) (by omega) (by omega) (by omega) hs'
    (le_refl o) ha hG hGK hrecord hgeom.1 hgeom.2 rfl
    (fun pc hpc => compactTopPcs_offset hpc) hscale ?_ Z (compactTopInput_fits Z hW hZ) hX
    v S hL hT hI hio
  · intro pc hpc
    have hc : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) D (2^o*(3*(r*working)))).chunk=Mult.Sizes.K N := rfl
    rw [hc] at hpc
    have hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W) (oS := o)
    have hh := hp D o
      (o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a)
      R rBits r working ρ Ka hD h hρ hR hRbits haddress hprecision hrun
      (hwrun.trans (by omega)) hG hGK hrecord pc
    simp only [Nat.add_sub_cancel_left] at hh
    simpa only [hc,Nat.add_sub_cancel_left, Nat.add_sub_cancel_right] using
      hh hpc (hpcs pc hpc).okR

end
end IntegerMultBounds.MathlibTM2.Fast
