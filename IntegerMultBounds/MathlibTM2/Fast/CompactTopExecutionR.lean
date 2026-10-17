module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopReadyR
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlacedR

/-! The reserved rounded top transform running the placed rounded layer table: the rounded
twins of `compactTopActual_callSpec` and `compactTopActual_exec_Hl`. The output is the rounded top
with a shrink, `topRSW`, as the tape computes it. -/
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

/-- The rounded layer cost in absolute top coordinates, with the canonical basis budget. -/
noncomputable def compactTopCallCostR (ds : ComplexFramedExecution.Directions)
    (shape : Shape) (packD n o r w ρ : ℕ) (pc : TopPc) : ℕ :=
  compactLayerCostR ds pc.u shape.chunk ρ pc.R₀ (n-o) o r w
    (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o)) pc.j (pc.a₀-o)

/-- Place the rounded recursive layer at absolute coordinates. -/
theorem compactTopActualR_callSpec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4)
    (hgate : ∀ g, Instr.gate g∈program ds →
      (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
    {shape : Shape} {n o r w ρ packD : ℕ} (pc : TopPc)
    (hr : 1≤r) (hw : 1≤w) (hu : 1≤pc.u) (hR : 1≤pc.R₀)
    (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
    (hrecord : shape.bits+1≤shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (hn : o≤n) (ha : o≤pc.a₀) (hsw : ∀ i<pc.j, scaleR pc.u ds i<w)
    (hready : CompactLayerReady shape (n-o) o pc.u ρ pc.R₀ r w Ka packD
      hR hG hGK hrecord
      (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o)) pc.j (pc.a₀-o))
    (hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+shape.chunk*i<n)
    (hfitL : pc.a₀+shape.chunk*bits pc.u pc.j≤n) :
    CallSpecF (compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds) (.call .layer)
      (compactHostBasisRest shape o r) pc.R₀ pc.j pc.u shape.chunk ρ pc.a₀
      (shape.chunk*bits pc.u pc.j) n r w
      (layerRW w pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ shape.chunk (bits pc.u pc.j) n hfit))
      (compactTopCallCostR ds shape packD n o r w ρ pc) := by
  obtain ⟨j, u, R₀, a₀⟩ := pc
  obtain ⟨N, rfl⟩ : ∃ N, n = o + N := ⟨n - o, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a₀ = o + a' := ⟨a₀ - o, by simp only at ha; omega⟩
  simp only [Nat.add_sub_cancel_left] at hready
  unfold compactTopCallCostR
  simp only [Nat.add_sub_cancel_left]
  exact compactPlacedLayerR_callSpec (U := U) hQ ds hA hA9 hNW hgate hr hw hu hR hG hGK
    hrecord hpayload (compactLayerBasisBudget (nT CompactBReg) packD shape u R₀ N)
    j hsw a' hready hfit hfitL

/-- **The rounded reserved transform** on the union host, using the placed rounded layer
table and actual padded rows. The working width `w'`, the guard `gb`, the cut `s'`, the final
shift `s₂` and the shrink count `k` are free; the machine leaves on `io` the stream of
`topRSW … gb (s' + s₂) (k 2^s') Z`. -/
theorem compactTopActualR_exec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4)
    (hgate : ∀ g, Instr.gate g∈program ds →
      (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
    {shape : Shape} {d g D oS o a R r W ρ packD w' gb s' s₂ k : ℕ}
    (h : CompactReservationFits d g shape.chunk D) (hD : D≤d)
    (hρ : ρ<shape.chunk) (hR : 1≤R) (hr : 1≤r) (hW : 1≤W)
    (hsw : s₂+W≤w') (hgb : gb≤w') (hs' : s'<w')
    (ho : o≤oS) (ha : CompactGlobalRowPadding.rowAxes NW m d*shape.chunk≤a)
    (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
    (hrecord : shape.bits+1≤shape.payload) :
    let K := shape.chunk
    let n := oS+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D oS
    let R₂ := compactTopRows d R a
    let pcs := compactTopPcs d g K D oS R₂
    let hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    ∀ (hfitT : ∀ i<q,aT+ρ+K*i<n+a)
      (_hTL : aT+K*q≤n+a)
      (_hpayload : shape.payload=2^o*(3*(r*w')))
      (_hbase : ∀ pc∈pcs,o≤pc.a₀)
      (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<w')
      (_hready : ∀ pc (hpc : pc∈pcs), CompactLayerReady shape (n-o) o pc.u ρ pc.R₀ r w' Ka packD
        (hpcsR pc hpc).hR₀ hG hGK hrecord
        (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o)) pc.j (pc.a₀-o))
      (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, TopFitsZ W (Z z))
      (_hX : ∀ z, TopFitsZ w' (topPreRW ds w' a low (topTop aT ρ K q (n+a) hfitT) (by
        exact (compactTopRows_bounds (by omega) hR ha).1) Ps gb Z z))
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hT : CompactTopRegs (compactHostBasisRest shape o r) S.R (n+a) r w' K ρ)
      (_hI : CompactTopIn (BReg := CompactHostBReg) S.R (topCfgR W s₂ a R R₂ q aT K oS D gb s' k)
        (topPcRec K pcs))
      (_hio : S.R (reg (BReg := CompactHostBReg) .io)=encZ (prime+Ka) W Z),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCostR W w' s₂ n a R r K ρ q aT oS D R₂ gb s' k pcs
        (compactTopCallCostR ds shape packD (n+a) o r w' ρ ⟨0,q,R,aT⟩)
        (compactTopCallCostR ds shape packD n o r w' ρ) ∧
      Exec (compactPlacedLayerTableR hQ ds) (compactTopProgR (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ
                (prime+Ka) W (topRSW ds w' a low (topTop aT ρ K q (n+a) hfitT)
                  (compactTopRows_bounds (by omega) hR ha).1 Ps gb (s'+s₂) (k*2^s') Z))}) := by
  dsimp only
  intro hfitT hTL hpayload hbase hscale hready Z hZ hX v S hL hT hI hio
  let K := shape.chunk
  let n := oS+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D oS
  let R₂ := compactTopRows d R a
  let pcs := compactTopPcs d g K D oS R₂
  have hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W) (oS := oS)
  have hn : o≤n := by dsimp [n]; omega
  have hw' : 1≤w' := by omega
  have hcoverage := compactTopSelection_vals ds h hρ hpcs hfitT
  apply compactTopProgR_exec_RS (compactPlacedLayerTableR hQ ds) (.call .layer)
    (compactHostBasisRest shape o r) ds _ _ hA _ pcs hr hW hsw hgb hs' hρ hfitT
    (compactTopRows_bounds (by omega) hR ha).1 (fun pc hpc => (hpcs pc hpc).okR)
  · intro hq
    exact (compactTopActualR_callSpec hQ ds (by omega) hA9 hNW hgate ⟨0,q,R,aT⟩ hr hw' hq hR
      hG hGK hrecord hpayload (by omega)
      (by dsimp [aT,compactTopKernelOffset]; omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
      trivial (by simpa only [bits] using hfitT) (by simpa only [bits] using hTL)).callSpec_zero _
  · intro pc hpc hfit
    exact compactTopActualR_callSpec hQ ds (by omega) hA9 hNW hgate pc hr hw'
      (hpcs pc hpc).hu (hpcs pc hpc).hR₀ hG hGK hrecord hpayload hn (hbase pc hpc)
      (hscale pc hpc) (hready pc hpc) hfit (hpcs pc hpc).hfit
  · exact compactSelection_mem hcoverage
  · exact compactSelection_nodup (by omega) hcoverage
  · exact compactSelection_length hcoverage
  · exact hZ
  · exact hX
  · exact hL
  · exact hT
  · exact hI
  · exact hio

end
end IntegerMultBounds.MathlibTM2.Fast
