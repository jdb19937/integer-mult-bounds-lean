module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProc
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
import IntegerMultBounds.MathlibTM2.Fast.CompactTopPrecision
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopReady
public import IntegerMultBounds.MathlibTM2.Cost.CompactLayer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

/-- The real layer cost in absolute top coordinates, with the canonical basis budget. -/
noncomputable def compactTopCallCost (ds : ComplexFramedExecution.Directions)
    (shape : Shape) (packD n o r w ρ : ℕ) (pc : TopPc) : ℕ :=
  compactLayerCost ds pc.u shape.chunk ρ pc.R₀ (n-o) o r w
    (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o)) pc.j (pc.a₀-o)

/-- Place the recursive layer at absolute coordinates without adding an execution premise. -/
theorem compactTopActual_callSpec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4)
    (hgate : ∀ g, Instr.gate g∈program ds →
      (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
    {shape : Shape} {n o r w ρ packD : ℕ} (pc : TopPc)
    (hr : 1≤r) (hw : 1≤w) (hu : 1≤pc.u) (hR : 1≤pc.R₀)
    (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
    (hrecord : shape.bits+1≤shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (hn : o≤n) (ha : o≤pc.a₀) (hTw : ∀ i<pc.j,expZ pc.u ds i≤w)
    (hready : CompactLayerReady shape (n-o) o pc.u ρ pc.R₀ r w Ka packD
      hR hG hGK hrecord
      (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o)) pc.j (pc.a₀-o))
    (hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+shape.chunk*i<n)
    (hfitL : pc.a₀+shape.chunk*bits pc.u pc.j≤n) :
    CallSpec (compactPlacedLayerTable (Ka := Ka) (U := U) hQ ds) (.call .layer)
      (compactHostBasisRest shape o r) ds pc.R₀ pc.j pc.u shape.chunk ρ pc.a₀
      (shape.chunk*bits pc.u pc.j) n r w hfit
      (compactTopCallCost ds shape packD n o r w ρ pc) := by
  have hn' : o+(n-o)=n := Nat.add_sub_of_le hn
  have ha' : o+(pc.a₀-o)=pc.a₀ := Nat.add_sub_of_le ha
  simpa only [hn',ha',compactTopCallCost] using
    (compactPlacedLayer_callSpec (U := U) hQ ds hA hA9 hNW hgate hr hw hu hR hG hGK
      hrecord hpayload (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o))
      pc.j hTw (pc.a₀-o) hready
      (by simpa only [hn',ha'] using hfit) (by simpa only [hn',ha'] using hfitL))

/-- The full reserved transform on the union host, using the concrete recursive
layer table, actual padded rows and computed working precision. -/
theorem compactTopActual_exec_Hl (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4)
    (hgate : ∀ g, Instr.gate g∈program ds →
      (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
    {shape : Shape} {d g D oS o a R r W p ρ packD : ℕ}
    (h : CompactReservationFits d g shape.chunk D) (hD : D≤d)
    (hρ : ρ<shape.chunk) (hR : 1≤R) (hr : 1≤r) (hW : p+2≤W)
    (ho : o≤oS) (ha : CompactGlobalRowPadding.rowAxes NW m d*shape.chunk≤a)
    (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
    (hrecord : shape.bits+1≤shape.payload) :
    let K := shape.chunk
    let n := oS+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D oS
    let R₂ := compactTopRows d R a
    let s := (D+1)/2+q+(backChunks d g K+
      synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let w := W+s+D
    let pcs := compactTopPcs d g K D oS R₂
    let hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W)
    let Ps := topPieces hρ pcs hpcs
    let low := Ps.flatMap Piece.bitsList
    ∀ (hfitT : ∀ i<q,aT+ρ+K*i<n+a)
      (_hTL : aT+K*q≤n+a)
      (_hpayload : shape.payload=2^o*(3*(r*w)))
      (_hbase : ∀ pc∈pcs,o≤pc.a₀)
      (_hready : ∀ pc (hpc : pc∈pcs), CompactLayerReady shape (n-o) o pc.u ρ pc.R₀ r w Ka packD
        (hpcs pc hpc).hR₀ hG hGK hrecord
        (compactLayerBasisBudget (nT CompactBReg) packD shape pc.u pc.R₀ (n-o)) pc.j (pc.a₀-o))
      (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖≤2^p)
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hT : CompactTopRegs (compactHostBasisRest shape o r) S.R (n+a) r w K ρ)
      (_hI : CompactTopIn (BReg := CompactHostBReg) S.R (topCfg W s a R R₂ q aT K oS D)
        (topPcRec K pcs))
      (_hio : S.R (reg (BReg := CompactHostBReg) .io)=encZ (prime+Ka) W Z),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCost W w s n a R r K ρ q aT oS D R₂ pcs
        (compactTopCallCost ds shape packD (n+a) o r w ρ ⟨0,q,R,aT⟩)
        (compactTopCallCost ds shape packD n o r w ρ) ∧
      Exec (compactPlacedLayerTable hQ ds) (compactTopProg (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ (prime+Ka) W
          (fun z => (⟨truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).re,
            truncR (Hl _ (topSel a low (topTop aT ρ K q (n+a) hfitT)) (toC Z) z).im⟩ : GaussianInt)))}) := by
  dsimp only
  intro hfitT hTL hpayload hbase hready Z hZ v S hL hT hI hio
  let K := shape.chunk
  let n := oS+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D oS
  let R₂ := compactTopRows d R a
  let s := (D+1)/2+q+(backChunks d g K+
    synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive d g K D) (compactReservationActive d g K D))
  let w := W+s+D
  let pcs := compactTopPcs d g K D oS R₂
  have hpcs : ∀ pc∈pcs,pc.Ok ds K n w R₂ := compactTop_working_pcs_ok ds (by omega) hR h hD ha
  have hn : o≤n := by dsimp [n]; omega
  have hw : 1≤w := by dsimp [w]; omega
  have hR₂ : R*2^a≤R₂ := (compactTopRows_bounds (by omega) hR ha).1
  have hcoverage := compactTopSelection_vals ds h hρ hpcs hfitT
  apply compactTopProg_exec_Hl (compactPlacedLayerTable hQ ds) (.call .layer)
    (compactHostBasisRest shape o r) ds _ _ hd hA _ pcs hr (by omega) (by dsimp [w,s,q,K]; omega)
    hρ hfitT hR₂ hpcs
  · intro hq
    exact compactTopActual_callSpec hQ ds (by omega) hA9 hNW hgate ⟨0,q,R,aT⟩ hr hw hq hR
      hG hGK hrecord hpayload (by omega)
      (by dsimp [aT,compactTopKernelOffset]; omega) (by simp) trivial
      hfitT (by simpa only [bits] using hTL)
  · intro pc hpc hfit
    exact compactTopActual_callSpec hQ ds (by omega) hA9 hNW hgate pc hr hw
      (hpcs pc hpc).hu (hpcs pc hpc).hR₀ hG hGK hrecord hpayload hn (hbase pc hpc)
      (hpcs pc hpc).hTw (hready pc hpc) hfit (hpcs pc hpc).hfit
  · exact compactTopPieces_injective ds hρ pcs hpcs
  · exact List.Perm.refl _
  · exact compactSelection_mem hcoverage
  · exact compactSelection_nodup (by omega) hcoverage
  · exact compactSelection_length hcoverage
  · exact compactTop_shift ds h hρ hpcs hfitT
  · exact compactTopInput_fits Z hW hZ
  · exact compactTopPre_fits ds hd h hρ hR₂ hW hfitT Z hZ hpcs
  · exact hL
  · exact hT
  · exact hI
  · exact hio

end
end IntegerMultBounds.MathlibTM2.Fast
