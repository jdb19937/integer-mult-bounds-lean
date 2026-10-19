module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows
import IntegerMultBounds.MathlibTM2.Cost.CompactLayerReady
import IntegerMultBounds.MathlibTM2.Fast.CompactPieceGeometry
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
import IntegerMultBounds.MathlibTM2.Cost.CompactSlotPacking
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
public import IntegerMultBounds.MathlibTM2.Cost.CompactLayer
import IntegerMultBounds.MathlibTM2.Fast.SynRecB
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Runtime sizes pay every descendant packing obligation of an actual reserved
piece. No execution or numerical cost oracle is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
open Filter IntegerMultBounds.Networks
noncomputable section

/-- Every recursive descendant has at most its root's row stock. -/
theorem compactPiece_descendant_rows {R₀ i j : ℕ} (hij : i≤j) :
    rowsAt R₀ i≤rowsAt R₀ j := by
  rw [rowsAt_eq,rowsAt_eq]
  exact Nat.mul_le_mul_right R₀ (Nat.pow_le_pow_right NW_pos hij)

/-- Uniform packing for any local layout and any descendant stock bounded by the
actual padded top array. Exact native address width removes high spectators. -/
theorem compactPiece_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (D o address R rBits r w rows a k ρ left right : ℕ)
      (_hD : D≤Mult.Sizes.d N)
      (_hfit : CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D)
      (hG : 1≤(compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D (2^o*(3*(r*w)))).guard)
      (hGK : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D (2^o*(3*(r*w)))).guard+1≤(Mult.Sizes.K N))
      (hrecord : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D (2^o*(3*(r*w)))).bits+1≤2^o*(3*(r*w)))
      (hrows : 0<rows)
      (layout : CompactRecursiveLayout
        (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
          (Mult.Sizes.K N) D (2^o*(3*(r*w))))
        (Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))
        a k ρ left right),
      0<R → R≤2^rBits → o+Mult.Sizes.K N*D≤address →
      rows≤compactTopRows (Mult.Sizes.d N) R
        (address-(o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))) →
      rBits+address+1≤Mult.Sizes.p N → Mult.Sizes.r N≤r → Mult.Sizes.p N≤w →
      CompactLayoutPacked layout rows 1 := by
  filter_upwards [compactCaller_slot_eventually_packed,
    compactCaller_runtime_eventually_guard] with N hp hguard
  intro D o address R rBits r w rows a k ρ left right hD hfit hG hGK hrecord hrows
    layout hR hRbits haddress hstock hprecision hr hw
  have hK : 0<Mult.Sizes.K N := by omega
  show CompactSlotPacked _ k (2^(_-_)*rows) 1
  rw [compactCaller_selected_native_rows hK hfit]
  apply hp D o r w (rBits+(address-(o+Mult.Sizes.K N*D))+1) k rows hD hfit
  · exact hstock.trans (by simpa using compactCaller_selected_rows_le hK hR hfit haddress hRbits 0)
  · exact compactCaller_selected_extra_le hprecision
  · exact hr
  · exact hw
  · exact layout.widthFits

/-- Every actual serialized piece is ready for the concrete recursive program
at the canonical basis budget, from original address/row precision alone. -/
theorem compactPiece_eventually_ready : ∀ᶠ N : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (D o address R rBits r w ρ Ka : ℕ),
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
      (hok : pc.Ok ds K (o+n) w R₂),
    CompactLayerReady shape n o pc.u ρ pc.R₀ r w Ka 1 hok.hR₀ hG hGK hrecord
      (compactLayerBasisBudget (nT CompactBReg) 1 shape pc.u pc.R₀ n) pc.j (pc.a₀-o) := by
  filter_upwards [compactPiece_eventually_packed] with N hp
  intro ds D o address R rBits r w ρ Ka
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
    intro i hi a left right layout
    apply hp D o address R rBits r w (rowsAt pc.R₀ i) a (bits pc.u i) ρ left right
      hD hfit hG hGK hrecord (rowsAt_pos hok.hR₀ i) layout hR hRbits haddress
    · rw [←hroot]
      apply compactPiece_descendant_rows
      omega
    · exact hprecision
    · exact hr
    · exact hw

end
end IntegerMultBounds.MathlibTM2.Cost
