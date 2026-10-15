module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformReadiness
public import IntegerMultBounds.MathlibTM2.Cost.CompactPiecePacking
public import IntegerMultBounds.MathlibTM2.Cost.CompactLayerReady
public import IntegerMultBounds.MathlibTM2.Fast.CompactPieceGeometry

/-! Runtime sizes pay every descendant packing obligation of an actual reserved
piece. No execution or numerical cost oracle is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
open Filter IntegerMultBounds.Networks
noncomputable section

/-- Uniform packing for any local layout and any descendant stock bounded by the
actual padded top array. Exact native address width removes high spectators. -/
theorem compactPiece_uniform_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (K D o address R rBits r w rows a k ρ left right : ℕ)
      (_hlo : Mult.Sizes.K N≤K) (_hhi : K≤Mult.Sizes.d N)
      (_hD : D≤Mult.Sizes.d N)
      (_hfit : CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D)
      (hG : 1≤(compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D (2^o*(3*(r*w)))).guard)
      (hGK : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D (2^o*(3*(r*w)))).guard+1≤K)
      (hrecord : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D (2^o*(3*(r*w)))).bits+1≤2^o*(3*(r*w)))
      (hrows : 0<rows)
      (layout : CompactRecursiveLayout
        (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
          K D (2^o*(3*(r*w))))
        (K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))
        a k ρ left right),
      0<R → R≤2^rBits → o+K*D≤address →
      rows≤compactTopRows (Mult.Sizes.d N) R
        (address-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))) →
      rBits+address+1≤Mult.Sizes.p N → Mult.Sizes.r N≤r → Mult.Sizes.p N≤w →
      ∀ x y (hxy : x≠y), ActivePrefixStageRuntimeData.Packed
        (compactSlotComputedInputs layout x y hxy rows hG hGK hrows hrecord) 1 := by
  filter_upwards [compactCaller_uniform_eventually_packed,
    compactCaller_runtime_eventually_guard] with N hp hguard
  intro K D o address R rBits r w rows a k ρ left right hlo hhi hD hfit hG hGK hrecord hrows
    layout hR hRbits haddress hstock hprecision hr hw x y hxy
  have hK : 0<K := by omega
  apply hp K D o r w (rBits+(address-(o+K*D))+1) _ hlo hhi hD hfit
  · dsimp only [compactSlotComputedInputs,compactRecursiveInputs]
    rw [compactCaller_selected_native_rows hK hfit]
    exact hstock.trans (by simpa using compactCaller_selected_rows_le hK hR hfit haddress hRbits 0)
  · exact compactCaller_selected_extra_le hprecision
  · exact hr
  · exact hw

/-- Every actual serialized piece is ready for the concrete recursive program
at the canonical basis budget, from original address/row precision alone. -/
theorem compactPiece_uniform_eventually_ready : ∀ᶠ N : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (K D o address R rBits r w ρ Ka : ℕ),
    let d := Mult.Sizes.d N
    let g := CompactReservationGrowth.guard N
    let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
    let n := K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let R₂ := compactTopRows d R (address-(o+n))
    ∀ (_hlo : Mult.Sizes.K N≤K) (_hhi : K≤d) (_hD : D≤d) (_hfit : CompactReservationFits d g K D)
      (_hρ : ρ<K) (_hR : 0<R) (_hRbits : R≤2^rBits) (_haddress : o+K*D≤address)
      (_hprecision : rBits+address+1≤Mult.Sizes.p N)
      (_hr : Mult.Sizes.r N≤r) (_hw : Mult.Sizes.p N≤w)
      (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
      (hrecord : shape.bits+1≤shape.payload)
      (pc : TopPc) (_hpc : pc∈compactTopPcs d g K D o R₂)
      (hok : pc.Ok ds K (o+n) w R₂),
    CompactLayerReady shape n o pc.u ρ pc.R₀ r w Ka 1 hok.hR₀ hG hGK hrecord
      (compactLayerBasisBudget (nT CompactBReg) 1 shape pc.u pc.R₀ n) pc.j (pc.a₀-o) := by
  filter_upwards [compactPiece_uniform_eventually_packed] with N hp
  intro ds K D o address R rBits r w ρ Ka
  dsimp only
  intro hlo hhi hD hfit hρ hR hRbits haddress hprecision hr hw hG hGK hrecord pc hpc hok
  cases hj : pc.j with
  | zero => simp only [CompactLayerReady]
  | succ j =>
    obtain ⟨left,right,layout⟩ := compactTopPcs_layout (by omega) hfit hD hρ hpc hj
    have hroot : rowsAt pc.R₀ pc.j = compactTopRows (Mult.Sizes.d N) R
        (address-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)))) :=
      hok.hR.symm
    have hh := compactLayerReady_canonical (Ka := Ka) (D := 1) hok.hu hok.hR₀ hG hGK hrecord rfl
      (j := j) (a := pc.a₀-o) (layout := layout)
    apply hh
    intro i hi a left right layout x y hxy _
    apply hp K D o address R rBits r w (rowsAt pc.R₀ i) a (bits pc.u i) ρ left right
      hlo hhi hD hfit hG hGK hrecord (rowsAt_pos hok.hR₀ i) layout hR hRbits haddress
    · rw [←hroot]
      apply compactPiece_descendant_rows
      omega
    · exact hprecision
    · exact hr
    · exact hw

end
end IntegerMultBounds.MathlibTM2.Cost
