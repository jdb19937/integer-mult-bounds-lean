module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcStages
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcPieces
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcKernel

/-! Complete actual top runner over arbitrary basis banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}

/-- **The host machine of the simultaneous layer**, one fixed program: widening (`compactTopWidenS`),
the phase (`compactTopPhaseS`), the top kernels (`compactTopKerS`), the pieces with the top bits as rows
(`compactTopBlockS`), the phase, the unit (`compactTopUnitS`) and the truncating shift (`compactTopShiftS`). All sizes
come from the registers. -/
noncomputable def compactTopProg (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq compactTopWidenS (.seq compactTopPhaseS (.seq (compactTopKerS cp) (.seq (compactTopBlockS cp) (.seq compactTopPhaseS
    (.seq compactTopUnitS compactTopShiftS)))))

/-- The step bound of `compactTopProg`: the sum of the stage bounds. -/
def compactTopCost
    (w w' s n a R r K ρ q aT oS D R₂ : ℕ) (pcs : List TopPc) (kc : ℕ) (cc : TopPc → ℕ) : ℕ :=
  compactTopWidenSCost (topCfg w s a R R₂ q aT K oS D) R (n + a) r w w' +
    compactTopPhaseSCost (topCfg w s a R R₂ q aT K oS D) (n + a) R r w' K ρ oS D +
    compactTopKerSCost (topCfg w s a R R₂ q aT K oS D) K R q aT kc +
    compactTopBlockCost (topCfg w s a R R₂ q aT K oS D) K n a r w' R R₂ cc pcs +
    compactTopPhaseSCost (topCfg w s a R R₂ q aT K oS D) (n + a) R r w' K ρ oS D +
    compactTopUnitSCost (topCfg w s a R R₂ q aT K oS D) R (n + a) r w' D +
    compactTopShiftSCost (topCfg w s a R R₂ q aT K oS D) R (n + a) r w' s w

/-- **The host machine of the simultaneous layer** (`compactTopProg`). The configuration is read from
the registers: `park` holds the record `topCfg w s a R R₂ q aT K oS D` (on top of anything),
`ph .arr` the piece record `topPcRec K pcs`, `lf (.k .arr)`, `st`, `cs` are empty, and
`CompactTopRegs bc S.R (n + a) r w' K ρ` holds (the per-call parameters empty, `n`, `w`, `rw`, `K`, `ρ`
holding `n + a`, `w'`, `r w'`, `K`, `ρ`, every register at rest). With every left stack empty
and `io` holding the `w`-bit stream of `Z` (coefficients fitting `w` signed bits), the machine
ends with `io` holding the `w`-bit stream of `topZ ds a low top hR₂ Ps s Z`, `top` the bits
`aT + ρ + K i` (`i < q`) and `Ps` the pieces of `pcs`, provided the selected bits are the `D`
distinct bits `ρ + oS + K i`, the array before the shift fits `w'` signed bits and
`s + w ≤ w'`. Every other register and `user` end as they started, within `compactTopCost` steps. -/
theorem compactTopProg_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (kc : ℕ) (cc : TopPc → ℕ)
    (hA : 21 ≤ A)
    {w w' s n a R r K ρ q aT oS D R₂ : ℕ} (low : List (Fin n)) (pcs : List TopPc)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hsw : s + w ≤ w') (hρ : ρ < K)
    (hfitT : ∀ i < q, aT + ρ + K * i < n + a)
    (hR₂ : R * 2 ^ a ≤ R₂) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w' R₂)
    (hkernel : 1≤q → CallSpec body cp bc ds R 0 q K ρ aT (K*q) (n+a) r w'
      (by simpa only [bits] using hfitT) kc)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpec body cp bc ds pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w' hfit (cc pc))
    (hselm : ∀ t : Fin (n + a), t ∈ topSel a low (topTop aT ρ K q (n + a) hfitT) ↔
      ∃ i < D, (t : ℕ) = ρ + oS + K * i)
    (hsel : (topSel a low (topTop aT ρ K q (n + a) hfitT)).Nodup)
    (hD : (topSel a low (topTop aT ρ K q (n + a) hfitT)).length = D)
    (Z : ZArr (Fin R × Fin r) (n + a)) (hZ : ∀ p, TopFitsZ w (Z p))
    (hX : ∀ p, TopFitsZ w' (topPre ds a low (topTop aT ρ K q (n + a) hfitT) hR₂
      (topPieces hρ pcs hpcs) Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R (n + a) r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R (topCfg w s a R R₂ q aT K oS D) (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopCost w w' s n a R r K ρ q aT oS D R₂ pcs kc cc ∧
      Exec body (compactTopProg cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (topZ ds a low
            (topTop aT ρ K q (n + a) hfitT) hR₂ (topPieces hρ pcs hpcs) s Z)) }) := by
  set cfg := topCfg w s a R R₂ q aT K oS D with hcfg
  set top := topTop aT ρ K q (n + a) hfitT with htop
  set sel := topSel a low top with hseldef
  set Ps := topPieces hρ pcs hpcs with hPs
  have hw' : 1 ≤ w' := by omega
  have hK : 1 ≤ K := by omega
  have hA5 : 5 ≤ A := by omega
  have hmask : topMaskOf (n + a) ρ K oS D = topSelMask sel := topMaskOf_eq hK sel hselm
  have hT' : ∀ X, CompactTopRegs bc (Function.update S.R (reg .io) X) (n + a) r w' K ρ :=
    fun X => hT.update_io X
  have hI' : ∀ X, CompactTopIn (BReg := BReg) (Function.update S.R (reg .io) X) cfg (topPcRec K pcs) :=
    fun X => hI.update_io X
  -- the arrays
  set Z₁ := sZ sel Z with hZ₁
  set Z₂ := k2s top Z₁ with hZ₂
  set G := unpadRows hR₂ (piecesZ ds Ps (padRows R₂ (toRows a Z₂))) with hG
  set Z₃ := ofRows a G with hZ₃
  set Z₄ := sZ sel Z₃ with hZ₄
  set Z₅ := topPre ds a low top hR₂ Ps Z with hZ₅
  have hZ₅e : Z₅ = fun p => unitD D * Z₄ p := by rw [hZ₅, ← hD]; rfl
  -- 1. widen
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopWidenS_exec body (cfg := cfg) (by simp [hcfg, topCfg]) hw
    (by omega : w ≤ w') Z hZ v S hT hI hio
  -- 2. phase
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopPhaseS_exec body hA5 (cfg := cfg) (R := R) (oS := oS)
    (D := D)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hr hw' hK Z v₁
    { S with R := Function.update S.R (reg .io) (encZ A w' Z) } (hT' _) (hI' _)
    (by simp)
  rw [hmask, topPhase_sZ sel hsel, topIo] at e₂
  -- 3. the top kernels
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := compactTopKerS_exec body cp bc ds kc (cfg := cfg)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg])
    (by simp [hcfg, topCfg]) hfitT hkernel Z₁ v₂
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₁) } hL (hT' _) (hI' _)
    (by simp)
  rw [topIo] at e₃
  -- 4. the pieces with the top bits as rows
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := compactTopBlockS_exec body cp bc ds cc (cfg := cfg)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hρ hR₂ pcs
    hpcs hcalls (toRows a Z₂) v₃
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₂) } hL (hT' _) (hI' _)
    (by simp [topEnc_toRows])
  rw [topIo, ← hG, ← topEnc_ofRows a G, ← hZ₃] at e₄
  -- 5. phase
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := compactTopPhaseS_exec body hA5 (cfg := cfg) (R := R) (oS := oS)
    (D := D)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hr hw' hK Z₃ v₄
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₃) } (hT' _) (hI' _)
    (by simp)
  rw [hmask, topPhase_sZ sel hsel, topIo] at e₅
  -- 6. the unit
  obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := compactTopUnitS_exec body (by omega) (cfg := cfg) (D := D)
    (by simp [hcfg, topCfg]) hw' Z₄ v₅
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₄) } (hT' _) (hI' _)
    (by simp)
  rw [topIo, ← hZ₅e] at e₆
  -- 7. the truncating shift
  obtain ⟨v₇, c₇, hu₇, hc₇, e₇⟩ := compactTopShiftS_exec body (by omega) (cfg := cfg)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hw' hsw Z₅ hX v₆
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₅) } (hT' _) (hI' _)
    (by simp)
  rw [topIo] at e₇
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      e₇)))))) rfl (by rw [topZ_eq_pre])⟩
  unfold compactTopCost
  rw [← hcfg]
  omega

/-- **The layer.** `compactTopProg_exec` with `topZ_correct`: for injective pieces covering `low` and
the shift `s = ⌈D/2⌉ + |top| + Σ exp`, the machine leaves on `io` the stream of the
componentwise truncation toward zero of the normalized butterflies `Hl` on the selected bits. -/
theorem compactTopProg_exec_Hl (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (kc : ℕ) (cc : TopPc → ℕ)
    (hd : ComplexPhaseBudget.Realizes ds)
    (hA : 21 ≤ A)
    {w w' s n a R r K ρ q aT oS D R₂ : ℕ} (low : List (Fin n)) (pcs : List TopPc)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hsw : s + w ≤ w') (hρ : ρ < K)
    (hfitT : ∀ i < q, aT + ρ + K * i < n + a)
    (hR₂ : R * 2 ^ a ≤ R₂) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w' R₂)
    (hkernel : 1≤q → CallSpec body cp bc ds R 0 q K ρ aT (K*q) (n+a) r w'
      (by simpa only [bits] using hfitT) kc)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpec body cp bc ds pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w' hfit (cc pc))
    (hinj : ∀ P ∈ topPieces hρ pcs hpcs, Function.Injective P.e)
    (hcover : ((topPieces hρ pcs hpcs).flatMap Piece.bitsList).Perm low)
    (hselm : ∀ t : Fin (n + a), t ∈ topSel a low (topTop aT ρ K q (n + a) hfitT) ↔
      ∃ i < D, (t : ℕ) = ρ + oS + K * i)
    (hsel : (topSel a low (topTop aT ρ K q (n + a) hfitT)).Nodup)
    (hD : (topSel a low (topTop aT ρ K q (n + a) hfitT)).length = D)
    (hs : s = (low.length + q + 1) / 2 + q + ((topPieces hρ pcs hpcs).map (Piece.exp ds)).sum)
    (Z : ZArr (Fin R × Fin r) (n + a)) (hZ : ∀ p, TopFitsZ w (Z p))
    (hX : ∀ p, TopFitsZ w' (topPre ds a low (topTop aT ρ K q (n + a) hfitT) hR₂
      (topPieces hρ pcs hpcs) Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R (n + a) r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R (topCfg w s a R R₂ q aT K oS D) (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopCost w w' s n a R r K ρ q aT oS D R₂ pcs kc cc ∧
      Exec body (compactTopProg cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p =>
            (⟨truncR (Hl _ (topSel a low (topTop aT ρ K q (n + a) hfitT)) (toC Z) p).re,
              truncR (Hl _ (topSel a low (topTop aT ρ K q (n + a) hfitT)) (toC Z) p).im⟩ :
              GaussianInt))) }) := by
  obtain ⟨v', c, hu, hc, he⟩ := compactTopProg_exec body cp bc ds kc cc hA low pcs hr hw hsw hρ
    hfitT hR₂ hpcs hkernel hcalls hselm hsel hD Z hZ hX v S hL hT hI hio
  refine ⟨v', c, hu, hc, Exec.cast he rfl ?_⟩
  congr 4
  funext p
  have hq : (topTop aT ρ K q (n + a) hfitT).length = q := by simp [topTop]
  exact topZ_correct ds hd a low _ hR₂ _ hinj hcover hsel s (by rw [hq]; exact hs) Z p

end
end IntegerMultBounds.MathlibTM2.LayerMachine
