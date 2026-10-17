module
public import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadR
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerCombinedBudget
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerDivisorPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopReadyR

/-! The working width of a rounded round and the eventual absorption of its overhead at the
actual caller sizes. With no factor term the scale sum is `synE G 0 ≤ D(D+G)`, so the guard and
the working width are linear in `W` once `d^2 ≤ b`; no larger power of `d` enters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

/-- With no factor term every level scale is at most `D+G`. -/
theorem synE_zero_le (G D t : ℕ) : synE G 0 D t≤t*(D+G) := by
  unfold synE
  have h : ∀ j∈Finset.range t,
      (if synDg D j=0 then 0 else expSeq G 0 (synDg D j) j)≤D+G := by
    intro j _
    split_ifs
    · omega
    · cases j with
      | zero => have := synDg_le D 0; simp only [expSeq]; omega
      | succ j => simp only [expSeq]; omega
  have hs := Finset.sum_le_card_nsmul _ _ _ h
  simpa only [Finset.card_range,smul_eq_mul] using hs

theorem synE_zero_active_le (G d g K D : ℕ) :
    synE G 0 (compactReservationActive d g K D) (compactReservationActive d g K D)≤D*D+D*G := by
  have ha : compactReservationActive d g K D≤D :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have h := (synE_zero_le G _ _).trans (Nat.mul_le_mul ha (Nat.add_le_add_right ha G))
  rwa [Nat.mul_add] at h

/-- **The rounded working width** is linear in `W`: the guard fields are at most `4W` and the
working width at most `8W`. Only `d^2 ≤ b` is used. -/
theorem compactCallerR_eventually_width (G cG : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∀ K D W N l : ℕ,
    D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D →
    Mult.Sizes.p M≤W → N≤Mult.Sizes.p M → l≤Mult.Sizes.p M →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let q := compactTopKernelCount d g K
    let E := backChunks d g K+
      synE G 0 (compactReservationActive d g K D) (compactReservationActive d g K D)
    let gb := guardG cG N l D
    let s := (D+1)/2+q+(gb+E)
    let working := W+s+D+guardKc cG N l D+G+m+4
    gb+E≤4*W ∧ working≤8*W := by
  filter_upwards [Mult.Sizes.eventually_big,
    tendsto_atTop.1 Mult.Sizes.tendsto_d (cG+G+m+20)] with M hbig hlarge
  intro K D W N l hD hfit hW hN hl
  dsimp only
  have hdd : Mult.Sizes.d M^2≤Mult.Sizes.b M :=
    Mult.Sizes.pow_le_b_of (by norm_num [Mult.Sizes.powerCap]) hbig.one_le_d
  rw [pow_two] at hdd
  have hp : Mult.Sizes.p M=6*Mult.Sizes.b M := rfl
  have hax := compactReservation_axes hfit
  have hE := synE_zero_active_le G (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D
  have hDD : D*D≤Mult.Sizes.d M*Mult.Sizes.d M := Nat.mul_le_mul hD hD
  have hDG : D*G≤Mult.Sizes.d M*Mult.Sizes.d M := Nat.mul_le_mul hD (by omega)
  have hDc : (cG+1)*D≤Mult.Sizes.d M*Mult.Sizes.d M := Nat.mul_le_mul (by omega) hD
  have h20 : 20*Mult.Sizes.d M≤Mult.Sizes.d M*Mult.Sizes.d M := Nat.mul_le_mul_right _ (by omega)
  have hhalf := Nat.div_le_self (D+1) 2
  unfold guardG guardKc compactTopKernelCount
  omega

private theorem scalarFieldsR (N d g K D o W h b qrow f back active E working c p : ℕ)
    (hN : N≤p) (hd : d≤p) (hg : g≤p) (hK : K≤p) (hD : D≤d)
    (hfit : qrow+f+back≤D) (haddress : o+K*D≤N)
    (hactive : active=D-qrow-f-back) (hE : E≤4*W)
    (hwork : working≤8*W) (hW : W≤2^c*(p+1)) (hh : h≤p) (hb : b≤p) :
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerScalarBudget (c+3) p) := by
  have hB : 1≤compactCallerScalarBudget (c+3) p :=
    Nat.mul_pos (pow_pos (by decide : 0<2) _) (pow_pos (Nat.succ_pos p) _)
  have hp2 : p^2≤compactCallerScalarBudget (c+3) p :=
    (Nat.pow_le_pow_left (Nat.le_succ p) 2).trans
      (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0<2) _))
  have hp : p≤compactCallerScalarBudget (c+3) p := (Nat.le_self_pow (by decide : 2≠0) p).trans hp2
  have h8W : 8*W≤compactCallerScalarBudget (c+3) p := by
    calc
      8*W≤8*(2^c*(p+1)) := Nat.mul_le_mul_left _ hW
      _ = 2^(c+3)*(p+1) := by rw [pow_add]; ring
      _ ≤ 2^(c+3+2)*(p+1)^2 := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : c+3≤c+3+2))
        (Nat.le_self_pow (by decide : 2≠0) _)
  have hWB : W≤compactCallerScalarBudget (c+3) p := (by omega : W≤8*W).trans h8W
  have hDp : D≤p := hD.trans hd
  have hbackD : back≤D := by omega
  have hqD : qrow+f≤D := by omega
  have hbaD : back+active≤D := by omega
  have hoff : o+K*back≤p :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hbackD) o).trans (haddress.trans hN)
  have haT : o+K*(back+active)≤p :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hbaD) o).trans (haddress.trans hN)
  have hKq : K*(qrow+f)≤p := (Nat.mul_le_mul_left K hqD).trans (by omega)
  refine ⟨hB,hN.trans hp,hd.trans hp,hg.trans hp,hK.trans hp,hDp.trans hp,
    (by omega : o≤p).trans hp,hWB,?_,hh.trans hp,hb.trans hp,
    (by omega : qrow≤p).trans hp,(by omega : f≤p).trans hp,
    (by omega : back≤p).trans hp,(by omega : active≤p).trans hp,
    hoff.trans hp,(by omega : E≤8*W).trans h8W,hqD.trans (hDp.trans hp),haT.trans hp,
    hKq.trans hp,hwork.trans h8W⟩
  have hprod : d*g≤p^2 := by simpa only [pow_two] using Nat.mul_le_mul hd hg
  exact hprod.trans hp2

private theorem callerAddressGeometryR (N K D o qrow : ℕ)
    (hq : qrow≤D) (haddress : o+K*D≤N) :
    qrow*K≤N-(o+K*(D-qrow)) ∧ o+K*(D-qrow)≤N := by
  have he : K*(D-qrow)+qrow*K=K*D := by
    rw [Nat.mul_comm qrow K,←Nat.mul_add,Nat.sub_add_cancel hq]
  omega

/-- **The rounded round overhead at the actual caller sizes** is linear in the padded working
volume, with the two stash passes explicit. -/
theorem compactCallerR_eventually_roundOverhead
    (ds : ComplexFramedExecution.Directions) (cG c : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∀ N D o W r h b l ρ stash : ℕ,
    N≤Mult.Sizes.p M → D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) D →
    o+Mult.CompactSizes.K M*D≤N → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h≤Mult.Sizes.p M → b≤Mult.Sizes.p M → l≤Mult.Sizes.p M →
    Mult.Sizes.r M≤r → ρ<Mult.CompactSizes.K M →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.CompactSizes.K M
    let G := gateCount (program ds)
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let back := backChunks d g K
    let active := compactReservationActive d g K D
    let E := back+synE G 0 active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let gb := guardG cG N l D
    let s := (D+1)/2+q+(gb+E)
    let s' := gb+E-5
    let working := W+s+D+guardKc cG N l D+G+m+4
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
    qrow*K+3≤n →
    compactSynLayerRoundOverheadR G cG N d g K D o W r h b l ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      32768*(R₂*2^n*(r*working))+2*stash := by
  filter_upwards [eventually_ge_atTop 2,compactCaller_runtime_eventually_guard,
    compactCallerR_eventually_width (gateCount (program ds)) cG,
    compactSynLayerRoundOverheadR_eventually (gateCount (program ds))
      (c+3+(Nat.clog 2 (m+1)*Nat.clog m NW)+2) (max 2 (Nat.clog m NW))]
    with M hM hguard hwidth hcost
  intro N D o W r h b l ρ stash hN hD hfit haddress hWp hW hh hb hl hrun hρ
  dsimp only
  intro hn
  have hdp : Mult.Sizes.d M≤Mult.Sizes.p M := by
    have := Mult.Sizes.d_le_b M
    unfold Mult.Sizes.p
    omega
  have hKd : Mult.CompactSizes.K M≤Mult.Sizes.d M := Mult.CompactSizes.K_le_d M
  have hKp := hKd.trans hdp
  have hgp : CompactReservationGrowth.guard M≤Mult.Sizes.p M := by
    have hgK : CompactReservationGrowth.guard M≤Mult.CompactSizes.K M := by
      have := Mult.CompactSizes.old_K_le_K M
      unfold CompactReservationGrowth.guard
      omega
    exact hgK.trans hKp
  obtain ⟨hgbE,hwork⟩ := hwidth (Mult.CompactSizes.K M) D W N l hD hfit hWp hN hl
  have hqD := compactReservation_axes hfit
  have hfit' := hfit
  unfold CompactReservationFits at hfit'
  have hs := scalarFieldsR N (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
    (Mult.CompactSizes.K M) D o W h b (CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))
    (frontChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.CompactSizes.K M))
    (backChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.CompactSizes.K M))
    (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) D) _ _ c (Mult.Sizes.p M)
    hN hdp hgp hKp hD hfit' haddress rfl hgbE hwork hW hh hb
  have hsc := hs.mono (compactCallerScalarBudget_le_combined (c+3)
    (Nat.clog 2 (m+1)*Nat.clog m NW) (Nat.clog m NW) (Mult.Sizes.p M))
  have hdivisor := (compactCaller_runtime_divisor_polynomial M hM).trans
    (compactCallerDivisorBudget_le_combined (c+3) (Nat.clog 2 (m+1)*Nat.clog m NW)
      (Nat.clog m NW) (Mult.Sizes.p M))
  have hdpos : 0<Mult.Sizes.d M := Mult.Sizes.one_le_d hM
  have hKpos : 0<Mult.CompactSizes.K M := Nat.zero_lt_of_lt hρ
  have hr : 0<r := (pow_pos (by decide : 0<2) (Mult.Sizes.ℓ M)).trans_le hrun
  have hWpos : 0<W := by
    have hb := Mult.Sizes.one_le_b hM
    have hp : 0<Mult.Sizes.p M := by unfold Mult.Sizes.p; omega
    exact hp.trans_le hWp
  have hgeom := callerAddressGeometryR N (Mult.CompactSizes.K M) D o
    (CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M)) (by omega) haddress
  have hpcs := compactTop_working_pcs_ok ds hKpos (by decide : 0<1) hfit hD hgeom.1
    (w := W) (oS := o)
  have hpcsR := fun pc hpc => (hpcs pc hpc).okR
  have hlB : l≤compactCallerCombinedBudget (c+3) (Nat.clog 2 (m+1)*Nat.clog m NW)
      (Nat.clog m NW) (Mult.Sizes.p M) :=
    hl.trans (hWp.trans hsc.hW)
  dsimp only [compactReservationActive,compactTopKernelCount,compactTopKernelOffset] at hsc hpcsR ⊢
  exact hcost cG N (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.CompactSizes.K M)
    D o W r h b l ρ _ stash _
    hsc.hB hdpos hKpos hr (hWpos.trans_le (by omega)) hsc.hN hsc.hd hsc.hg hsc.hK hsc.hD hsc.ho
    hsc.hW hsc.hdg hsc.hh hsc.hb hlB hρ hsc.hqrow hsc.hf hsc.hback hsc.hoffset hsc.hE hsc.hq
    hsc.haT hsc.hKq (hsc.hworking.trans (by omega)) hdivisor hgeom.1 hn hgeom.2
    (Nat.le_refl _) hrun hpcsR

end
end IntegerMultBounds.MathlibTM2.Cost
