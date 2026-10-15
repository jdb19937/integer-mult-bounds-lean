module
public import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadRuntime
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformBudget
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopReady

/-! Eventual absorption of actual complete compact-round overhead. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

private theorem callerAddressGeometry (N K D o qrow : ℕ)
    (hq : qrow≤D) (haddress : o+K*D≤N) :
    qrow*K≤N-(o+K*(D-qrow)) ∧ o+K*(D-qrow)≤N := by
  have he : K*(D-qrow)+qrow*K=K*D := by
    rw [Nat.mul_comm qrow K,←Nat.mul_add,Nat.sub_add_cancel hq]
  omega

/-- Actual runtime sizes and address/width bounds pay the complete compact
round overhead, including the computed piece and configuration records. -/
theorem compactCaller_uniform_eventually_roundOverhead
    (ds : ComplexFramedExecution.Directions) (c : ℕ)
    (hF : factorCount (program ds)+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ N K D o W r h b ρ stash : ℕ,
    Mult.Sizes.K M≤K → K≤Mult.Sizes.d M →
    N≤Mult.Sizes.p M → D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D →
    o+K*D≤N → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h≤Mult.Sizes.p M → b≤Mult.Sizes.p M →
    Mult.Sizes.r M≤r → ρ<K →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let G := gateCount (program ds)
    let F := factorCount (program ds)
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := compactReservationActive d g K D
    let E := back+synE G F active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(back+active)
    let shift := (D+1)/2+q+E
    let working := W+shift+D
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W shift a 1 R₂ q aT K o D
    qrow*K+3≤n →
    compactSynLayerRoundOverhead G F N d g K D o W r h b ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      32768*(R₂*2^n*(r*working))+2*stash := by
  filter_upwards [eventually_ge_atTop 2,
    compactCaller_uniform_eventually_combinedBudget (gateCount (program ds)) (factorCount (program ds)) c hF,
    compactSynLayerRoundOverhead_eventually ds (gateCount (program ds)) (factorCount (program ds))
      (c+(Nat.clog 2 (m+1)*Nat.clog m NW)+2) (max 2 (Nat.clog m NW))]
    with M hM hbudget hcost
  intro N K D o W r h b ρ stash hlo hhi hN hD hfit haddress hWp hW hh hb hrun hρ
  dsimp only
  intro hn
  obtain ⟨hs,hdivisor⟩ := hbudget N K D o W h b hlo hhi hN hD hfit haddress hWp hW hh hb
  have hdpos : 0<Mult.Sizes.d M := Mult.Sizes.one_le_d hM
  have hKpos : 0<K := Nat.zero_lt_of_lt hρ
  have hr : 0<r := (pow_pos (by decide : 0<2) (Mult.Sizes.ℓ M)).trans_le hrun
  have hWpos : 0<W := by
    have hb := Mult.Sizes.one_le_b hM
    have hp : 0<Mult.Sizes.p M := by unfold Mult.Sizes.p; omega
    exact hp.trans_le hWp
  have hqD := compactReservation_axes hfit
  have hgeom := callerAddressGeometry N K D o
    (CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M)) (by omega) haddress
  have hpcs := compactTop_working_pcs_ok ds hKpos (by decide : 0<1) hfit hD hgeom.1
    (w := W) (oS := o)
  dsimp only [compactReservationActive] at hs ⊢
  dsimp only [compactReservationActive,compactTopKernelCount] at hpcs
  exact (hcost N (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K
    D o W r h b ρ stash
    (compactCallerCombinedBudget c (Nat.clog 2 (m+1)*Nat.clog m NW) (Nat.clog m NW) (Mult.Sizes.p M))
    hs.hB hF hdpos hKpos hr hWpos hs.hN hs.hd hs.hg hs.hK hs.hD hs.ho hs.hW hs.hdg
    hs.hh hs.hb hρ hs.hqrow hs.hf hs.hback hs.hoffset hs.hE hs.hq hs.haT hs.hKq
    hdivisor hgeom.1 hn hgeom.2 (Nat.le_refl _) hrun hpcs)

theorem compactCaller_retuned_eventually_roundOverhead
    (ds : ComplexFramedExecution.Directions) (c : ℕ)
    (hF : factorCount (program ds)+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ N D o W r h b ρ stash : ℕ,
    N≤Mult.Sizes.p M → D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.CompactSizes.K M) D →
    o+Mult.CompactSizes.K M*D≤N → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h≤Mult.Sizes.p M → b≤Mult.Sizes.p M →
    Mult.Sizes.r M≤r → ρ<Mult.CompactSizes.K M →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.CompactSizes.K M
    let G := gateCount (program ds)
    let F := factorCount (program ds)
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := compactReservationActive d g K D
    let E := back+synE G F active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(back+active)
    let shift := (D+1)/2+q+E
    let working := W+shift+D
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W shift a 1 R₂ q aT K o D
    qrow*K+3≤n →
    compactSynLayerRoundOverhead G F N d g K D o W r h b ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      32768*(R₂*2^n*(r*working))+2*stash := by
  filter_upwards [compactCaller_uniform_eventually_roundOverhead ds c hF] with M hcost
  intro N D o W r h b ρ stash
  exact hcost N (Mult.CompactSizes.K M) D o W r h b ρ stash
    (Mult.CompactSizes.old_K_le_K M) (Mult.CompactSizes.K_le_d M)

end
end IntegerMultBounds.MathlibTM2.Cost
