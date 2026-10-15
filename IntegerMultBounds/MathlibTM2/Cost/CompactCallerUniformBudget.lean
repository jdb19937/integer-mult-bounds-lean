module
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerCombinedBudget

/-! One explicit polynomial scalar budget for the actual compact caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

theorem compactCaller_uniform_eventually_workingWidth (G F : ℕ) (hF : F+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ K D W : ℕ,
    D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D →
    Mult.Sizes.p M≤W →
    let shift := (D+1)/2+compactTopKernelCount (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      K+(backChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K+
        synE G F (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D)
          (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D))
    shift+D≤W ∧ W+shift+D≤2*W := by
  filter_upwards [Mult.Sizes.eventually_big,
    tendsto_atTop.1 Mult.Sizes.tendsto_d (G+m+4)] with M hbig hlarge
  intro K D W hD hfit hW
  dsimp only
  have hd6 : Mult.Sizes.d M≤Mult.Sizes.d M^6 := Nat.le_self_pow (by decide) _
  have hD6 : D≤Mult.Sizes.d M^6 := hD.trans hd6
  have hone6 : 1≤Mult.Sizes.d M^6 := Nat.one_le_pow _ _ hbig.one_le_d
  have hactive : compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      K D≤Mult.Sizes.d M := by
    unfold compactReservationActive
    omega
  have hE := (mrO_synE_le G F _ hF).trans
    (Nat.mul_le_mul_left (G+m) (Nat.pow_le_pow_left hactive 6))
  have hpoly : (G+m+4)*Mult.Sizes.d M^6≤Mult.Sizes.b M := by
    calc
      (G+m+4)*Mult.Sizes.d M^6≤Mult.Sizes.d M*Mult.Sizes.d M^6 := Nat.mul_le_mul_right _ hlarge
      _ = Mult.Sizes.d M^7 := by rw [pow_succ]; ring
      _ ≤ Mult.Sizes.b M := hbig.pow_le_b (by decide : 7≤7)
  have hb : Mult.Sizes.b M≤Mult.Sizes.p M := Nat.le_mul_of_pos_left _ (by decide : 0<6)
  have hhalf := Nat.div_le_self (D+1) 2
  unfold CompactReservationFits at hfit
  have hs : (D+1)/2+compactTopKernelCount (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      K+(backChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K+
        synE G F (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D)
          (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D))+D≤W := by
    apply le_trans (b := (G+m+4)*Mult.Sizes.d M^6) ?_ (hpoly.trans (hb.trans hW))
    unfold compactTopKernelCount
    nlinarith only [hfit,hhalf,hE,hD6,hone6]
  exact ⟨hs,by omega⟩

private theorem scalarFields (N d g K D o W h b qrow f back active E working c p : ℕ)
    (hN : N≤p) (hd : d≤p) (hg : g≤p) (hK : K≤p) (hD : D≤d)
    (hfit : qrow+f+back≤D) (haddress : o+K*D≤N)
    (hactive : active=D-qrow-f-back) (hE : E≤W)
    (hwork : working≤2*W) (hW : W≤2^c*(p+1)) (hh : h≤p) (hb : b≤p) :
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerScalarBudget c p) := by
  have hB : 1≤compactCallerScalarBudget c p :=
    Nat.mul_pos (pow_pos (by decide : 0<2) _) (pow_pos (Nat.succ_pos p) _)
  have hp2 : p^2≤compactCallerScalarBudget c p :=
    (Nat.pow_le_pow_left (Nat.le_succ p) 2).trans
      (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0<2) _))
  have hp : p≤compactCallerScalarBudget c p := (Nat.le_self_pow (by decide : 2≠0) p).trans hp2
  have h2W : 2*W≤compactCallerScalarBudget c p := by
    calc
      2*W≤2*(2^c*(p+1)) := Nat.mul_le_mul_left _ hW
      _ = 2^(c+1)*(p+1) := by rw [pow_succ]; ring
      _ ≤ 2^(c+2)*(p+1)^2 := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : c+1≤c+2))
        (Nat.le_self_pow (by decide : 2≠0) _)
  have hWB : W≤compactCallerScalarBudget c p := (by omega : W≤2*W).trans h2W
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
    hoff.trans hp,hE.trans hWB,hqD.trans (hDp.trans hp),haT.trans hp,hKq.trans hp,hwork.trans h2W⟩
  have hprod : d*g≤p^2 := by simpa only [pow_two] using Nat.mul_le_mul hd hg
  exact hprod.trans hp2

theorem compactCaller_uniform_eventually_scalarBudget (G F c : ℕ) (hF : F+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ N K D o W h b : ℕ,
    Mult.Sizes.K M≤K → K≤Mult.Sizes.d M →
    N≤Mult.Sizes.p M → D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D →
    o+K*D≤N → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h≤Mult.Sizes.p M → b≤Mult.Sizes.p M →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := compactReservationActive d g K D
    let E := back+synE G F active active
    let working := W+((D+1)/2+(qrow+f)+E)+D
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerScalarBudget c (Mult.Sizes.p M)) := by
  filter_upwards [eventually_ge_atTop 2,compactCaller_runtime_eventually_guard,
    compactCaller_uniform_eventually_workingWidth G F hF] with M hM hguard hwidth
  intro N K D o W h b hlo hhi hN hD hfit haddress hWp hW hh hb
  have hdp : Mult.Sizes.d M≤Mult.Sizes.p M := by
    have := Mult.Sizes.d_le_b M
    unfold Mult.Sizes.p
    omega
  have hKp := hhi.trans hdp
  have hgp : CompactReservationGrowth.guard M≤Mult.Sizes.p M := by
    have hgK : CompactReservationGrowth.guard M≤K := by
      unfold CompactReservationGrowth.guard
      omega
    exact hgK.trans hKp
  have hwidth' := hwidth K D W hD hfit hWp
  have hE : backChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K+
      synE G F (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D)
        (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D)≤W := by
    have h := hwidth'.1
    omega
  dsimp only
  apply scalarFields <;> try assumption
  · rfl
  · simpa only [compactTopKernelCount] using hwidth'.2

theorem compactCaller_uniform_eventually_combinedBudget (G F c : ℕ) (hF : F+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ N K D o W h b : ℕ,
    Mult.Sizes.K M≤K → K≤Mult.Sizes.d M →
    N≤Mult.Sizes.p M → D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K D →
    o+K*D≤N → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h≤Mult.Sizes.p M → b≤Mult.Sizes.p M →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := compactReservationActive d g K D
    let E := back+synE G F active active
    let working := W+((D+1)/2+(qrow+f)+E)+D
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerCombinedBudget c (Nat.clog 2 (m+1)*Nat.clog m NW)
        (Nat.clog m NW) (Mult.Sizes.p M)) ∧
    NW^CompactGlobalRowPadding.depth m d≤
      compactCallerCombinedBudget c (Nat.clog 2 (m+1)*Nat.clog m NW)
        (Nat.clog m NW) (Mult.Sizes.p M) := by
  filter_upwards [eventually_ge_atTop 2,compactCaller_uniform_eventually_scalarBudget G F c hF]
    with M hM hs
  intro N K D o W h b hlo hhi hN hD hfit haddress hWp hW hh hb
  have hfields := hs N K D o W h b hlo hhi hN hD hfit haddress hWp hW hh hb
  constructor
  · exact hfields.mono (compactCallerScalarBudget_le_combined c
      (Nat.clog 2 (m+1)*Nat.clog m NW) (Nat.clog m NW) (Mult.Sizes.p M))
  · exact (compactCaller_runtime_divisor_polynomial M hM).trans
      (compactCallerDivisorBudget_le_combined c (Nat.clog 2 (m+1)*Nat.clog m NW)
        (Nat.clog m NW) (Mult.Sizes.p M))

end
end IntegerMultBounds.MathlibTM2.Cost
