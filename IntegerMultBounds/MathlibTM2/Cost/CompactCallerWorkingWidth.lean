module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection

/-! The compact precision shift fits the actual caller precision. This keeps
the padded working volume within its fixed dyadic envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer Filter
open CompactGadgetReservationCapacity
noncomputable section

theorem compactCaller_runtime_eventually_workingWidth (G F : ℕ) (hF : F+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ D W : ℕ,
    D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M) D →
    Mult.Sizes.p M≤W →
    let shift := (D+1)/2+compactTopKernelCount (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.Sizes.K M)+(backChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M)+
        synE G F (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M) D)
          (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M) D))
    shift+D≤W ∧ W+shift+D≤2*W := by
  filter_upwards [Mult.Sizes.eventually_big,
    tendsto_atTop.1 Mult.Sizes.tendsto_d (G+m+4)] with M hbig hlarge
  intro D W hD hfit hW
  dsimp only
  have hd6 : Mult.Sizes.d M≤Mult.Sizes.d M^6 := Nat.le_self_pow (by decide) _
  have hD6 : D≤Mult.Sizes.d M^6 := hD.trans hd6
  have hone6 : 1≤Mult.Sizes.d M^6 := Nat.one_le_pow _ _ hbig.one_le_d
  have hactive : compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.Sizes.K M) D≤Mult.Sizes.d M := by
    unfold compactReservationActive
    omega
  have hE := (mrO_synE_le G F _ hF).trans
    (Nat.mul_le_mul_left (G+m) (Nat.pow_le_pow_left hactive 6))
  have hpoly : (G+m+4)*Mult.Sizes.d M^6≤Mult.Sizes.b M := by
    calc
      (G+m+4)*Mult.Sizes.d M^6≤Mult.Sizes.d M*Mult.Sizes.d M^6 := Nat.mul_le_mul_right _ hlarge
      _ = Mult.Sizes.d M^7 := by rw [pow_succ]; ring
      _ ≤ Mult.Sizes.b M := hbig.pow_le_b (by decide : 7≤20)
  have hb : Mult.Sizes.b M≤Mult.Sizes.p M := Nat.le_mul_of_pos_left _ (by decide : 0<6)
  have hhalf := Nat.div_le_self (D+1) 2
  unfold CompactReservationFits at hfit
  have hs : (D+1)/2+compactTopKernelCount (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.Sizes.K M)+(backChunks (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M)+
        synE G F (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M) D)
          (compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M) D))+D≤W := by
    apply le_trans (b := (G+m+4)*Mult.Sizes.d M^6) ?_ (hpoly.trans (hb.trans hW))
    unfold compactTopKernelCount
    nlinarith only [hfit,hhalf,hE,hD6,hone6]
  exact ⟨hs,by omega⟩

end
end IntegerMultBounds.MathlibTM2.Cost
