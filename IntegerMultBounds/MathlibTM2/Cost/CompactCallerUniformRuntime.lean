module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters

/-! Packing is uniform over larger chunks up to the original dimension. This
lets the retuned compact sizes reuse the same actual repair implementation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open ActivePrefixStageFullData Filter
noncomputable section

theorem compactCaller_uniform_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (K D o r w extra : ℕ)
      (d : Inputs (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D (2^o*(3*(r*w))))),
      Mult.Sizes.K N ≤ K → K ≤ Mult.Sizes.d N →
      D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D →
      d.rows ≤ 2^extra*CompactGlobalRowPadding.initialRows NW m
        (Mult.Sizes.d N) K →
      extra ≤ Mult.Sizes.p N → Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w →
      ActivePrefixStageRuntimeData.Packed d 1 := by
  filter_upwards [eventually_ge_atTop 2, compactCaller_runtime_eventually_guard,
    Mult.Sizes.eventually_pow_p_le_r 1] with N hN hguard haxis
  intro K D o r w extra d hlo hhi hD hfit hrows hextra hr hw
  have hK : 0<K := by omega
  have hguardK : 8*CompactScalarAllowances.guardLog N+16≤K := hguard.trans hlo
  have hb := Mult.Sizes.one_le_b hN
  have hp6 : 6 ≤ Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hprod : D*K ≤ Mult.Sizes.b N*Mult.Sizes.b N :=
    Nat.mul_le_mul (hD.trans (Mult.Sizes.d_le_b N))
      (hhi.trans (Mult.Sizes.d_le_b N))
  have hs : D*K+3 ≤ Mult.Sizes.p N^2 := by
    unfold Mult.Sizes.p
    nlinarith
  have haddress := compactCaller_address_le (payload := 2^o*(3*(r*w))) hK hfit hrows
  have haddr : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤
      Mult.Sizes.p N^2+Mult.Sizes.p N := by
    rw [Nat.mul_comm D] at hs
    omega
  have hrp : Mult.Sizes.p N ≤ r := by simpa only [pow_one] using haxis.trans hr
  have hprodRW : Mult.Sizes.p N^2 ≤ r*w := by
    simpa only [pow_two] using Nat.mul_le_mul hrp hw
  have hfold : 3*(r*w) ≤ 2^o*(3*(r*w)) :=
    Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  have hrecord : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤ 2^o*(3*(r*w)) := by
    nlinarith
  have hcubeNat : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤ Mult.Sizes.p N^3 := by
    have hmul := Nat.mul_le_mul_right (Mult.Sizes.p N^2) (show 2 ≤ Mult.Sizes.p N by omega)
    nlinarith
  have hfNat : d.stage.f-1 ≤ Mult.Sizes.p N := by
    have hf : d.stage.f ≤ Mult.Sizes.d N := d.stage.widthFits
    have hd := Mult.Sizes.d_le_b N
    unfold Mult.Sizes.p
    omega
  have hell : (Mult.Sizes.p N : ℝ) ≤ (2:ℝ)^CompactScalarAllowances.guardLog N := by
    rw [compactCaller_runtime_guardLog hN]
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (Mult.Sizes.p N)
  exact compactRuntimePacked_of_dyadic d (Mult.Sizes.p N) (CompactScalarAllowances.guardLog N)
    (by exact_mod_cast (show 0 < Mult.Sizes.p N by omega))
    (by exact_mod_cast hfNat) hell hguardK rfl hrecord (by exact_mod_cast hcubeNat)


end
end IntegerMultBounds.MathlibTM2.Cost
