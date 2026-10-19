module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerGuardPower
import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.Machine.CompactGlobalReservation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Quantitative reservation savings for the actual half-dimension compact chunk. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationCapacity
noncomputable section

/-- The chunk is at least half the dimension: `d ≤ 2 Kroot ≤ 2K`. -/
theorem compactRetuned_chunk_lower (M : ℕ) :
    (Mult.Sizes.d M:ℝ)≤2*(Mult.CompactSizes.K M:ℝ) := by
  exact_mod_cast (Mult.CompactSizes.d_le_two_Kroot M).trans
    (Nat.mul_le_mul_left 2 (Mult.CompactSizes.Kroot_le_K M))

private theorem fieldsRate {d g k f : ℝ} (hg : 0≤g) (hk : 0<k)
    (hchunk : d≤2*k) (hfields : f*k≤3*d*g+2*k) :
    f≤6*g+2 := by
  have hscale := mul_le_mul_of_nonneg_right hchunk (show 0≤3*g by positivity)
  apply (mul_le_mul_iff_left₀ hk).mp
  nlinarith only [hfields,hscale]

/-- Dyadic coefficient for the complete original row/front/back reservation. -/
def compactRetunedReservationCoeff (a : ℝ) : ℝ :=
  compactLayerDyadic (((Nat.clog 2 NW:ℝ)+8)*compactCallerGuardPowerCoeff a)

/-- All reserved axes fit every positive exponent, including the proposed compact layer
exponent. This is stronger than merely sublinear growth. -/
theorem compactRetuned_reservation_power (M : ℕ) (hM : 2≤M) (a : ℝ) (ha : 0<a) :
    (CompactGlobalReservation.reservedAxes NW m (Mult.Sizes.d M)
      (Mult.CompactSizes.guard M) (Mult.CompactSizes.K M):ℝ)≤
      compactRetunedReservationCoeff a*(Mult.Sizes.d M:ℝ)^a := by
  let d := Mult.Sizes.d M
  let g := Mult.CompactSizes.guard M
  let K := Mult.CompactSizes.K M
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K+backChunks d g K
  have hd : 1≤d := Mult.Sizes.one_le_d hM
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have hK : 0<K := lt_of_lt_of_le (by decide : 0<1) (Mult.CompactSizes.one_le_K hM)
  have hg : (1:ℝ)≤g := by
    change (1:ℝ)≤(4*Nat.clog 2 (Mult.Sizes.p M)+6:ℕ)
    exact_mod_cast (by omega : 1≤4*Nat.clog 2 (Mult.Sizes.p M)+6)
  have hfields := fieldsRate (by positivity : (0:ℝ)≤g)
    (by exact_mod_cast hK) (compactRetuned_chunk_lower M)
    (CompactReservationGrowth.fields_bound d g K hK)
  have hdimP : 2*d≤Mult.Sizes.p M := by
    have hdb := Mult.Sizes.d_le_b M
    change 2*Mult.Sizes.d M≤6*Mult.Sizes.b M
    omega
  have hlog : Nat.clog m (2*d)≤Nat.clog 2 (Mult.Sizes.p M) :=
    Nat.clog_mono (by decide : 1<2) (by decide : 2≤m) hdimP
  have hrow : (q:ℝ)≤(Nat.clog 2 NW:ℝ)*(g:ℝ) := by
    have hgp : Nat.clog 2 (Mult.Sizes.p M)≤g := by
      change Nat.clog 2 (Mult.Sizes.p M)≤4*Nat.clog 2 (Mult.Sizes.p M)+6
      omega
    exact_mod_cast Nat.mul_le_mul_left (Nat.clog 2 NW) (hlog.trans hgp)
  have htwo : (2:ℝ)≤2*(g:ℝ) := by linarith
  have hsum : ((q+f:ℕ):ℝ)≤((Nat.clog 2 NW:ℝ)+8)*(g:ℝ) := by
    push_cast
    nlinarith only [hrow,hfields,htwo]
  have hguard := compactCaller_guard_power M hM a ha
  have hbound : ((q+f:ℕ):ℝ)≤((Nat.clog 2 NW:ℝ)+8)*compactCallerGuardPowerCoeff a*(d:ℝ)^a := by
    calc
      _ ≤ ((Nat.clog 2 NW:ℝ)+8)*(g:ℝ) := hsum
      _ ≤ ((Nat.clog 2 NW:ℝ)+8)*(compactCallerGuardPowerCoeff a*(d:ℝ)^a) :=
        mul_le_mul_of_nonneg_left hguard (add_nonneg (Nat.cast_nonneg _) (by norm_num))
      _ = _ := by ring
  have hcoeff := mul_le_mul_of_nonneg_right
    (compactLayerDyadic_le (((Nat.clog 2 NW:ℝ)+8)*compactCallerGuardPowerCoeff a))
    (Real.rpow_nonneg hd0.le a)
  simpa only [q,f,d,g,K,CompactGlobalReservation.reservedAxes,Nat.add_assoc,
    compactRetunedReservationCoeff] using hbound.trans hcoeff

end
end IntegerMultBounds.MathlibTM2.Cost
