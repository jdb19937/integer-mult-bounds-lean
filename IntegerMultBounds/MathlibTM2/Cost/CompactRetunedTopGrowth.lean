module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedReservationGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerLayerGrowth
public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlPower
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The complete compact top cost envelope at the actual eighth-root sizes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

/-- Exact dimension-dependent factor in the complete actual top-cost bound. -/
def compactRetunedTopEnvelope (packD : ℕ) (ds : ComplexFramedExecution.Directions) (M D : ℕ) : ℝ :=
  let d := Mult.Sizes.d M
  let g := Mult.CompactSizes.guard M
  let K := Mult.CompactSizes.K M
  let q := CompactGlobalRowPadding.rowAxes NW m d+frontChunks d g K
  16384*compactTopCountConst CompactInterim.lam*(d:ℝ)^CompactInterim.lam+
    512*(backChunks d g K:ℝ)+512*(q:ℝ)+
    compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) packD ds CompactInterim.lam) m CompactInterim.lam*
      (compactReservationActive d g K D:ℝ)^CompactInterim.lam*(g:ℝ)^Parameters.tau

/-- One fixed dyadic coefficient includes controls, reservation and recursive layers. -/
def compactRetunedTopCoeff (packD : ℕ) (ds : ComplexFramedExecution.Directions) : ℝ :=
  compactLayerDyadic (16384*compactTopCountConst CompactInterim.lam+
    512*compactRetunedReservationCoeff CompactInterim.lam'+
    compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) packD ds CompactInterim.lam) m CompactInterim.lam*
      compactCallerGuardPowerCoeff (CompactInterim.lam'-CompactInterim.lam))

/-- The actual top envelope fits the proposed layer exponent, with no guard,
reservation-rate or recursive-cost envelope premise supplied by the caller. -/
theorem compactRetuned_top_envelope (packD : ℕ) (ds : ComplexFramedExecution.Directions)
    (M : ℕ) (hM : 2≤M) (D : ℕ) (hD : D≤Mult.Sizes.d M) :
    compactRetunedTopEnvelope packD ds M D≤
      compactRetunedTopCoeff packD ds*(Mult.Sizes.d M:ℝ)^CompactInterim.lam' := by
  let d := Mult.Sizes.d M
  let g := Mult.CompactSizes.guard M
  let K := Mult.CompactSizes.K M
  let q := CompactGlobalRowPadding.rowAxes NW m d+frontChunks d g K
  let A := 16384*compactTopCountConst CompactInterim.lam
  let C := compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) packD ds CompactInterim.lam) m CompactInterim.lam
  have hd : (1:ℝ)≤d := by exact_mod_cast Mult.Sizes.one_le_d hM
  have hl : 0≤CompactInterim.lam := by norm_num [CompactInterim.lam]
  have hll : CompactInterim.lam≤CompactInterim.lam' := by norm_num [CompactInterim.lam,CompactInterim.lam']
  have hdp := Real.rpow_le_rpow_of_exponent_le hd hll
  have hA : 0≤A := mul_nonneg (by norm_num) (compactLayerDyadic_pos _).le
  have hC : 0≤C := (compactLayerDyadic_pos _).le
  have hcontrol : A*(d:ℝ)^CompactInterim.lam≤A*(d:ℝ)^CompactInterim.lam' :=
    mul_le_mul_of_nonneg_left hdp hA
  have hres := compactRetuned_reservation_power M hM CompactInterim.lam'
    (by norm_num [CompactInterim.lam'])
  have hreservation : 512*(backChunks d g K:ℝ)+512*(q:ℝ)≤
      512*compactRetunedReservationCoeff CompactInterim.lam'*(d:ℝ)^CompactInterim.lam' := by
    have he : backChunks d g K+q=CompactGlobalReservation.reservedAxes NW m d g K := by
      dsimp only [q,CompactGlobalReservation.reservedAxes]
      omega
    have h := mul_le_mul_of_nonneg_left hres (by norm_num : (0:ℝ)≤512)
    rw [←he,Nat.cast_add] at h
    nlinarith only [h]
  have hactive : compactReservationActive d g K D≤d := by
    dsimp only [compactReservationActive]
    omega
  have hactiveR : (compactReservationActive d g K D:ℝ)≤d := by exact_mod_cast hactive
  have hg := compactCaller_interim_layer_growth M hM
  have hrec : C*(compactReservationActive d g K D:ℝ)^CompactInterim.lam*(g:ℝ)^Parameters.tau≤
      C*compactCallerGuardPowerCoeff (CompactInterim.lam'-CompactInterim.lam)*(d:ℝ)^CompactInterim.lam' := by
    have ha := Real.rpow_le_rpow (Nat.cast_nonneg _) hactiveR hl
    have hg0 := Real.rpow_nonneg (Nat.cast_nonneg g) Parameters.tau
    have hs := mul_le_mul_of_nonneg_right ha hg0
    have h := mul_le_mul_of_nonneg_left (hs.trans hg) hC
    simpa only [mul_assoc] using h
  have hsum : compactRetunedTopEnvelope packD ds M D≤
      (A+512*compactRetunedReservationCoeff CompactInterim.lam'+
        C*compactCallerGuardPowerCoeff (CompactInterim.lam'-CompactInterim.lam))*(d:ℝ)^CompactInterim.lam' := by
    change A*(d:ℝ)^CompactInterim.lam+512*(backChunks d g K:ℝ)+512*(q:ℝ)+
      C*(compactReservationActive d g K D:ℝ)^CompactInterim.lam*(g:ℝ)^Parameters.tau≤_
    nlinarith only [hcontrol,hreservation,hrec]
  have hcoeff := mul_le_mul_of_nonneg_right
    (compactLayerDyadic_le (A+512*compactRetunedReservationCoeff CompactInterim.lam'+
      C*compactCallerGuardPowerCoeff (CompactInterim.lam'-CompactInterim.lam)))
    (Real.rpow_nonneg (Nat.cast_nonneg d) CompactInterim.lam')
  exact hsum.trans hcoeff

end
end IntegerMultBounds.MathlibTM2.Cost
