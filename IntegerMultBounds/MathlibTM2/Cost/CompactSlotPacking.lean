module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSlot
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerParameters
import IntegerMultBounds.Machine.ActiveRepairLayoutDensityArithmetic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The parameter conditions of the compact slot operations

A logarithmic guard pays the bad records of the compact slot XOR (`compactSlotPacked_of_dyadic`),
and the actual multiplier sizes eventually provide it (`compactCaller_slot_eventually_packed`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node
open CompactGadgetReservationShape (Shape)
open Filter

noncomputable section

/-- A logarithmic guard pays every record address of the compact slot XOR. -/
theorem compactSlotPacked_of_dyadic {s : Shape} {k rows : ℕ} (p : ℝ) (ell : ℕ)
    (hp : 0 < p) (hf : ((k - 1 : ℕ) : ℝ) ≤ p) (hell : p ≤ (2 : ℝ) ^ ell)
    (hchunk : 8*ell + 16 ≤ s.chunk) (hguard : s.guard = 4*ell + 6)
    (hrecord : s.bits + rows.log2 + 2 ≤ s.payload)
    (hcube : ((s.bits + rows.log2 + 2 : ℕ) : ℝ) ≤ p^3) :
    CompactSlotPacked s k rows 1 := by
  refine ⟨by omega, by omega, hrecord, ?_⟩
  have h := ActiveRepairLayoutDensityArithmetic.dyadic_late_paid p (k - 1) ell s.chunk
    (s.bits + rows.log2 + 1) hp hf hell hchunk (by push_cast at hcube ⊢; linarith)
  rw [hguard]
  unfold cxDensity
  unfold VaryingControlRepairDensity.lateDensity at h
  push_cast at h ⊢
  linarith

/-- Actual multiplier sizes pay the compact slot operations of every width up to the dimension,
on every row stock of the shared reservation, uniformly over chunks up to the dimension. -/
theorem compactCaller_slot_uniform_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (K D o r w extra k rows : ℕ),
      Mult.Sizes.K N ≤ K → K ≤ Mult.Sizes.d N → D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N) K D →
      rows ≤ 2^extra*CompactGlobalRowPadding.initialRows NW m (Mult.Sizes.d N) K →
      extra ≤ Mult.Sizes.p N → Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w → k ≤ Mult.Sizes.d N →
      CompactSlotPacked (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        K D (2^o*(3*(r*w)))) k rows 1 := by
  filter_upwards [eventually_ge_atTop 2, compactCaller_runtime_eventually_guard,
    Mult.Sizes.eventually_pow_p_le_r 1] with N hN hguard haxis
  intro K D o r w extra k rows hlo hhi hD hfit hrows hextra hr hw hk
  have hK : 0 < K := by omega
  have hguardK : 8*CompactScalarAllowances.guardLog N+16 ≤ K := hguard.trans hlo
  have hb := Mult.Sizes.one_le_b hN
  have hp6 : 6 ≤ Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hprod : D*K ≤ Mult.Sizes.b N*Mult.Sizes.b N :=
    Nat.mul_le_mul (hD.trans (Mult.Sizes.d_le_b N)) (hhi.trans (Mult.Sizes.d_le_b N))
  have hs : D*K+3 ≤ Mult.Sizes.p N^2 := by
    unfold Mult.Sizes.p
    nlinarith
  have haddress := compactCaller_address_le (payload := 2^o*(3*(r*w))) hK hfit hrows
  have haddr : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*w)))).bits+rows.log2+2 ≤ Mult.Sizes.p N^2+Mult.Sizes.p N := by
    rw [Nat.mul_comm D] at hs
    omega
  have hrp : Mult.Sizes.p N ≤ r := by simpa only [pow_one] using haxis.trans hr
  have hprodRW : Mult.Sizes.p N^2 ≤ r*w := by
    simpa only [pow_two] using Nat.mul_le_mul hrp hw
  have hfold : 3*(r*w) ≤ 2^o*(3*(r*w)) :=
    Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  have hrecord : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*w)))).bits+rows.log2+2 ≤ 2^o*(3*(r*w)) := by
    nlinarith
  have hcubeNat : (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      K D (2^o*(3*(r*w)))).bits+rows.log2+2 ≤ Mult.Sizes.p N^3 := by
    have hmul := Nat.mul_le_mul_right (Mult.Sizes.p N^2) (show 2 ≤ Mult.Sizes.p N by omega)
    nlinarith
  have hfNat : k-1 ≤ Mult.Sizes.p N := by
    have hd := Mult.Sizes.d_le_b N
    unfold Mult.Sizes.p
    omega
  have hell : (Mult.Sizes.p N : ℝ) ≤ (2:ℝ)^CompactScalarAllowances.guardLog N := by
    rw [compactCaller_runtime_guardLog hN]
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (Mult.Sizes.p N)
  exact compactSlotPacked_of_dyadic (Mult.Sizes.p N) (CompactScalarAllowances.guardLog N)
    (by exact_mod_cast (show 0 < Mult.Sizes.p N by omega))
    (by exact_mod_cast hfNat) hell hguardK rfl hrecord (by exact_mod_cast hcubeNat)

/-- Actual multiplier sizes pay the compact slot operations at the actual chunk. -/
theorem compactCaller_slot_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (D o r w extra k rows : ℕ),
      D ≤ Mult.Sizes.d N →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D →
      rows ≤ 2^extra*CompactGlobalRowPadding.initialRows NW m
        (Mult.Sizes.d N) (Mult.Sizes.K N) →
      extra ≤ Mult.Sizes.p N → Mult.Sizes.r N ≤ r → Mult.Sizes.p N ≤ w → k ≤ Mult.Sizes.d N →
      CompactSlotPacked (compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D (2^o*(3*(r*w)))) k rows 1 := by
  filter_upwards [compactCaller_slot_uniform_eventually_packed] with N hp
  intro D o r w extra k rows hD hfit hrows hextra hr hw hk
  exact hp _ D o r w extra k rows le_rfl (Mult.Sizes.K_le_d N) hD hfit hrows hextra hr hw hk

end

end IntegerMultBounds.MathlibTM2.Cost
