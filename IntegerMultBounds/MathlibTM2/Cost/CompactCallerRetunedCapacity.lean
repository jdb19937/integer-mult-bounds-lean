module

public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerFullDimension
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Larger compact chunks decrease the front/back reservation. The existing
proved capacity therefore applies to the parallel eighth-root sizes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer Filter
open CompactGadgetReservationCapacity
noncomputable section

theorem compactChunks_antitone (x k k' : ℕ) (hk : 0<k) (hkk : k≤k') :
    chunks x k'≤chunks x k := by
  have hk' : 0<k' := hk.trans_le hkk
  have hx := (Compact.Layout.ceiling_chunks x k hk).1
  change x≤chunks x k*k at hx
  have hx' : x≤chunks x k*k' := hx.trans (Nat.mul_le_mul_left _ hkk)
  apply Nat.le_of_lt_succ
  change (x+k'-1)/k'<chunks x k+1
  apply (Nat.div_lt_iff_lt_mul hk').2
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem compactReservationFits_mono_chunk {d g K K' D : ℕ}
    (hK : 0<K) (hKK : K≤K') (h : CompactReservationFits d g K D) :
    CompactReservationFits d g K' D := by
  have hf := compactChunks_antitone (2*(d*g)) K K' hK hKK
  have hb := compactChunks_antitone (d*g) K K' hK hKK
  change frontChunks d g K'≤frontChunks d g K at hf
  change backChunks d g K'≤backChunks d g K at hb
  unfold CompactReservationFits at h ⊢
  omega

theorem compactCaller_retuned_eventually_full_dimension : ∀ᶠ M : ℕ in atTop,
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) (Mult.Sizes.d M-1) ∧
    Mult.CompactSizes.K M≤Mult.Sizes.d M-1 := by
  filter_upwards [compactCaller_runtime_eventually_full_dimension,
    Mult.CompactSizes.eventually_K_le_predecessor,
    Mult.Sizes.tendsto_K.eventually (eventually_ge_atTop 1)] with M hfit hnew hK
  exact ⟨compactReservationFits_mono_chunk (by omega) (Mult.CompactSizes.old_K_le_K M) hfit.1,hnew⟩

end
end IntegerMultBounds.MathlibTM2.Cost
