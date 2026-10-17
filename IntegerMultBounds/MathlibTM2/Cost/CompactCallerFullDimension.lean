module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerCapacity
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The actual initial transform has original dimension minus one. Its runtime
integer-root sizes eventually pay the complete compact reservation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer Filter
noncomputable section

/-- The chunk is eventually strictly smaller than the original dimension. -/
theorem compactCaller_runtime_eventually_chunk_predecessor : ∀ᶠ N : ℕ in atTop,
    Mult.Sizes.K N≤Mult.Sizes.d N-1 := by
  filter_upwards [Mult.Sizes.tendsto_K.eventually (eventually_ge_atTop 2)] with N hK
  have hpow : Mult.Sizes.K N^2≤Mult.Sizes.K N^Mult.Sizes.cExp :=
    Nat.pow_le_pow_right (by omega) (by norm_num [Mult.Sizes.cExp])
  have hd := hpow.trans (Mult.Sizes.K_pow_le N)
  have hlt : Mult.Sizes.K N<Mult.Sizes.d N := by nlinarith
  omega

/-- Full initial axes have length `d-1`, and pay both the reservation and one chunk. -/
theorem compactCaller_runtime_eventually_full_dimension : ∀ᶠ N : ℕ in atTop,
    CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) (Mult.Sizes.d N-1) ∧
    Mult.Sizes.K N≤Mult.Sizes.d N-1 := by
  filter_upwards [compactCaller_runtime_eventually_capacity 2 (by decide),
    compactCaller_runtime_eventually_chunk_predecessor,
    Mult.Sizes.tendsto_d.eventually (eventually_ge_atTop 2)] with N hcap hK hd
  exact ⟨hcap (Mult.Sizes.d N-1) (by omega),hK⟩

/-- Apply the full-dimension result directly to the nonterminal synthetic selector. -/
theorem compactCaller_runtime_eventually_initial_synDp : ∀ᶠ N : ℕ in atTop,
    ∀ (es : List ℕ) (ell h : ℕ), es.length=Mult.Sizes.d N-1 → h+1<ell →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) (synDp es ell h) ∧
      Mult.Sizes.K N≤synDp es ell h := by
  filter_upwards [compactCaller_runtime_eventually_full_dimension] with N hfull
  intro es ell h hlen hh
  simpa only [synDp,hh,ite_true,hlen] using hfull

end
end IntegerMultBounds.MathlibTM2.Cost
