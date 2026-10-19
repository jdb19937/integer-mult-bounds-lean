module

import IntegerMultBounds.Machine.CompactGuardGrowth
public import IntegerMultBounds.Machine.CompactGlobalReservation
public import IntegerMultBounds.Machine.CompactScalarAllowances
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! The manuscript's actual original-axis reservation is sublinear in the
actual dimension. This never asserts that a small selected-axis set contains
the full reservation; the fallback decision is formalized separately. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactReservationGrowth
noncomputable section
open Filter Asymptotics Sizes CompactScalarAllowances
open CompactGadgetReservationCapacity CompactGlobalRowPadding

def guard (n : ℕ) := 4*guardLog n+6
def reserved (c m n : ℕ) := CompactGlobalReservation.reservedAxes c m (d n) (guard n) (K n)

theorem fields_bound (d G K : ℕ) (hK : 0<K) :
    ((frontChunks d G K+backChunks d G K:ℕ):ℝ)*(K:ℝ)≤3*(d:ℝ)*(G:ℝ)+2*(K:ℝ) := by
  have hf := (Compact.Layout.ceiling_chunks (2*capacity d G) K hK).2
  have hb := (Compact.Layout.ceiling_chunks (capacity d G) K hK).2
  change frontChunks d G K*K<2*(d*G)+K at hf
  change backChunks d G K*K<d*G+K at hb
  have h : (frontChunks d G K+backChunks d G K)*K≤3*d*G+2*K := by nlinarith
  exact_mod_cast h

end
end IntegerMultBounds.Machine.CompactReservationGrowth
