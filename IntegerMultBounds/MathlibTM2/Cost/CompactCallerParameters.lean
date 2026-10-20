module

public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
public import IntegerMultBounds.Machine.CompactReservationGrowth
import IntegerMultBounds.MathlibTM2.Fast.SynRecB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Caller size discharge for the shared reserved shape. Actual global padding
and extra outer spectators are counted in the repair address. The eventual
regime here uses `IntegerMultBounds.Sizes`; identifying those sizes with a
separate runtime parameter generator remains a caller obligation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationShape (Shape)
open Filter
noncomputable section

/-- Padding adds at most one row-address bit; extra outer spectators are retained.
The row count may be any smaller positive descendant count. -/
theorem compactCaller_address_le {axes guard K D payload rows extra : ℕ}
    (hK : 0<K) (hfit : CompactReservationFits axes guard K D)
    (hrows : rows ≤ 2^extra*CompactGlobalRowPadding.initialRows NW m axes K) :
    (compactReservationShape axes guard K D payload).bits + rows.log2 + 2 ≤ extra+K*D+3 := by
  have hc : 0<NW := NW_pos
  have hb := (CompactGlobalRowPadding.initial_bounds NW m axes K hc hK).2.2.1
  have hr : rows ≤ 2^(extra+CompactGlobalRowPadding.rowAxes NW m axes*K+1) := by
    calc
      rows ≤ 2^extra*(2*CompactGlobalRowPadding.originalRows NW m axes K) :=
        hrows.trans (Nat.mul_le_mul_left _ hb)
      _ = _ := by unfold CompactGlobalRowPadding.originalRows; simp only [pow_add,pow_one]; ring
  have hl : rows.log2 ≤ extra+CompactGlobalRowPadding.rowAxes NW m axes*K+1 := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_mono_right (b:=2) hr).trans_eq (Nat.log_pow (by decide) _)
  have hq : CompactGlobalRowPadding.rowAxes NW m axes≤D := by
    unfold CompactReservationFits at hfit
    omega
  have he : K*(D-CompactGlobalRowPadding.rowAxes NW m axes)+
      CompactGlobalRowPadding.rowAxes NW m axes*K=K*D := by
    rw [Nat.mul_comm (CompactGlobalRowPadding.rowAxes NW m axes) K,←Nat.mul_add,
      Nat.sub_add_cancel hq]
  rw [compactReservation_bits hK hfit]
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
