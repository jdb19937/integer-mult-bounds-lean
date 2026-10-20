module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRows
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Row bounds from the original selected interval and actual top-level split. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
noncomputable section

/-- The top split consists of reserved row bits plus original high spectators. -/
theorem compactCaller_selected_split {d g K D o N : ℕ}
    (h : CompactReservationFits d g K D) (hfit : o+K*D≤N) :
    N-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)) =
      CompactGlobalRowPadding.rowAxes NW m d*K+(N-(o+K*D)) := by
  have hq : CompactGlobalRowPadding.rowAxes NW m d≤D := by
    have := compactReservation_axes h
    omega
  have he := congrArg (fun x => K*x) (Nat.sub_add_cancel hq)
  simp only [Nat.mul_add] at he
  rw [Nat.mul_comm (CompactGlobalRowPadding.rowAxes NW m d) K]
  omega

/-- All non-row selected bits are present in the native shape; no extra high
spectator multiplier remains inside the recursively executed address. -/
theorem compactCaller_selected_native_rows {d g K D payload : ℕ}
    (hK : 0<K) (h : CompactReservationFits d g K D) (rows : ℕ) :
    2^(K*(D-CompactGlobalRowPadding.rowAxes NW m d)-
      (compactReservationShape d g K D payload).bits)*rows=rows := by
  rw [compactReservation_bits hK h]
  simp

/-- Actual native descendant rows satisfy the caller bound, with only original
outside rows, original high spectators and one padding bit in the exponent. -/
theorem compactCaller_selected_rows_le {d g K D o N R rBits : ℕ}
    (hK : 0<K) (hR : 0<R) (h : CompactReservationFits d g K D)
    (hfit : o+K*D≤N) (hRbits : R≤2^rBits) (j : ℕ) :
    compactTopRows d R (N-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)))/NW^j ≤
      2^(rBits+(N-(o+K*D))+1)*CompactGlobalRowPadding.initialRows NW m d K := by
  have he := compactCaller_selected_split h hfit
  apply compactCaller_topRows_quotient_le hK hR
  · omega
  · exact he.le
  · exact hRbits

/-- A simple original-address precision budget suffices for the row exponent. -/
theorem compactCaller_selected_extra_le {N o K D rBits p : ℕ}
    (hp : rBits+N+1≤p) : rBits+(N-(o+K*D))+1≤p := by omega

end
end IntegerMultBounds.MathlibTM2.Cost
