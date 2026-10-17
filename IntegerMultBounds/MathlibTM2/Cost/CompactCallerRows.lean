module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
import IntegerMultBounds.MathlibTM2.Fast.SynRecB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The actual top-level padding includes outside rows and high spectators.
Its factor-two bound, rather than an equality between padded stocks, supplies
the row premise of the compact caller parameter theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
noncomputable section

/-- One extra exponent bit pays for padding the complete actual top row stock. -/
theorem compactCaller_topRows_le {d K R a rBits outside : ℕ}
    (hK : 0 < K) (hR : 0 < R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K ≤ a)
    (haUpper : a ≤ CompactGlobalRowPadding.rowAxes NW m d*K+outside)
    (hRbits : R ≤ 2^rBits) :
    compactTopRows d R a ≤
      2^(rBits+outside+1)*CompactGlobalRowPadding.initialRows NW m d K := by
  have hbase := (CompactGlobalRowPadding.initial_bounds NW m d K NW_pos hK).1
  calc
    compactTopRows d R a ≤ 2*(R*2^a) := (compactTopRows_bounds hK hR ha).2.2.1
    _ ≤ 2*(2^rBits*2^(CompactGlobalRowPadding.rowAxes NW m d*K+outside)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hRbits
        (Nat.pow_le_pow_right (by decide : 0<2) haUpper))
    _ = 2^(rBits+outside+1)*CompactGlobalRowPadding.originalRows NW m d K := by
      unfold CompactGlobalRowPadding.originalRows
      simp only [pow_add,pow_one]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ hbase

/-- Every actual descendant quotient satisfies the same caller row bound. -/
theorem compactCaller_topRows_quotient_le {d K R a rBits outside : ℕ}
    (hK : 0 < K) (hR : 0 < R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K ≤ a)
    (haUpper : a ≤ CompactGlobalRowPadding.rowAxes NW m d*K+outside)
    (hRbits : R ≤ 2^rBits) (j : ℕ) :
    compactTopRows d R a / NW^j ≤
      2^(rBits+outside+1)*CompactGlobalRowPadding.initialRows NW m d K :=
  (Nat.div_le_self _ _).trans (compactCaller_topRows_le hK hR ha haUpper hRbits)

end
end IntegerMultBounds.MathlibTM2.Cost
