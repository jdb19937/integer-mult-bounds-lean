module

public import IntegerMultBounds.Machine.RecoverHeaderControlSetup
public import IntegerMultBounds.Schoenhage.LevelParams

/-! Pay all public-header parsing, binary division, ruler generation and
residual adjustment from linear parameter volume. The existing binary-size
square bound absorbs division setup; no asymptotic or supplied cost premise
is needed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverHeaderControlBudget
open Spec.SignedRingProduct (header gamma)

/-- The exponent is encoded as a power-of-two size, so its gamma width grows
with the exponent rather than the much larger transform length. -/
theorem header_length_le (precision lengthExponent wordWidth : ℕ)
    (precisionPositive : 1 ≤ precision) (widthPositive : 1 ≤ wordWidth) :
    (header precision (2 ^ lengthExponent) wordWidth).length ≤
      2 * (precision + lengthExponent + wordWidth + 1) := by
  have sizePositive : 1 ≤ 2 ^ lengthExponent := by
    have positive := Nat.two_pow_pos lengthExponent
    omega
  have precisionSize := Schoenhage.size_le_self precision
  have widthSize := Schoenhage.size_le_self wordWidth
  simp only [header,List.length_append,Spec.SignedRingProduct.length_gamma precisionPositive,
    Spec.SignedRingProduct.length_gamma sizePositive,Spec.SignedRingProduct.length_gamma widthPositive,Nat.size_pow]
  omega

/-- The quadratic descriptor-width term is linear in its encoded count.
All actual header/control operations and connecting transitions are included. -/
theorem cost_le_linear (precision lengthExponent wordWidth : ℕ)
    (precisionPositive : 1 ≤ precision) (widthPositive : 1 ≤ wordWidth) :
    RecoverHeaderControlSetup.cost precision lengthExponent wordWidth ≤
      2100 * (precision + lengthExponent + wordWidth + 1) := by
  have headerBound := header_length_le precision lengthExponent wordWidth precisionPositive widthPositive
  have precisionSize := Schoenhage.size_le_self precision
  have precisionSquare := Schoenhage.size_sq_le precision
  have widthSize := Schoenhage.size_le_self wordWidth
  have quotientBound : precision / 6 ≤ precision := Nat.div_le_self _ _
  unfold RecoverHeaderControlSetup.cost RecoverHeaderRulers.cost
  rw [Nat.size_pow]
  nlinarith

/-- At manuscript precision, setup is paid by the actual public word width.
This bound also covers an exponent of zero and all positive field widths. -/
theorem cost_six_le_width (chunkWidth lengthExponent wordWidth : ℕ)
    (chunkLarge : 3 ≤ chunkWidth) (lengthFits : lengthExponent ≤ chunkWidth)
    (wordFits : 6 * chunkWidth ≤ wordWidth) :
    RecoverHeaderControlSetup.cost (6*chunkWidth) lengthExponent wordWidth ≤ 6300 * (wordWidth + 1) := by
  have setupBound := cost_le_linear (6*chunkWidth) lengthExponent wordWidth (by omega) (by omega)
  omega

end IntegerMultBounds.Machine.RecoverHeaderControlBudget
