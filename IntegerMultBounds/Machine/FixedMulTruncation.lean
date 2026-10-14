module

public import IntegerMultBounds.Machine.FixedMulValue

/-! Generic signed semantics of the actual fixed-point multiplier. Operand
bounds and dropped precision are independent: full numerator products use zero
drop, and later scaling drops the requested places after complex sums have
been formed. Only centered output representability is required. -/

@[expose] public section
namespace IntegerMultBounds.Machine.FixedMulTruncation
open TwosComplement (signed signed_negWord)
open Counter (value)
open FixedMul (result padProd mag)

/-- Any nonnegative residue below the sign threshold decodes literally. -/
theorem signed_eq_value_of_small (bits : List Bool) (nonempty : bits≠[])
    (small : (value bits : ℤ)<2^(bits.length-1)) : signed bits=value bits := by
  unfold signed
  split_ifs with topSet
  · have split := TwosComplement.value_dropLast bits nonempty
    rw [←TwosComplement.getLastD_eq bits nonempty,topSet] at split
    simp only [BinaryAdd.bitValue,ite_true,mul_one] at split
    have splitInteger : (value bits : ℤ)=value bits.dropLast+2^(bits.length-1) := by exact_mod_cast split
    have lower : (0 : ℤ)≤value bits.dropLast := by positivity
    omega
  · simp

/-- The physically constructed unsigned product is the exact signed-product
magnitude whenever both original centered words can be negated. -/
theorem magnitude_value (left right : List Bool) (width : ℕ)
    (leftNonempty : left≠[]) (rightNonempty : right≠[])
    (leftNotMinimum : signed left≠-(2 : ℤ)^(left.length-1))
    (rightNotMinimum : signed right≠-(2 : ℤ)^(right.length-1)) :
    (value (padProd left right width) : ℤ)=|signed left*signed right| := by
  unfold padProd
  rw [TwosComplement.value_append,TwosComplement.value_replicate_false,mul_zero,add_zero,
    BinaryMultiply.horner_value,abs_mul]
  push_cast
  rw [FixedMul.value_mag left leftNonempty leftNotMinimum,FixedMul.value_mag right rightNonempty rightNotMinimum]

/-- Decoupling operand scale from dropped precision permits exact products
and rounding only after complex numerator sums have actually been formed. -/
theorem field_value (left right : List Bool) (dropPrecision width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (widthPositive : 1≤width) (dropFits : dropPrecision≤width)
    (leftNotMinimum : signed left≠-(2 : ℤ)^(left.length-1))
    (rightNotMinimum : signed right≠-(2 : ℤ)^(right.length-1))
    (outputFits : |signed left*signed right|/2^dropPrecision<(2 : ℤ)^(width-1)) :
    (value (Gather.field (padProd left right width) dropPrecision width) : ℤ)=
      |signed left*signed right|/2^dropPrecision := by
  have leftNonempty : left≠[] := by intro empty; rw [empty] at leftWidth; simp at leftWidth; omega
  have rightNonempty : right≠[] := by intro empty; rw [empty] at rightWidth; simp at rightWidth; omega
  have magnitude := magnitude_value left right width leftNonempty rightNonempty leftNotMinimum rightNotMinimum
  have paddedLength := FixedMul.padProd_length left right width leftWidth rightWidth
  rw [FixedMul.value_field_middle _ _ _ (by omega)]
  have quotient : ((value (padProd left right width)/2^dropPrecision : ℕ) : ℤ)=
      |signed left*signed right|/2^dropPrecision := by
    push_cast
    rw [magnitude]
  have wholeThreshold : (2 : ℤ)^(width-1)≤2^width := pow_le_pow_right₀ (by norm_num) (by omega)
  have quotientFits : value (padProd left right width)/2^dropPrecision<2^width := by
    exact_mod_cast (quotient ▸ outputFits.trans_le wholeThreshold)
  rw [Nat.mod_eq_of_lt quotientFits]
  exact quotient

/-- Actual result bits represent truncation toward zero whenever the result
fits the centered width. This is independent of the operand scale used by
chirp arithmetic, and includes dropping zero places for exact products. -/
theorem signed_result_of_fits (left right : List Bool) (dropPrecision width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (widthPositive : 1≤width) (dropFits : dropPrecision≤width)
    (leftNotMinimum : signed left≠-(2 : ℤ)^(left.length-1))
    (rightNotMinimum : signed right≠-(2 : ℤ)^(right.length-1))
    (outputFits : |signed left*signed right|/2^dropPrecision<(2 : ℤ)^(width-1)) :
    signed (result left right dropPrecision width)=(signed left*signed right).tdiv (2^dropPrecision) := by
  have leftNonempty : left≠[] := by intro empty; rw [empty] at leftWidth; simp at leftWidth; omega
  have rightNonempty : right≠[] := by intro empty; rw [empty] at rightWidth; simp at rightWidth; omega
  let magnitudeBits := Gather.field (padProd left right width) dropPrecision width
  have magnitudeLength : magnitudeBits.length=width := Gather.field_length _ _ _
  have magnitudeNonempty : magnitudeBits≠[] := by intro empty; rw [empty] at magnitudeLength; simp at magnitudeLength; omega
  have magnitudeValue := field_value left right dropPrecision width leftWidth rightWidth widthPositive dropFits
    leftNotMinimum rightNotMinimum outputFits
  have magnitudeSigned : signed magnitudeBits=|signed left*signed right|/2^dropPrecision := by
    rw [signed_eq_value_of_small magnitudeBits magnitudeNonempty (by
      change (value (Gather.field (padProd left right width) dropPrecision width) : ℤ)<2^(magnitudeBits.length-1)
      rw [magnitudeLength,magnitudeValue]
      exact outputFits)]
    exact magnitudeValue
  have magnitudeNotMinimum : signed magnitudeBits≠-(2 : ℤ)^(magnitudeBits.length-1) := by
    rw [magnitudeSigned,magnitudeLength]
    have nonnegative : (0 : ℤ)≤|signed left*signed right|/2^dropPrecision := by positivity
    have thresholdPositive : (0 : ℤ)<2^(width-1) := by positivity
    omega
  unfold result
  have leftSign := FixedMul.top_eq_false_iff left leftNonempty
  have rightSign := FixedMul.top_eq_false_iff right rightNonempty
  cases leftTop : left.getLastD false <;> cases rightTop : right.getLastD false <;>
    simp only [Bool.false_eq_true,Bool.true_eq_false,↓reduceIte] <;>
    rw [leftTop] at leftSign <;> rw [rightTop] at rightSign
  · have leftNonnegative : 0≤signed left := leftSign.mp rfl
    have rightNonnegative : 0≤signed right := rightSign.mp rfl
    rw [magnitudeSigned,abs_of_nonneg (mul_nonneg leftNonnegative rightNonnegative),
      Int.tdiv_eq_ediv_of_nonneg (mul_nonneg leftNonnegative rightNonnegative)]
  · have leftNonnegative : 0≤signed left := leftSign.mp rfl
    have rightNegative : signed right<0 := lt_of_not_ge (fun nonnegative => Bool.noConfusion (rightSign.mpr nonnegative))
    rw [signed_negWord _ magnitudeNonempty magnitudeNotMinimum,magnitudeSigned,abs_of_nonpos (by nlinarith)]
    have signedProduct : signed left*signed right = -(-(signed left*signed right)) := (neg_neg _).symm
    conv_rhs => rw [signedProduct,Int.neg_tdiv,Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]
  · have leftNegative : signed left<0 := lt_of_not_ge (fun nonnegative => Bool.noConfusion (leftSign.mpr nonnegative))
    have rightNonnegative : 0≤signed right := rightSign.mp rfl
    rw [signed_negWord _ magnitudeNonempty magnitudeNotMinimum,magnitudeSigned,abs_of_nonpos (by nlinarith)]
    have signedProduct : signed left*signed right = -(-(signed left*signed right)) := (neg_neg _).symm
    conv_rhs => rw [signedProduct,Int.neg_tdiv,Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]
  · have leftNegative : signed left<0 := lt_of_not_ge (fun nonnegative => Bool.noConfusion (leftSign.mpr nonnegative))
    have rightNegative : signed right<0 := lt_of_not_ge (fun nonnegative => Bool.noConfusion (rightSign.mpr nonnegative))
    rw [magnitudeSigned,abs_of_nonneg (by nlinarith),Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]

end IntegerMultBounds.Machine.FixedMulTruncation
