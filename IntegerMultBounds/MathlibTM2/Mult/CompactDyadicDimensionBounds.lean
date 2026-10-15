module

public import IntegerMultBounds.MathlibTM2.Mult.CompactDyadicDimensionSizes

/-! Coarse upper growth bounds for the candidate dyadic dimension.
The upper growth power eight is distinct from the exact root degree sixty-four,
the input power nine, and the available lower size cap seven. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactDyadicDimensionBounds

open CompactDyadicDimensionSizes

/-- A coarse growth exponent, not the reciprocal of the real dimension exponent. -/
def upperPower : ℕ := 8

theorem lt_dimension_succ_pow (b : ℕ) : b < (dimension b+1)^upperPower := by
  by_contra h
  have hb : (dimension b+1)^8≤b := Nat.le_of_not_gt h
  have hp := Nat.pow_le_pow_left hb 9
  have hroot := CompactDyadicDimensionSizes.lt_dimension_succ_pow b
  have hmono : (dimension b+1)^64≤(dimension b+1)^72 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  rw [←pow_mul] at hp
  norm_num only [Nat.mul] at hp
  omega

/-- The old coarse upper estimate for `p=6b` survives the change of dimension. -/
theorem six_mul_lt_pow {b : ℕ} (hb : 1≤b) : 6*b < (12*dimension b)^upperPower := by
  have hd := one_le_dimension hb
  have hroot := lt_dimension_succ_pow b
  have hstep : (dimension b+1)^8≤(2*dimension b)^8 :=
    Nat.pow_le_pow_left (by omega) 8
  calc
    6*b < 6*(dimension b+1)^8 := Nat.mul_lt_mul_of_pos_left hroot (by decide)
    _ ≤ 6*(2*dimension b)^8 := Nat.mul_le_mul_left _ hstep
    _ ≤ (6*(2*dimension b))^8 := Sizes.mul_pow_le_mul_pow (by decide) 6 _
    _ = (12*dimension b)^upperPower := by unfold upperPower; congr 1; ring

/-- The real dimension sandwich retains the old constants for `p=6b`. -/
theorem six_mul_rpow_bounds {b : ℕ} (hb : 1≤b) :
    (6*(b:ℝ))^epsilon/12 ≤ dimension b ∧
      (dimension b:ℝ) ≤ (6*(b:ℝ))^epsilon := by
  have he : (0:ℝ)≤epsilon := by norm_num [epsilon]
  have hbounds := dimension_rpow_bounds hb
  have hnonneg : (0:ℝ)≤(b:ℝ)^epsilon := by positivity
  have h6 : (6:ℝ)^epsilon≤6 := Real.rpow_le_self_of_one_le (by norm_num)
    (by norm_num [epsilon])
  constructor
  · have hscale : (6*(b:ℝ))^epsilon≤6*(b:ℝ)^epsilon := by
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg b)]
      exact mul_le_mul_of_nonneg_right h6 hnonneg
    linarith [hbounds.1]
  · exact hbounds.2.trans (Real.rpow_le_rpow (Nat.cast_nonneg b) (by nlinarith) he)

end IntegerMultBounds.MathlibTM2.Mult.CompactDyadicDimensionBounds
