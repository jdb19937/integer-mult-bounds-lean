module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom

/-! Independent size arithmetic for the candidate exponent `9/64`.
This file does not change the multiplier's executable parameters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactDyadicDimensionSizes

open Filter

noncomputable def epsilon : ℝ := 9 / 64

def dimension (b : ℕ) : ℕ := Sizes.iroot 64 (b^9)

def d (n : ℕ) : ℕ := dimension (Sizes.b n)

theorem dimension_pow_le (b : ℕ) : dimension b ^ 64 ≤ b^9 :=
  Sizes.iroot_pow_le (by decide) _

theorem lt_dimension_succ_pow (b : ℕ) : b^9 < (dimension b+1)^64 :=
  Sizes.lt_succ_iroot_pow (by decide) _

theorem le_dimension_iff {D b : ℕ} : D ≤ dimension b ↔ D^64 ≤ b^9 :=
  Sizes.le_iroot_iff (by decide)

theorem one_le_dimension {b : ℕ} (hb : 1≤b) : 1≤dimension b :=
  Sizes.one_le_iroot (by decide) (one_le_pow₀ hb)

theorem dimension_seventh_le (b : ℕ) : dimension b ^ 7 ≤ b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have h := dimension_pow_le 0
    have hz : dimension 0 = 0 := by simpa using h
    simp [hz]
  · exact CompactDyadicRootRoom.seventh_power_le hb (dimension_pow_le b)

theorem dimension_le (b : ℕ) : dimension b ≤ b :=
  (Nat.le_self_pow (by decide : 7≠0) _).trans (dimension_seventh_le b)

theorem dimension_eq_floor (b : ℕ) : dimension b = ⌊(b : ℝ)^epsilon⌋₊ := by
  rw [dimension, Sizes.iroot_eq_floor (by decide)]
  push_cast
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg b)]
  norm_num [epsilon]

theorem dimension_rpow_bounds {b : ℕ} (hb : 1≤b) :
    (b : ℝ)^epsilon / 2 ≤ dimension b ∧ (dimension b : ℝ) ≤ (b : ℝ)^epsilon := by
  have hfloor : (dimension b : ℝ) ≤ (b : ℝ)^epsilon ∧
      (b : ℝ)^epsilon < (dimension b : ℝ)+1 := by
    exact (Nat.floor_eq_iff (by positivity)).mp (dimension_eq_floor b).symm
  have hd : (1:ℝ)≤dimension b := by exact_mod_cast one_le_dimension hb
  constructor
  · linarith [hfloor.2]
  · exact hfloor.1

theorem tendsto_dimension : Tendsto dimension atTop atTop := by
  apply tendsto_atTop.2
  intro D
  filter_upwards [eventually_ge_atTop (D^64)] with b hb
  exact le_dimension_iff.mpr (hb.trans (Nat.le_self_pow (by decide : 9≠0) b))

theorem tendsto_d : Tendsto d atTop atTop := tendsto_dimension.comp Sizes.tendsto_b

theorem d_pow_le (n : ℕ) : d n ^ 64 ≤ Sizes.b n ^ 9 := dimension_pow_le _

theorem d_seventh_le (n : ℕ) : d n ^ 7 ≤ Sizes.b n := dimension_seventh_le _

theorem d_le_b (n : ℕ) : d n ≤ Sizes.b n := dimension_le _

theorem d_eq_floor (n : ℕ) : d n = ⌊(Sizes.b n : ℝ)^epsilon⌋₊ := dimension_eq_floor _

theorem d_rpow_bounds {n : ℕ} (hn : 2≤n) :
    (Sizes.b n : ℝ)^epsilon / 2 ≤ d n ∧ (d n : ℝ) ≤ (Sizes.b n : ℝ)^epsilon :=
  dimension_rpow_bounds (Sizes.one_le_b hn)

end IntegerMultBounds.MathlibTM2.Mult.CompactDyadicDimensionSizes
