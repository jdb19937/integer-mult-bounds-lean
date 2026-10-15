module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Cost.CompactLogGrowth

/-! Actual fixed-point multiplication costs with dyadic constants and sharper polylog absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

/-- A sharper analytic budget for the unchanged executable multiplier. -/
def compactSharpMp (n : ℕ) : ℝ := (p n:ℝ)^(1+(2^5:ℝ)⁻¹)

theorem compactSharp_mp_eq (n : ℕ) : compactSharpMp n=(p n:ℝ)^(33/32:ℝ) := by
  norm_num [compactSharpMp]

theorem compactSharp_mp_nonneg (n : ℕ) : 0≤compactSharpMp n := by
  unfold compactSharpMp
  positivity

theorem compactSharp_p_le_mp {n : ℕ} (h : Big n) : (p n:ℝ)≤compactSharpMp n := by
  rw [compactSharp_mp_eq]
  calc (p n:ℝ)=(p n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (mt_one_le_p h) (by norm_num)

theorem compactSharp_one_le_mp {n : ℕ} (h : Big n) : (1:ℝ)≤compactSharpMp n :=
  (mt_one_le_p h).trans (compactSharp_p_le_mp h)

/-- `mLogLog w ≤ 16384 cw² M(p)` for `1 ≤ w ≤ cw p`. -/
theorem compactSharp_mLogLog_le {n w cw : ℕ} (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (mLogLog w : ℝ) ≤ 16384 * (cw : ℝ) ^ 2 * compactSharpMp n := by
  have h1 := compact_mLogLog_le hw
  have hcw : 1 ≤ cw := by
    rcases Nat.eq_zero_or_pos cw with rfl | hc
    · simp at hwc; omega
    · exact hc
  have hcw' : (1 : ℝ) ≤ cw := by exact_mod_cast hcw
  have hp := mt_p_pos h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have h2 : (w : ℝ) ^ (33 / 32 : ℝ) ≤ ((cw : ℝ) * p n) ^ (33 / 32 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hw' (by norm_num)
  have h3 : ((cw : ℝ) * p n) ^ (33 / 32 : ℝ) = (cw : ℝ) ^ (33 / 32 : ℝ) * (p n : ℝ) ^ (33 / 32 : ℝ) :=
    Real.mul_rpow (Nat.cast_nonneg _) hp.le
  have h4 : (cw : ℝ) ^ (33 / 32 : ℝ) ≤ (cw : ℝ) ^ 2 := by
    rw [show ((cw : ℝ) ^ 2) = (cw : ℝ) ^ (2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le hcw' (by norm_num)
  have h5 : (0 : ℝ) ≤ (p n : ℝ) ^ (33 / 32 : ℝ) := Real.rpow_nonneg hp.le _
  have e : (mLogLog w : ℝ) =
      ((w * (Nat.log 2 w + 1) * (Nat.log 2 (Nat.log 2 w) + 1) : ℕ) : ℝ) := rfl
  rw [e, compactSharp_mp_eq]
  calc _ ≤ 16384 * (w : ℝ) ^ (33 / 32 : ℝ) := h1
    _ ≤ 16384 * ((cw : ℝ) ^ 2 * (p n : ℝ) ^ (33 / 32 : ℝ)) := by
        rw [h3] at h2
        have := mul_le_mul_of_nonneg_right h4 h5
        nlinarith
    _ = 16384 * (cw : ℝ) ^ 2 * (p n : ℝ) ^ (33 / 32 : ℝ) := by ring

/-- The constant of one complex fixed-point product at width `w ≤ cw p` on a host of `Tm`
stacks, against `M(p)`. -/
noncomputable def compactSharpCM (Tm cw : ℕ) : ℝ :=
  65536 * ssMulConst * (Tm + 1) * (cw : ℝ) ^ 2 + 256 * cw + 128

theorem compactSharp_CM_nonneg (Tm cw : ℕ) : 0 ≤ compactSharpCM Tm cw := by unfold compactSharpCM; positivity

/-- `cmulCost Tm w ≤ compactSharpCM Tm cw · M(p)`. -/
theorem compactSharp_cmul_le {n w cw : ℕ} (Tm : ℕ) (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (cmulCost Tm w : ℝ) ≤ compactSharpCM Tm cw * compactSharpMp n := by
  have h1 := compactSharp_mLogLog_le h hw hwc
  have hm1 := compactSharp_one_le_mp h
  have hpm := compactSharp_p_le_mp h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwm : (w : ℝ) ≤ cw * compactSharpMp n := hw'.trans (mul_le_mul_of_nonneg_left hpm hcw)
  have hS : (0 : ℝ) ≤ ssMulConst * ((Tm : ℝ) + 1) := by positivity
  unfold cmulCost compactSharpCM
  push_cast
  have h2 := mul_le_mul_of_nonneg_left h1 hS
  have hmp0 : 0 ≤ compactSharpMp n := compactSharp_mp_nonneg n
  have hcw2 : (0 : ℝ) ≤ (cw : ℝ) ^ 2 * compactSharpMp n := by positivity
  nlinarith

/-- `rmulCost Tm w ≤ compactSharpCM Tm cw · M(p)`. -/
theorem compactSharp_rmul_le {n w cw : ℕ} (Tm : ℕ) (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (rmulCost Tm w : ℝ) ≤ compactSharpCM Tm cw * compactSharpMp n := by
  have h1 := compactSharp_mLogLog_le h hw hwc
  have hm1 := compactSharp_one_le_mp h
  have hpm := compactSharp_p_le_mp h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwm : (w : ℝ) ≤ cw * compactSharpMp n := hw'.trans (mul_le_mul_of_nonneg_left hpm hcw)
  have hS : (0 : ℝ) ≤ ssMulConst * ((Tm : ℝ) + 1) := by positivity
  unfold rmulCost compactSharpCM
  push_cast
  have h2 := mul_le_mul_of_nonneg_left h1 hS
  have hmp0 : 0 ≤ compactSharpMp n := compactSharp_mp_nonneg n
  have hcw2 : (0 : ℝ) ≤ (cw : ℝ) ^ 2 * compactSharpMp n := by positivity
  nlinarith

end
end IntegerMultBounds.MathlibTM2.Cost
