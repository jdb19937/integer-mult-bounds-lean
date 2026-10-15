module

public import IntegerMultBounds.MathlibTM2.Cost.CompactSharpBase
public import IntegerMultBounds.MathlibTM2.Fast.Round

/-! Actual rounded-output and square costs against the sharper multiplication budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

/-- The constant of the rounding stage. -/
noncomputable def compactSharpRndC (Tm cm cw cW : ℕ) : ℝ :=
  16384 * ssMulConst * (Tm + 1) * (cm : ℝ) ^ 2 + 16 * cw + 16 * cm + 8 * cW + 128

theorem compactSharp_rnd_C_nonneg (Tm cm cw cW : ℕ) : 0 ≤ compactSharpRndC Tm cm cw cW := by
  unfold compactSharpRndC; positivity

/-- **The rounding stage** (`roundStage_exec` at `b n`, `p n`, `S n`): at most
`compactSharpRndC Tm cm cw cW · S M(p)` steps for `1 ≤ m ≤ cm p`, `w ≤ cw p`, `W ≤ cW p`. -/
theorem compactSharp_rnd_stage_le (Tm cm cw cW : ℕ) :
    ∀ᶠ n in atTop, ∀ m w W : ℕ, 1 ≤ m → m ≤ cm * p n → w ≤ cw * p n → W ≤ cW * p n →
      (roundStageCost Tm m w (b n) (p n) W (S n) : ℝ) ≤
        compactSharpRndC Tm cm cw cW * ((S n : ℝ) * compactSharpMp n) := by
  filter_upwards [eventually_big] with n h m w W hm1 hm hw hW
  have h1 := roundStageCost_le Tm hm1 w (b n) (p n) W (S n)
  have h2 := compactSharp_mLogLog_le h hm1 hm
  have hpm := compactSharp_p_le_mp h
  have hm1' := compactSharp_one_le_mp h
  have hmp0 : 0 ≤ compactSharpMp n := compactSharp_mp_nonneg n
  have hp : (p n : ℝ) = 6 * b n := gr_p_eq n
  have hb0 : (0 : ℝ) ≤ b n := Nat.cast_nonneg _
  have hS1 : (1 : ℝ) ≤ S n := by
    have : 0 < S n := by
      unfold S
      exact Finset.prod_pos fun i _ => mt_s_pos h i
    exact_mod_cast this
  have hm' : (m : ℝ) ≤ cm * compactSharpMp n :=
    (show (m : ℝ) ≤ cm * p n by exact_mod_cast hm).trans
      (mul_le_mul_of_nonneg_left hpm (Nat.cast_nonneg _))
  have hw' : (w : ℝ) ≤ cw * compactSharpMp n :=
    (show (w : ℝ) ≤ cw * p n by exact_mod_cast hw).trans
      (mul_le_mul_of_nonneg_left hpm (Nat.cast_nonneg _))
  have hW' : (W : ℝ) ≤ cW * compactSharpMp n :=
    (show (W : ℝ) ≤ cW * p n by exact_mod_cast hW).trans
      (mul_le_mul_of_nonneg_left hpm (Nat.cast_nonneg _))
  have h1' : (roundStageCost Tm m w (b n) (p n) W (S n) : ℝ) ≤
      (S n : ℝ) * ((ssMulConst : ℝ) * ((Tm : ℝ) + 1) * (mLogLog m : ℝ) + 12 * w + 14 * m +
        12 * b n + 4 * p n + 6 * W + 58) + 4 := by exact_mod_cast h1
  clear h1
  have hκ0 : (0 : ℝ) ≤ (ssMulConst : ℝ) := Nat.cast_nonneg _
  unfold compactSharpRndC
  generalize (roundStageCost Tm m w (b n) (p n) W (S n) : ℝ) = R at h1' ⊢
  generalize (ssMulConst : ℝ) = κ at h1' hκ0 ⊢
  generalize (mLogLog m : ℝ) = L at h1' h2
  have hT0 : (0 : ℝ) ≤ (Tm : ℝ) + 1 := by positivity
  have hκT : 0 ≤ κ * ((Tm : ℝ) + 1) := mul_nonneg hκ0 hT0
  have h3 : κ * ((Tm : ℝ) + 1) * L ≤ κ * ((Tm : ℝ) + 1) * (16384 * (cm : ℝ) ^ 2 * compactSharpMp n) :=
    mul_le_mul_of_nonneg_left h2 hκT
  have h4 : κ * ((Tm : ℝ) + 1) * L + 12 * w + 14 * m + 12 * b n + 4 * p n + 6 * W + 58 ≤
      (16384 * κ * ((Tm : ℝ) + 1) * (cm : ℝ) ^ 2 + 12 * cw + 14 * cm + 6 * cW + 64) * compactSharpMp n := by
    have : (12 : ℝ) * b n + 4 * p n ≤ 6 * compactSharpMp n := by rw [hp] at hpm ⊢; linarith
    nlinarith
  have hS0 : (0 : ℝ) ≤ S n := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hS0
  have hpad : 0≤(4*(cw:ℝ)+2*cm+2*cW+60)*compactSharpMp n := by positivity
  have h6 : (4 : ℝ) ≤ 4 * ((S n : ℝ) * compactSharpMp n) := by nlinarith
  have hpadS := mul_nonneg hS0 hpad
  nlinarith

/-- **The square `S²`** (`rndSquare_exec` with `S < 2^ℓ`, `topN ℓ + 1 ≤ m`): at most
`compactSharpRndC Tm cm 0 0 · M(p)` steps for `1 ≤ ℓ ≤ m ≤ cm p`. -/
theorem compactSharp_rnd_square_le (Tm cm : ℕ) :
    ∀ᶠ n in atTop, ∀ ℓ' m : ℕ, 1 ≤ ℓ' → ℓ' ≤ m → m ≤ cm * p n →
      (((Tm + 773) * ssCostBound ℓ' + 164 * ℓ' + 463 + 8 * m + 8 : ℕ) : ℝ) ≤
        compactSharpRndC Tm cm 0 0 * compactSharpMp n := by
  filter_upwards [eventually_big] with n h ℓ' m hl hlm hm
  have h1 := ssMul_cost_le Tm hl
  have h2 := compactSharp_mLogLog_le h hl (hlm.trans hm)
  have hpm := compactSharp_p_le_mp h
  have hm1' := compactSharp_one_le_mp h
  have h1' : (((Tm + 773) * ssCostBound ℓ' + 164 * ℓ' + 463 + 8 * m + 8 : ℕ) : ℝ) ≤
      (ssMulConst : ℝ) * ((Tm : ℝ) + 1) * (mLogLog ℓ' : ℝ) + 8 * m + 8 := by
    have : (Tm + 773) * ssCostBound ℓ' + 164 * ℓ' + 463 + 8 * m + 8 ≤
        ssMulConst * (Tm + 1) * mLogLog ℓ' + 8 * m + 8 := by omega
    exact_mod_cast this
  clear h1
  have hm' : (m : ℝ) ≤ cm * compactSharpMp n :=
    (show (m : ℝ) ≤ cm * p n by exact_mod_cast hm).trans
      (mul_le_mul_of_nonneg_left hpm (Nat.cast_nonneg _))
  have hκ0 : (0 : ℝ) ≤ (ssMulConst : ℝ) := Nat.cast_nonneg _
  unfold compactSharpRndC
  generalize ((((Tm + 773) * ssCostBound ℓ' + 164 * ℓ' + 463 + 8 * m + 8 : ℕ) : ℝ)) = R at h1' ⊢
  generalize (ssMulConst : ℝ) = κ at h1' hκ0 ⊢
  generalize (mLogLog ℓ' : ℝ) = L at h1' h2
  have hT0 : (0 : ℝ) ≤ (Tm : ℝ) + 1 := by positivity
  have hκT : 0 ≤ κ * ((Tm : ℝ) + 1) := mul_nonneg hκ0 hT0
  have h3 : κ * ((Tm : ℝ) + 1) * L ≤ κ * ((Tm : ℝ) + 1) * (16384 * (cm : ℝ) ^ 2 * compactSharpMp n) :=
    mul_le_mul_of_nonneg_left h2 hκT
  push_cast
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
