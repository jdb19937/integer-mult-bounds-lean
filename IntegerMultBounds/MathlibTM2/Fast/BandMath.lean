module

public import IntegerMultBounds.MathlibTM2.Fast.BandStage
public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0Sizes

/-!
# The numeric facts of the banded `B̃₀` at the pipeline sizes

In the regime `Big n`, with the Gaussian width `α² = u` satisfying the small-gap conditions
`8p ≤ 2^u` and `u d ≤ p`, every axis has the numeric facts `BandAxisMath` of the band stage with
the Newton floor `β = 1/(32p)` (`band_axis_math`): the window matrix of the coefficient tables at
precision `5p` and width `8m` is within `2^-3p` of the phase-cell matrix, so it keeps the stage
invariant, and the band line map sends the unit ball into itself. The Newton conditions hold with
`4α²` steps (`band_prec`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.NLogN
open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Resampling.WeightTable (tableE tableD tableE_err tableD_spec)

noncomputable section

variable {n : ℕ}

theorem six_mul_le_two_pow (q : ℕ) (hq : 5 ≤ q) : 6 * q ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih => rw [pow_succ]; omega

/-- The coefficient numerators approximate the Gaussian weights within `2/2^P`. -/
theorem bandAZ_err (h : Big n) (i : Fin (d n)) (j : ZMod (s n i)) (k : ℤ) :
    |Mult.BandFactor.gv (5 * p n) (bandAZ n i j k) - Real.exp (normExp (s n i) (t n i)
      (alpha n : ℝ) j.val k)| ≤ 2 / 2 ^ (5 * p n) := by
  have hp13 := h.thirteen_le_p
  have hP : (0 : ℝ) < 2 ^ (5 * p n) := by positivity
  simp only [bandAZ, Mult.BandFactor.coefZ]
  split_ifs with hk
  · subst hk
    have e : normExp (s n i) (t n i) (alpha n : ℝ) (j.val : ℤ) 0 = 0 := by
      simp [normExp]
    rw [e, Real.exp_zero]
    simp only [Mult.BandFactor.gv]; push_cast
    rw [div_self hP.ne', sub_self, abs_zero]; positivity
  · have herr := tableE_err (s n i) (t n i) (alpha n) (5 * p n) (h.good.lt i) (by omega) j k
    simp only [Mult.BandFactor.gv]
    rw [show ((tableE (s n i) (t n i) (alpha n) (5 * p n) j k : ℤ) : ℝ) / 2 ^ (5 * p n) -
        Real.exp (normExp (s n i) (t n i) (alpha n : ℝ) j.val k) =
        ((tableE (s n i) (t n i) (alpha n) (5 * p n) j k : ℝ) -
          2 ^ (5 * p n) * Real.exp (normExp (s n i) (t n i) (alpha n : ℝ) j.val k)) / 2 ^ (5 * p n) by
      field_simp, abs_div, abs_of_pos hP]
    exact div_le_div_of_nonneg_right herr hP.le


/-- The Newton conditions with `4α²` steps. -/
theorem band_newton (h : Big n) (hwidth : 8 * p n ≤ 2 ^ (alpha n ^ 2)) :
    (1 - 1 / (32 * (p n : ℝ)) / 4 / 2) ^ (2 ^ (4 * (alpha n * alpha n))) ≤
      3 * (5 * (1 / 2 ^ (5 * p n) : ℝ)) / (1 / (32 * (p n : ℝ)) / 4) := by
  have hp64 := h.sixty_four_le_p
  obtain ⟨-, -, -, hK, -⟩ := h.newton_conditions
  have hlog : Nat.log 2 (p n) < alpha n ^ 2 :=
    Nat.log_lt_of_lt_pow (by omega) (by omega)
  have hlog6 : 6 ≤ Nat.log 2 (p n) := by
    have := Nat.log_mono_right (b := 2) hp64
    have e : Nat.log 2 64 = 6 := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.log_pow (by norm_num)]
    omega
  have hKle : Mult.Sizes.newtonK (p n) ≤ 4 * (alpha n * alpha n) := by
    unfold Mult.Sizes.newtonK; rw [← sq]; omega
  refine le_trans ?_ hK
  have hx0 : (0 : ℝ) ≤ 1 - 1 / (32 * (p n : ℝ)) / 4 / 2 := by
    have : 1 / (32 * (p n : ℝ)) / 4 / 2 ≤ 1 := by
      have : (64 : ℝ) ≤ p n := by exact_mod_cast hp64
      rw [div_div, div_div, div_le_one (by positivity)]; nlinarith
    linarith
  have hx1 : 1 - 1 / (32 * (p n : ℝ)) / 4 / 2 ≤ 1 := by
    have : 0 ≤ 1 / (32 * (p n : ℝ)) / 4 / 2 := by positivity
    linarith
  exact pow_le_pow_of_le_one hx0 hx1 (Nat.pow_le_pow_right (by norm_num) hKle)

/-- **The precision of the band** at the Newton floor `β = 1/(32p)`, for a record width `w`
with `(192p + 1) 2^(5p) < 2^(w-1)`. -/
theorem band_prec (h : Big n) (hwidth : 8 * p n ≤ 2 ^ (alpha n ^ 2)) {w : ℕ}
    (hw : (6 / (1 / (32 * (p n : ℝ))) + 1) * 2 ^ (5 * p n) < (2 : ℝ) ^ (w - 1)) :
    BandPrec n (1 / (32 * (p n : ℝ))) w := by
  obtain ⟨hβ, hβp, hηβ, -, -⟩ := h.newton_conditions
  exact ⟨hβ, hβp, hηβ, band_newton h hwidth, hw⟩

/-- **The numeric facts of every axis**, and the line map approximates `2^-α² ℬ₀` within `p²`
for every left inverse `J` of the exact normalized operator. -/
theorem band_axis_full (h : Big n) (hwidth : 8 * p n ≤ 2 ^ (alpha n ^ 2))
    (hbudget : ((alpha n : ℝ)) ^ 2 * (d n : ℝ) ≤ p n) (i : Fin (d n)) :
    BandAxisMath n (1 / (32 * (p n : ℝ))) i ∧
      ∀ J : (ZMod (s n i) → ℂ) →L[ℂ] (ZMod (s n i) → ℂ),
        J ∘L PhaseCellOperator.exact (s n i) (t n i) (alpha n : ℝ) = 1 →
        ApproxMap (p n) (bandA n i) (((2 : ℂ) ^ (alpha n * alpha n))⁻¹ •
          resampB₀ (s n i) (t n i) (alpha n : ℝ) J) ((p n : ℝ) ^ 2) := by
  have hp13 := h.thirteen_le_p
  have hp64 := h.sixty_four_le_p
  have hα2 := two_le_alpha h.1
  have hst := h.good.lt i
  have hα : (0 : ℝ) < alpha n := by have : (2 : ℝ) ≤ alpha n := by exact_mod_cast hα2
                                    linarith
  have hαu : ((alpha n : ℝ)) ^ 2 = ((alpha n ^ 2 : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨-, hθ, hgap, -⟩ := h.smallgap i
  set m := Mult.FastB0.fastWindow (p n) (alpha n)
  set wd := 8 * m
  have hm3 := Mult.FastB0.fastWindow_le_third hα2 hp13
  have hband : 16 * p n ≤ alpha n ^ 2 * wd ^ 2 := by
    have h1 := Mult.FastB0.fastWindow_sq (p n) (alpha n) (by omega)
    have h2 : (16 * p n : ℝ) ≤ ((alpha n ^ 2 * wd ^ 2 : ℕ) : ℝ) := by
      push_cast [wd]; nlinarith
    exact_mod_cast h2
  have hwd : (2 * wd + 1 : ℝ) ≤ 2 ^ p n := by
    have h1 : 2 * wd + 1 ≤ 2 ^ p n := by
      have : 2 * wd + 1 ≤ 6 * p n := by simp only [wd]; omega
      exact this.trans (six_mul_le_two_pow _ (by omega))
    exact_mod_cast h1
  set a : ZMod (s n i) → ℤ → ℝ := fun j k => Mult.BandFactor.gv (5 * p n) (bandAZ n i j k)
  set δ : ℝ := 2 / 2 ^ (5 * p n)
  set ε : ℝ := 1 / 2 ^ (3 * p n)
  have ha : ∀ j k, k.natAbs ≤ wd → |a j k - Real.exp (normExp (s n i) (t n i) (alpha n : ℝ) j.val k)|
      ≤ δ := fun j k _ => bandAZ_err h i j k
  have hεdef : (2 * wd + 1) * δ + 1 / (2 : ℝ) ^ (46 * p n) + 1 / (2 : ℝ) ^ (45 * p n) ≤ ε := by
    have := Mult.Sizes.window_eps_le (p n) wd (by omega) hwd
    exact this
  have hθpos : 0 < (t n i : ℝ) / s n i - 1 := (by positivity : (0 : ℝ) < 1 / (4 * (p n : ℝ))).trans_le hθ
  have hε : ∀ j, ∑ l, |NLogN.PhaseCellMatrix.windowMatrix (s n i) wd a j l -
      NLogN.PhaseCellMatrix.realMatrix (s n i) (t n i) (p n) (alpha n ^ 2) j l| ≤ ε := fun j =>
    (NLogN.PhaseCellMatrix.windowMatrix_close (s n i) (t n i) hst hα (p n) (alpha n ^ 2) (by omega)
      (by nlinarith) hαu hθpos hgap hbudget wd hband a δ ha j).trans hεdef
  obtain ⟨hε1, hprec, hsm, hfin⟩ := h.concreteB0P_conditions i ε (by positivity) le_rfl
  have hwidthR : 8 * p n ≤ 2 ^ (alpha n ^ 2) := hwidth
  have hinv := NLogN.PhaseCellMatrix.perturb_stageInv (s n i) (t n i) hst hα (p n) (alpha n ^ 2)
    (by omega) hwidthR hαu hθ hgap hbudget _ ε hε hε1
  obtain ⟨hβ, hβp, hηβ, hK, -⟩ := h.newton_conditions
  have hj : 4 * (p n : ℝ) ≤ 2 ^ (alpha n * alpha n) := by
    have : 4 * p n ≤ 2 ^ (alpha n * alpha n) := by rw [← sq]; omega
    exact_mod_cast this
  have hK' := band_newton h hwidth
  set df : ZMod (s n i) → ℝ := fun ℓ => (tableD (s n i) (t n i) (alpha n) (p n) ℓ : ℝ) / 2 ^ p n
  have hP : (0 : ℝ) < 2 ^ p n := by positivity
  have hrd : ∀ ℓ, rhoC (p n) (df ℓ : ℂ) = ((df ℓ : ℝ) : ℂ) := fun ℓ => by
    rw [Resampling.WindowSum.rhoC_real, mul_div_cancel₀ _ hP.ne', Resampling.NeumannWords.rho0_int]
  have hD := fun ℓ => tableD_spec (s n i) (t n i) (alpha n) (p n) hp13 (by omega) h.alpha_sq_le_p ℓ
  have hdf : ∀ ℓ, 2 ^ p n * ‖rhoC (p n) (df ℓ : ℂ) - (dPrime (s n i) (t n i) (alpha n : ℝ) ℓ : ℂ)‖ ≤ 2 := by
    intro ℓ
    rw [hrd, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : 2 ^ p n * |df ℓ - dPrime (s n i) (t n i) (alpha n : ℝ) ℓ| =
        |(tableD (s n i) (t n i) (alpha n) (p n) ℓ : ℝ) - 2 ^ p n * dPrime (s n i) (t n i) (alpha n : ℝ) ℓ| := by
      rw [← abs_of_pos hP, ← abs_mul, abs_of_pos hP]; congr 1; simp only [df]; field_simp
    rw [e]; exact (hD ℓ).1
  have hdf1 : ∀ ℓ, ‖rhoC (p n) (df ℓ : ℂ)‖ ≤ 1 := by
    intro ℓ
    rw [hrd, Complex.norm_real, Real.norm_eq_abs]
    have h0 : (0 : ℝ) ≤ tableD (s n i) (t n i) (alpha n) (p n) ℓ := by exact_mod_cast (hD ℓ).2.1
    have h1 : (tableD (s n i) (t n i) (alpha n) (p n) ℓ : ℝ) ≤ 2 ^ p n := by exact_mod_cast (hD ℓ).2.2
    simp only [df]
    rw [abs_of_nonneg (div_nonneg h0 hP.le), div_le_one hP]; exact h1
  have hspec := fun (J : (ZMod (s n i) → ℂ) →L[ℂ] (ZMod (s n i) → ℂ))
      (hJ : J ∘L PhaseCellOperator.exact (s n i) (t n i) (alpha n : ℝ) = 1) =>
    Mult.FastB0.concrete_resampB₀_specW hst hα (p n) (alpha n ^ 2) (alpha n * alpha n)
      (by omega) hwidthR hαu hθ hgap hbudget hj wd hband a δ ha ε hεdef hε1 (rdP (5 * p n))
      (1 / 2 ^ (5 * p n)) (rdP_err _) (rdP_zero _) _ hβ hβp hηβ (4 * (alpha n * alpha n)) hK' hprec
      hsm J hJ df hdf hdf1
  obtain ⟨J₀, -, hJ₀, -⟩ := PhaseCellDominance.selected_rounded_inverse (s n i) (t n i) hst hα (p n)
    (alpha n ^ 2) (by omega) hwidthR hαu hθ hgap hbudget
  refine ⟨⟨hinv, hprec, ?_, (hspec J₀ hJ₀).2⟩, fun J hJ v hv => ((hspec J hJ).1 v hv).trans hfin⟩
  have h0 : 0 ≤ 64 * (p n : ℝ) ^ 2 * ε := by positivity
  have h1 : (0 : ℝ) ≤ 2 / 2 ^ p n := by positivity
  have h2 : (0 : ℝ) ≤ 32 * (p n : ℝ) ^ 2 / (2 : ℝ) ^ (45 * p n) / 2 := by positivity
  linarith
end

theorem band_axis_math (h : Big n) (hwidth : 8 * p n ≤ 2 ^ (alpha n ^ 2))
    (hbudget : ((alpha n : ℝ)) ^ 2 * (d n : ℝ) ≤ p n) (i : Fin (d n)) :
    BandAxisMath n (1 / (32 * (p n : ℝ))) i := (band_axis_full h hwidth hbudget i).1

end IntegerMultBounds.MathlibTM2.Fast
