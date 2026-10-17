module

public import IntegerMultBounds.Resampling.TabledMaps
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! `B̃₀ = D̃' J̃ C` for any computed inverse `J̃`: a computed inverse that keeps the unit
disk and approximates `J (v/2)` within a scaled error gives the source-error interface of
`B̃₀`, so the banded solve plugs into the source-error theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.TabledMaps (diagW diagW_err)
open ContinuousLinearMap

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- `B̃₀` built from a supplied computed inverse. -/
noncomputable def resampB₀Of (p : ℕ) (Jt : (ZMod s → ℂ) → ZMod s → ℂ) (df : ZMod s → ℝ)
    (w : ZMod t → ℂ) : ZMod s → ℂ :=
  diagW p df (Jt (rowSelect s t w))

/-- Any computed inverse within `εJ` of `J (v/2)` that keeps the unit disk gives the
pipeline's `B̃₀` interface with error `6 + εJ`. -/
theorem resampB₀Of_spec {p : ℕ} (Jt : (ZMod s → ℂ) → ZMod s → ℂ) (df : ZMod s → ℝ)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} {εJ : ℝ}
    (hJt : ∀ v : ZMod s → ℂ, ‖v‖ ≤ 1 →
      ‖Jt v‖ ≤ 1 ∧ 2 ^ p * ‖Jt v - J ((1 / 2 : ℂ) • v)‖ ≤ εJ)
    (hdf : ∀ ℓ, 2 ^ p * ‖rhoC p (df ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖ ≤ 1) :
    ApproxMap p (resampB₀Of (t := t) p Jt df) (resampB₀ s t α J) (6 + εJ) ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀Of (t := t) p Jt df w‖ ≤ 1 := by
  refine ⟨approxMap_of_pointwise fun w hw ℓ => ?_, fun w hw => ?_⟩
  · set v := rowSelect s t w
    have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans hw
    set y := Jt v
    obtain ⟨hy1, hyJ⟩ := hJt v hv1
    have hB : resampB₀ s t α J w ℓ = (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ := by
      rw [resampB₀_apply, map_smul, Pi.smul_apply, smul_eq_mul]; ring
    have hBN : resampB₀Of (t := t) p Jt df w ℓ = diagW p df y ℓ := rfl
    rw [hB, hBN]
    have hD := diagW_err (t := t) (α := α) p df (hy1.trans one_le_two) ℓ (hdf ℓ)
    have hJℓ : 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ εJ :=
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (y - J ((1 / 2 : ℂ) • v)) ℓ)
        (by positivity)).trans hyJ
    have hd1 : ‖(dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
      exact dPrime_le_one ℓ
    have hsplit : diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ =
        (diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
          (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ) := by ring
    rw [hsplit]
    calc 2 ^ p * ‖(diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
          (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ)‖
        ≤ 2 ^ p * (‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
            ‖(dPrime s t α ℓ : ℂ)‖ * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by
          gcongr
          rw [← norm_mul]
          exact norm_add_le _ _
      _ = 2 ^ p * ‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
            ‖(dPrime s t α ℓ : ℂ)‖ * (2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by ring
      _ ≤ 6 + 1 * εJ := by gcongr
      _ = 6 + εJ := by ring
  · have hv1 : ‖rowSelect s t w‖ ≤ 1 := (norm_rowSelect_le _).trans hw
    have hy := (hJt _ hv1).1
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro ℓ
    unfold resampB₀Of diagW
    refine (norm_rhoC_le p _).trans ?_
    rw [norm_mul]
    calc ‖rhoC p (df ℓ : ℂ)‖ * ‖Jt (rowSelect s t w) ℓ‖ ≤ 1 * 1 :=
          mul_le_mul (hdf1 ℓ) ((norm_le_pi_norm _ ℓ).trans hy) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The normalized target of a small-gap inverse: `B₀ (J/2^j) = B₀ J / 2^j`. -/
theorem resampB₀_smul (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (c : ℂ) :
    resampB₀ s t α (c • J) = c • resampB₀ s t α J := by
  unfold resampB₀
  ext w ℓ
  simp only [smul_apply, comp_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  ring

end IntegerMultBounds.MathlibTM2.Mult.FastB0
