module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellB0
public import IntegerMultBounds.NLogN.PhaseCellBoundary

/-! The `B̃₀` interface for the small-gap inverse computed by real solves of
the rounded matrix. The rounded operator acts on complex vectors through the
real matrix on real and imaginary parts, so its inverse on `v` is assembled
from the two real solutions. Real solves within `e` of the exact ones,
followed by a normalization within `η`, give the pipeline interface for the
normalized factorization target `B₀ J / 2^j`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open ContinuousLinearMap

variable {s t : ℕ} [NeZero s] [NeZero t]

omit [NeZero t] in
/-- The rounded operator on a complex vector is the real matrix on its parts. -/
theorem rounded_parts (p u : ℕ) (xr xi : ZMod s → ℝ) :
    PhaseCellOperator.rounded s t p u (fun i => ⟨xr i, xi i⟩)=
      fun j => ⟨Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) xr j,
        Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) xi j⟩ := by
  rw [PhaseCellOperator.rounded_apply, ←PhaseCellMatrix.matrix_mulVec]
  funext j
  apply Complex.ext
  · simp [Matrix.mulVec, dotProduct, PhaseCellMatrix.realMatrix, Complex.re_sum]
  · simp [Matrix.mulVec, dotProduct, PhaseCellMatrix.realMatrix, Complex.im_sum]

omit [NeZero t] in
/-- An inverse of the rounded operator acts through exact real solves. -/
theorem inverse_parts (p u : ℕ) (L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hL : L ∘L PhaseCellOperator.rounded s t p u=1) (v : ZMod s → ℂ) (xr xi : ZMod s → ℝ)
    (hr : Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) xr=fun i => (v i).re)
    (hi : Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) xi=fun i => (v i).im) :
    L v=fun i => ⟨xr i, xi i⟩ := by
  have hv : PhaseCellOperator.rounded s t p u (fun i => ⟨xr i, xi i⟩)=v := by
    rw [rounded_parts, hr, hi]
  have h := congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f (fun i => ⟨xr i, xi i⟩)) hL
  simp only [comp_apply, hv] at h
  exact h

/-- Real solves within `e` give the small-gap `B̃₀` interface. -/
theorem banded_resampB₀_spec (p j : ℕ) {α : ℝ} (uu : ℕ)
    (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hL : L ∘L PhaseCellOperator.rounded s t p uu=1)
    (hJn : ‖J‖≤4*(p : ℝ)) (hj : 4*(p : ℝ)≤2^j) {δ₀ e η : ℝ} (he : 0≤e) (hη : 0≤η)
    (hdiff : ‖L-J‖≤δ₀)
    (hsmall : 2*e+η+δ₀/2≤1/2)
    (xr xi : (ZMod s → ℂ) → ZMod s → ℝ) (Jt : (ZMod s → ℂ) → ZMod s → ℂ)
    (hsolve : ∀ v : ZMod s → ℂ, ‖v‖≤1 → ∀ yr yi : ZMod s → ℝ,
      Matrix.mulVec (PhaseCellMatrix.realMatrix s t p uu) yr=(fun i => ((1/2 : ℂ)*v i).re) →
      Matrix.mulVec (PhaseCellMatrix.realMatrix s t p uu) yi=(fun i => ((1/2 : ℂ)*v i).im) →
      ∀ i, |xr v i-yr i|≤e ∧ |xi v i-yi i|≤e)
    (hexist : ∀ b : ZMod s → ℝ, ∃ y, Matrix.mulVec (PhaseCellMatrix.realMatrix s t p uu) y=b)
    (hJt : ∀ v i, ‖Jt v i-((2 : ℂ)^j)⁻¹*⟨xr v i, xi v i⟩‖≤η)
    (df : ZMod s → ℝ) (hdf : ∀ ℓ, 2^p*‖rhoC p (df ℓ : ℂ)-(dPrime s t α ℓ : ℂ)‖≤2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖≤1) :
    ApproxMap p (resampB₀Of (t := t) p Jt df) (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
        (6+2^p*((2*e+η)+δ₀/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖≤1 → ‖resampB₀Of (t := t) p Jt df w‖≤1 := by
  refine smallgap_resampB₀_spec p j J L hJn hj hdiff (by linarith) Jt (fun v hv => ?_) df hdf hdf1
  obtain ⟨yr, hyr⟩ := hexist fun i => ((1/2 : ℂ)*v i).re
  obtain ⟨yi, hyi⟩ := hexist fun i => ((1/2 : ℂ)*v i).im
  have hLv := inverse_parts p uu L hL ((1/2 : ℂ) • v) yr yi
    (by rw [hyr]; rfl) (by rw [hyi]; rfl)
  have hc : ‖((2 : ℂ)^j)⁻¹‖≤1 := by
    rw [norm_inv, norm_pow, RCLike.norm_two]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [hLv, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have hs := hsolve v hv yr yi hyr hyi i
  have hpart : ‖(⟨xr v i, xi v i⟩ : ℂ)-⟨yr i, yi i⟩‖≤2*e := by
    have : (⟨xr v i, xi v i⟩ : ℂ)-⟨yr i, yi i⟩=⟨xr v i-yr i, xi v i-yi i⟩ := by
      apply Complex.ext <;> simp
    rw [this]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only
    linarith [hs.1, hs.2]
  calc ‖Jt v i-(((2 : ℂ)^j)⁻¹ • fun i => (⟨yr i, yi i⟩ : ℂ)) i‖
      =‖(Jt v i-((2 : ℂ)^j)⁻¹*⟨xr v i, xi v i⟩)+
          ((2 : ℂ)^j)⁻¹*((⟨xr v i, xi v i⟩ : ℂ)-⟨yr i, yi i⟩)‖ := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring_nf
    _≤η+1*(2*e) := by
        refine (norm_add_le _ _).trans (add_le_add (hJt v i) ?_)
        rw [norm_mul]
        exact mul_le_mul hc hpart (norm_nonneg _) zero_le_one
    _=2*e+η := by ring

end IntegerMultBounds.MathlibTM2.Mult.FastB0
