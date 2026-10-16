module

public import IntegerMultBounds.MathlibTM2.Mult.BandedB0
public import IntegerMultBounds.NLogN.PhaseCellBandSolve
public import IntegerMultBounds.NLogN.ToeplitzLocal

/-! The concrete small-gap `B̃₀` line map. The inverse is computed by the
rounded band solve of the rounded matrix on the real and imaginary parts of
`v/2`, scaled by `2^-j` and rounded to the `p`-grid. Under explicit precision
conditions this map satisfies the pipeline interface for the normalized
factorization target `B₀ J / 2^j`, for the exact inverse `J` of `N`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open ContinuousLinearMap Finset

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- The concrete computed inverse: two rounded band solves, scaled and rounded. -/
noncomputable def bandJt (p u j : ℕ) (rd : ℝ → ℝ) (v : ZMod s → ℂ) (i : ZMod s) : ℂ :=
  rhoC p (((2 : ℂ)^j)⁻¹*⟨SchurDominance.bandSolve rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).re) i,
    SchurDominance.bandSolve rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).im) i⟩)

theorem concrete_resampB₀_spec (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u j : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) (hj : 4*(p : ℝ)≤2^j)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (hprec : 128*p*(s : ℝ)^2*η≤1)
    (hsmall : 2*(2700*(s : ℝ)^2*(p : ℝ)^2*η)+2/2^p+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2≤1/2)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α=1)
    (df : ZMod s → ℝ) (hdf : ∀ ℓ, 2^p*‖rhoC p (df ℓ : ℂ)-(dPrime s t α ℓ : ℂ)‖≤2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖≤1) :
    ApproxMap p (resampB₀Of (t := t) p (bandJt (s := s) (t := t) p u j rd) df)
        (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
        (6+2^p*((2*(2700*(s : ℝ)^2*(p : ℝ)^2*η)+2/2^p)+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖≤1 → ‖resampB₀Of (t := t) p (bandJt (s := s) (t := t) p u j rd) df w‖≤1 := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  obtain ⟨J0, L, hJ0N, hNJ0, hJ0n, hLH, -, -, hdiff⟩ :=
    PhaseCellDominance.selected_rounded_inverse s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hJeq : J=J0 := by
    refine ContinuousLinearMap.ext fun x => ?_
    have e1 : PhaseCellOperator.exact s t α (J0 x)=x := by
      simpa using congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f x) hNJ0
    have e2 : J (PhaseCellOperator.exact s t α (J0 x))=J0 x := by
      simpa using congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f (J0 x)) hJ
    rw [←e2, e1]
  subst hJeq
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA := PhaseCellMatrix.matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  obtain ⟨R, hR⟩ := SchurDominance.exists_solver _ _ _ hμ hA
  have hexist : ∀ b : ZMod s → ℝ, ∃ y, Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) y=b :=
    fun b => ⟨R b, funext fun i => hR b i (mem_univ i)⟩
  have hhalf : ∀ v : ZMod s → ℂ, ‖v‖≤1 → ∀ i, |((1/2 : ℂ)*v i).re|≤1/2 ∧ |((1/2 : ℂ)*v i).im|≤1/2 := by
    intro v hv i
    have hvi : ‖v i‖≤1 := (norm_le_pi_norm v i).trans hv
    have hn : ‖(1/2 : ℂ)*v i‖≤1/2 := by
      rw [norm_mul, norm_div, norm_one, RCLike.norm_two]; linarith
    exact ⟨(Complex.abs_re_le_norm _).trans hn, (Complex.abs_im_le_norm _).trans hn⟩
  refine banded_resampB₀_spec p j u J L hLH hJ0n hj (by positivity) (by positivity) hdiff
    (by linarith)
    (fun v => SchurDominance.bandSolve rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).re))
    (fun v => SchurDominance.bandSolve rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).im))
    (bandJt (s := s) (t := t) p u j rd) ?_ hexist ?_ df hdf hdf1
  · intro v hv yr yi hyr hyi i
    exact ⟨PhaseCellMatrix.bandSolve_actual s t hst hα p u hp hwidth hαu hθ hgap hbudget rd η hrd
        hrd0 hprec yr _ hyr (fun k => (hhalf v hv k).1) i,
      PhaseCellMatrix.bandSolve_actual s t hst hα p u hp hwidth hαu hθ hgap hbudget rd η hrd
        hrd0 hprec yi _ hyi (fun k => (hhalf v hv k).2) i⟩
  · intro v i
    unfold bandJt
    exact (norm_rhoC_sub_le_two p _)

/-- The machine-faithful computed inverse (rounded products, stored reciprocals). -/
noncomputable def bandJtM (p u j : ℕ) (rd : ℝ → ℝ) (v : ZMod s → ℂ) (i : ZMod s) : ℂ :=
  rhoC p (((2 : ℂ)^j)⁻¹*⟨SchurDominance.bandSolveM rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).re) i,
    SchurDominance.bandSolveM rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).im) i⟩)

theorem concrete_resampB₀_specM (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u j : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) (hj : 4*(p : ℝ)≤2^j)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (hprec : 2^16*(p : ℝ)^2*(s : ℝ)^2*η≤1)
    (hsmall : 2*(62000*(p : ℝ)^3*(s : ℝ)^2*η)+2/2^p+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2≤1/2)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α=1)
    (df : ZMod s → ℝ) (hdf : ∀ ℓ, 2^p*‖rhoC p (df ℓ : ℂ)-(dPrime s t α ℓ : ℂ)‖≤2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖≤1) :
    ApproxMap p (resampB₀Of (t := t) p (bandJtM (s := s) (t := t) p u j rd) df)
        (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
        (6+2^p*((2*(62000*(p : ℝ)^3*(s : ℝ)^2*η)+2/2^p)+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖≤1 → ‖resampB₀Of (t := t) p (bandJtM (s := s) (t := t) p u j rd) df w‖≤1 := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  obtain ⟨J0, L, hJ0N, hNJ0, hJ0n, hLH, -, -, hdiff⟩ :=
    PhaseCellDominance.selected_rounded_inverse s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hJeq : J=J0 := by
    refine ContinuousLinearMap.ext fun x => ?_
    have e1 : PhaseCellOperator.exact s t α (J0 x)=x := by
      simpa using congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f x) hNJ0
    have e2 : J (PhaseCellOperator.exact s t α (J0 x))=J0 x := by
      simpa using congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f (J0 x)) hJ
    rw [←e2, e1]
  subst hJeq
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA := PhaseCellMatrix.matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  obtain ⟨R, hR⟩ := SchurDominance.exists_solver _ _ _ hμ hA
  have hexist : ∀ b : ZMod s → ℝ, ∃ y, Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) y=b :=
    fun b => ⟨R b, funext fun i => hR b i (mem_univ i)⟩
  have hhalf : ∀ v : ZMod s → ℂ, ‖v‖≤1 → ∀ i, |((1/2 : ℂ)*v i).re|≤1/2 ∧ |((1/2 : ℂ)*v i).im|≤1/2 := by
    intro v hv i
    have hvi : ‖v i‖≤1 := (norm_le_pi_norm v i).trans hv
    have hn : ‖(1/2 : ℂ)*v i‖≤1/2 := by
      rw [norm_mul, norm_div, norm_one, RCLike.norm_two]; linarith
    exact ⟨(Complex.abs_re_le_norm _).trans hn, (Complex.abs_im_le_norm _).trans hn⟩
  refine banded_resampB₀_spec p j u J L hLH hJ0n hj (by positivity) (by positivity) hdiff
    (by linarith)
    (fun v => SchurDominance.bandSolveM rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).re))
    (fun v => SchurDominance.bandSolveM rd (PhaseCellMatrix.realMatrix s t p u) univ
      (PhaseCellMatrix.physOrder s) (fun k => ((1/2 : ℂ)*v k).im))
    (bandJtM (s := s) (t := t) p u j rd) ?_ hexist ?_ df hdf hdf1
  · intro v hv yr yi hyr hyi i
    exact ⟨PhaseCellMatrix.bandSolveM_actual s t hst hα p u hp hwidth hαu hθ hgap hbudget rd η hrd
        hrd0 hprec yr _ hyr (fun k => (hhalf v hv k).1) i,
      PhaseCellMatrix.bandSolveM_actual s t hst hα p u hp hwidth hαu hθ hgap hbudget rd η hrd
        hrd0 hprec yi _ hyi (fun k => (hhalf v hv k).2) i⟩
  · intro v i
    unfold bandJtM
    exact (norm_rhoC_sub_le_two p _)

end IntegerMultBounds.MathlibTM2.Mult.FastB0
