module

public import IntegerMultBounds.NLogN.PhaseCellDominanceBudget

/-! Polynomial exact and rounded inverse bounds in the community small-gap
regime. No assumption alpha squared times theta >= 1 is used. These are
mathematical inverses, not a claim of fast structured tape execution. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDominance

open ContinuousLinearMap
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- The actual normalized off-diagonal operator retains a polynomial gap. -/
theorem selected_offDiag_norm (hst : s<t) {α : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1) :
    ‖offDiagCLM s t α‖≤1-1/(4*(p : ℝ)) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hmargin : 0≤1-1/(4*(p : ℝ)) := by
    have h : 1/(4*(p : ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hu : 1≤u := by
    by_contra h
    have : u=0 := by omega
    simp [this] at hwidth
    omega
  apply opNorm_le_of_unit_norm hmargin
  intro v hv
  rw [offDiagCLM_apply s t hst hα, pi_norm_le_iff_of_nonneg hmargin]
  intro j
  exact (offDiag_row s t hst hα u hu hαu v
    (fun k => (norm_le_pi_norm v k).trans hv.le) j).trans
      (selected_scalar_gap p u hp hwidth hαu hθ)

/-- An actual two-sided exact inverse of norm at most4p in the small-gap regime. -/
theorem selected_exact_inverse (hst : s<t) {α : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      J ∘L PhaseCellOperator.exact s t α=1 ∧
      PhaseCellOperator.exact s t α ∘L J=1 ∧ ‖J‖≤4*(p : ℝ) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hE := selected_offDiag_norm s t hst hα p u hp hwidth hαu hθ
  have hlt : ‖offDiagCLM s t α‖<1 := by
    have : 0<1/(4*(p : ℝ)) := by positivity
    linarith
  obtain ⟨J, hJN, hNJ, hJ⟩ := exists_inverse_of_norm_lt_one (offDiagCLM s t α) hlt
  have heq : PhaseCellOperator.exact s t α=1+offDiagCLM s t α := normN_clm s t α
  refine ⟨J, by simpa only [heq] using hJN, by simpa only [heq] using hNJ, hJ.trans ?_⟩
  apply (div_le_iff₀ (by linarith : 0<1-‖offDiagCLM s t α‖)).mpr
  have hgap : 1/(4*(p : ℝ))≤1-‖offDiagCLM s t α‖ := by linarith
  have hmul := (div_le_iff₀ (by positivity : 0<4*(p : ℝ))).mp hgap
  nlinarith

/-- The actual corrected rounded matrix has the source's8p inverse bound. -/
theorem selected_rounded_inverse (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) :
    ∃ J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      J ∘L PhaseCellOperator.exact s t α=1 ∧
      PhaseCellOperator.exact s t α ∘L J=1 ∧ ‖J‖≤4*(p : ℝ) ∧
      L ∘L PhaseCellOperator.rounded s t p u=1 ∧
      PhaseCellOperator.rounded s t p u ∘L L=1 ∧
      ‖L‖≤8*(p : ℝ) ∧ ‖L-J‖≤32*(p : ℝ)^2/(2 : ℝ)^(45*p) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  obtain ⟨J, hJN, hNJ, hJ⟩ := selected_exact_inverse s t hst hα p u hp hwidth hαu hθ
  have hu : 1≤u := by
    by_contra h
    have : u=0 := by omega
    simp [this] at hwidth
    omega
  have hθpos : 0<(t : ℝ)/s-1 := (by positivity : 0<1/(4*(p : ℝ))).trans_le hθ
  have hsmall : 4*(p : ℝ)/(2 : ℝ)^(45*p)≤1/2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    simp only [one_mul]
    have hl := PhaseCellRow.linear_le_pow p
    calc 4*(p : ℝ)*2≤3*(2 : ℝ)^(4*p) := by linarith
      _≤4*(2 : ℝ)^(4*p) := by gcongr; norm_num
      _=(2 : ℝ)^(4*p+2) := by rw [pow_add]; ring
      _≤_ := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨L, hLH, hHL, hL, hdiff⟩ := PhaseCellOperator.inverse_transfer s t hst hα
    p u (by omega) hu hαu hθpos hgap hbudget J hJN hNJ hJ hsmall
  refine ⟨J, L, hJN, hNJ, hJ, hLH, hHL, ?_, ?_⟩
  · nlinarith [hL]
  · convert hdiff using 1
    ring

end IntegerMultBounds.NLogN.PhaseCellDominance
