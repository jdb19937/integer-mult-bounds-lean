module

public import IntegerMultBounds.NLogN.PhaseCellMatrix

/-! Instantiation of Schur elimination on the actual rounded periodic Gaussian
matrix. Row gap and row mass survive arbitrary boundary/interior elimination. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open ContinuousLinearMap
variable (s t : ℕ) [NeZero s] [NeZero t]

private theorem dyadic_le_margin (p : ℕ) (hp : 2≤p) :
    1/(2 : ℝ)^(45*p)≤1/(8*(p : ℝ)) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  apply one_div_le_one_div_of_le (by positivity)
  have hlin := PhaseCellRow.linear_le_pow p
  calc 8*(p : ℝ)≤3*(2 : ℝ)^(4*p) := by linarith
    _≤4*(2 : ℝ)^(4*p) := by gcongr; norm_num
    _=(2 : ℝ)^(4*p+2) := by rw [pow_add]; ring
    _≤_ := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The actual rounded operator stays strictly within unit distance of I. -/
theorem rounded_sub_one (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) :
    ‖PhaseCellOperator.rounded s t p u-1‖≤1-1/(8*(p : ℝ)) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hu : 1≤u := by
    by_contra h
    have : u=0 := by omega
    simp [this] at hwidth
    omega
  have hθpos : 0<(t : ℝ)/s-1 := (by positivity : 0<1/(4*(p : ℝ))).trans_le hθ
  have he := PhaseCellOperator.norm_error s t hst hα p u (by omega) hu hαu hθpos hgap hbudget
  have hN := PhaseCellDominance.selected_offDiag_norm s t hst hα p u hp hwidth hαu hθ
  have hid : PhaseCellOperator.exact s t α-1=offDiagCLM s t α := by
    unfold PhaseCellOperator.exact
    rw [normN_clm]
    abel
  have hsum := norm_sub_le_norm_sub_add_norm_sub (PhaseCellOperator.rounded s t p u)
    (PhaseCellOperator.exact s t α) 1
  rw [hid] at hsum
  have hsmall := dyadic_le_margin p hp
  have hfrac : 1/(4*(p : ℝ))=2*(1/(8*(p : ℝ))) := by ring
  rw [hfrac] at hN
  linarith

omit [NeZero t] in
/-- Summing literal rational entries gives the rounded operator on ones. -/
theorem row_sum (p u : ℕ) (j : ZMod s) :
    ((∑ l, realMatrix s t p u j l : ℝ) : ℂ)=
      PhaseCellOperator.rounded s t p u (fun _ => 1) j := by
  have h := congrFun (matrix_mulVec s t p u (fun _ => 1)) j
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [PhaseCellOperator.rounded_apply]
  convert h using 1
  simp [realMatrix]

/-- Positive entries and the central unit imply a true matrix row gap. -/
theorem matrix_gap (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) :
    SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))) := by
  have hnorm := rounded_sub_one s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hC : 0≤1-1/(8*(p : ℝ)) := by
    have h : 1/(8*(p : ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hone : ‖(fun _ : ZMod s => (1 : ℂ))‖≤1 := by simp
  have hv := (PhaseCellOperator.rounded s t p u-1).le_of_opNorm_le_of_le hnorm hone
  intro j _
  have hr := (norm_le_pi_norm ((PhaseCellOperator.rounded s t p u-1) (fun _ => 1)) j).trans hv
  simp only [sub_apply, Pi.sub_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply, mul_one] at hr
  rw [←row_sum s t p u j, ←Complex.ofReal_one, ←Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hr
  have hm : (∑ l, realMatrix s t p u j l)≤2-1/(8*(p : ℝ)) := by
    have h := le_abs_self ((∑ l, realMatrix s t p u j l)-1)
    linarith
  have hd : 1≤realMatrix s t p u j j := by
    unfold realMatrix
    exact_mod_cast matrix_diag s t p u j
  have hpos (l : ZMod s) : 0≤realMatrix s t p u j l := by
    unfold realMatrix
    exact_mod_cast matrix_nonneg s t p u j l
  simp_rw [abs_of_nonneg (hpos _)]
  have hsplit := Finset.sum_erase_add Finset.univ (fun l => realMatrix s t p u j l)
    (Finset.mem_univ j)
  linarith

/-- Any chosen elimination of interior vertices leaves the same positive
boundary-row margin in the actual rounded matrix. -/
theorem boundary_gap (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (ks : List (ZMod s)) :
    SchurDominance.DominatesOn
      (SchurDominance.run (realMatrix s t p u) Finset.univ ks).1
      (SchurDominance.run (realMatrix s t p u) Finset.univ ks).2 (1/(8*(p : ℝ))) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  exact SchurDominance.run_gap _ _ _ (by positivity)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget) ks

end IntegerMultBounds.NLogN.PhaseCellMatrix
