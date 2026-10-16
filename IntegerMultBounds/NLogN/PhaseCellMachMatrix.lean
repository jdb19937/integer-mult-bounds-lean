module

public import IntegerMultBounds.NLogN.PhaseCellPerturb

/-! The matrix a machine can build: the window of Gaussian coefficients
`exp(normExp j k)`, `|k| ≤ w`, each approximated within `δ`, wrapped and
accumulated like the phase-cell matrix. Each of its rows is within
`(2w+1)δ + 2^-46p + 2^-45p` of the phase-cell row in absolute sum, through the
exact window, the exact operator `N`, and the phase-cell operator. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset PhaseCellRow
variable (s t : ℕ) [NeZero s]

/-- The wrapped window matrix of coefficients `a j k`, `|k| ≤ w`. -/
noncomputable def windowMatrix (w : ℕ) (a : ZMod s → ℤ → ℝ) : Matrix (ZMod s) (ZMod s) ℝ :=
  fun j l => window (fun k => if j+(k : ZMod s)=l then a j k else 0) w

theorem windowMatrix_mulVec (w : ℕ) (a : ZMod s → ℤ → ℝ) (v : ZMod s → ℂ) (j : ZMod s) :
    ∑ l, (windowMatrix s w a j l : ℂ)*v l=window (fun k => (a j k : ℂ)*v (j+k)) w := by
  simp only [windowMatrix, window, Complex.ofReal_add, Complex.ofReal_sum, add_mul, sum_add_distrib,
    sum_mul]
  rw [sum_comm (s := univ) (t := range _), sum_comm (s := univ) (t := range _)]
  congr 2
  all_goals simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul, Fintype.sum_ite_eq]

/-- A real row whose action on unit vectors stays within `c` has absolute sum at most `c`. -/
theorem row_abs_sum_le (r : ZMod s → ℝ) (c : ℝ)
    (h : ∀ v : ZMod s → ℂ, (∀ l, ‖v l‖≤1) → ‖∑ l, (r l : ℂ)*v l‖≤c) : ∑ l, |r l|≤c := by
  set v : ZMod s → ℂ := fun l => if 0≤r l then 1 else -1
  have hv : ∀ l, ‖v l‖≤1 := by
    intro l
    simp only [v]
    split <;> simp
  have e : ∑ l, (r l : ℂ)*v l=((∑ l, |r l| : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun l _ => ?_
    simp only [v]
    split
    · rename_i hr; rw [abs_of_nonneg hr, mul_one]
    · rename_i hr; rw [abs_of_neg (not_le.mp hr)]; push_cast; ring
  have := h v hv
  rw [e, Complex.norm_real, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

omit [NeZero s] in
theorem window_sub (f g : ℤ → ℂ) (w : ℕ) : window f w-window g w=window (fun k => f k-g k) w := by
  simp only [window, sum_sub_distrib]; ring

omit [NeZero s] in
theorem norm_window_le (f : ℤ → ℂ) (w : ℕ) (δ : ℝ) (hf : ∀ k : ℤ, k.natAbs ≤ w → ‖f k‖≤δ) :
    ‖window f w‖≤(2*w+1)*δ := by
  unfold window
  have h0 := hf 0 (by simp)
  have h1 : ‖∑ n∈range w, f ((n : ℤ)+1)‖≤w*δ :=
    (norm_sum_le _ _).trans ((sum_le_sum fun n hn => hf _ (by have := mem_range.mp hn; omega)).trans
      (by rw [sum_const, card_range, nsmul_eq_mul]))
  have h2 : ‖∑ n∈range w, f (-((n : ℤ)+1))‖≤w*δ :=
    (norm_sum_le _ _).trans ((sum_le_sum fun n hn => hf _ (by have := mem_range.mp hn; omega)).trans
      (by rw [sum_const, card_range, nsmul_eq_mul]))
  have := norm_add_le (f 0+∑ n∈range w, f ((n : ℤ)+1)) (∑ n∈range w, f (-((n : ℤ)+1)))
  have := norm_add_le (f 0) (∑ n∈range w, f ((n : ℤ)+1))
  linarith

variable [NeZero t]

/-- The machine window matrix of any width `w` with `16p ≤ u w²` is close to the phase-cell
matrix row by row. -/
theorem windowMatrix_close (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (w : ℕ) (hband : 16*p≤u*w^2) (a : ZMod s → ℤ → ℝ) (δ : ℝ)
    (ha : ∀ j k, k.natAbs ≤ w → |a j k-Real.exp (normExp s t α j.val k)|≤δ)
    (j : ZMod s) :
    ∑ l, |windowMatrix s w a j l-realMatrix s t p u j l|≤
      (2*w+1)*δ+1/(2 : ℝ)^(46*p)+1/(2 : ℝ)^(45*p) := by
  refine row_abs_sum_le s _ _ fun v hv => ?_
  have hvn : ‖v‖≤1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hv
  have hsplit : ∑ l, ((windowMatrix s w a j l-realMatrix s t p u j l : ℝ) : ℂ)*v l=
      (window (fun k => (a j k : ℂ)*v (j+k)) w-exactWindow s t α w v j)+
      (exactWindow s t α w v j-normN s t α v j)+
      (PhaseCellOperator.exact s t α v j-PhaseCellOperator.rounded s t p u v j) := by
    have h1 := windowMatrix_mulVec s w a v j
    have h2 := congrFun (matrix_mulVec s t p u v) j
    simp only [Matrix.mulVec, dotProduct] at h2
    rw [PhaseCellOperator.exact_apply s t hα, PhaseCellOperator.rounded_apply, ← h2, ← h1]
    simp only [Complex.ofReal_sub, sub_mul, sum_sub_distrib, realMatrix, Complex.ofReal_ratCast]
    ring
  rw [hsplit]
  have hA : ‖window (fun k => (a j k : ℂ)*v (j+k)) w-exactWindow s t α w v j‖≤(2*w+1)*δ := by
    rw [exactWindow, window_sub]
    refine norm_window_le _ w δ fun k hk => ?_
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hv _)).trans (ha j k hk)
  have hB : ‖exactWindow s t α w v j-normN s t α v j‖≤1/(2 : ℝ)^(46*p) := by
    rw [norm_sub_rev]
    exact (exactWindow_error s t hst hα v hv j w).trans
      (PhaseCellTailBounds.selected_tail s t p u w (Nat.pos_of_ne_zero (NeZero.ne s)) hst.le hp hu
        hband α hα hαu j.val)
  have hC : ‖PhaseCellOperator.exact s t α v j-PhaseCellOperator.rounded s t p u v j‖≤1/(2 : ℝ)^(45*p) := by
    have hn := PhaseCellOperator.norm_error s t hst hα p u hp hu hαu htheta hgap hbudget
    have h := ((PhaseCellOperator.rounded s t p u-PhaseCellOperator.exact s t α).le_of_opNorm_le hn v)
    have hj := (norm_le_pi_norm ((PhaseCellOperator.rounded s t p u-PhaseCellOperator.exact s t α) v) j).trans h
    rw [norm_sub_rev]
    simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply] at hj
    exact hj.trans (by
      have : 0≤1/(2 : ℝ)^(45*p) := by positivity
      nlinarith [norm_nonneg v])
  have n1 := norm_add_le (window (fun k => (a j k : ℂ)*v (j+k)) w-exactWindow s t α w v j+
    (exactWindow s t α w v j-normN s t α v j))
    (PhaseCellOperator.exact s t α v j-PhaseCellOperator.rounded s t p u v j)
  have n2 := norm_add_le (window (fun k => (a j k : ℂ)*v (j+k)) w-exactWindow s t α w v j)
    (exactWindow s t α w v j-normN s t α v j)
  linarith

end IntegerMultBounds.NLogN.PhaseCellMatrix
