module

public import IntegerMultBounds.NLogN.PhaseCellRow

/-! Dyadic error budgeting for the actual periodic rounded Gaussian row. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRow

/-- A coarse dimension-independent upper bound for the executable band. -/
theorem width_le (p u : ℕ) :
    PhaseCellBand.width p u≤4*p+1 := by
  have hdiv : 16*p/u≤16*p := Nat.div_le_self _ _
  have hp2 : p≤p^2 := Nat.le_self_pow two_ne_zero p
  have hsq : 16*p/u≤(4*p)^2 := by nlinarith
  have hsqrt : Nat.sqrt (16*p/u)≤4*p := by
    have := Nat.sqrt_le_sqrt hsq
    simpa only [Nat.sqrt_eq'] using this
  exact Nat.add_le_add_right hsqrt 1

/-- Rational amplification written with a single dyadic denominator. -/
theorem entryError_eq (p : ℕ) : entryError p=
    (48*(2 : ℝ)^(16*p)+4)/(2 : ℝ)^(2^15*p) := by
  unfold entryError PhaseCellRounded.error
  rw [div_pow, div_pow, ←pow_mul]
  have hpow : (2 : ℝ)^(8*p*2)=(2 : ℝ)^(16*p) := by congr 1; omega
  rw [hpow]
  field_simp
  ring

/-- An elementary retained-cardinality bound with dyadic growth. -/
theorem linear_le_pow (p : ℕ) : (8*p+3 : ℝ)≤3*(2 : ℝ)^(4*p) := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    have hstep : (8*(p+1)+3 : ℝ)≤16*(8*p+3) := by nlinarith [show (0 : ℝ)≤p from Nat.cast_nonneg p]
    have hpow : (2 : ℝ)^(4*(p+1))=16*(2 : ℝ)^(4*p) := by
      rw [show 4*(p+1)=4*p+4 by omega, pow_add]
      ring
    push_cast
    rw [hpow]
    nlinarith

/-- The selected precision absorbs both denominator amplification and every
retained lattice incidence, leaving the same allowance as the full tail. -/
theorem rounding_budget (p u : ℕ) (hp : 0<p) :
    (2*(PhaseCellBand.width p u : ℝ)+1)*entryError p≤1/(2 : ℝ)^(46*p) := by
  have hw : (PhaseCellBand.width p u : ℝ)≤4*p+1 := by exact_mod_cast width_le p u
  have hc : 2*(PhaseCellBand.width p u : ℝ)+1≤3*(2 : ℝ)^(4*p) := by
    exact (by linarith : 2*(PhaseCellBand.width p u : ℝ)+1≤8*p+3).trans
      (linear_le_pow p)
  have hb : (48*(2 : ℝ)^(16*p)+4)≤52*(2 : ℝ)^(16*p) := by
    have := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := 16*p)
    linarith
  have hnum : (2*(PhaseCellBand.width p u : ℝ)+1)*(48*(2 : ℝ)^(16*p)+4)≤
      (2 : ℝ)^(20*p+8) := by
    calc _≤(3*(2 : ℝ)^(4*p))*(52*(2 : ℝ)^(16*p)) :=
          mul_le_mul hc hb (by positivity) (by positivity)
      _≤(2 : ℝ)^(20*p+8) := by
        rw [pow_add, show 20*p=4*p+16*p by omega, pow_add]
        norm_num
        nlinarith [mul_nonneg (show (0 : ℝ)≤2^(4*p) by positivity)
          (show (0 : ℝ)≤2^(16*p) by positivity)]
  rw [entryError_eq, ←mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  calc _≤(2 : ℝ)^(20*p+8)*(2 : ℝ)^(46*p) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _=(2 : ℝ)^(66*p+8) := by rw [←pow_add]; congr 1; omega
    _≤(2 : ℝ)^(2^15*p) := pow_le_pow_right₀ (by norm_num) (by omega)

variable (s t : ℕ) [NeZero s] [NeZero t]

/-- A clean dyadic error for the actual periodic corrected Gaussian row. -/
theorem selected_row_dyadic (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p) (v : ZMod s → ℂ) (hv : ∀ k, ‖v k‖≤1) (j : ZMod s) :
    ‖normN s t α v j-rounded s t p u (PhaseCellBand.width p u) v j‖≤
      1/(2 : ℝ)^(45*p) := by
  have hr := selected_row_error s t hst hα p u hp hu hαu htheta hgap hbudget v hv j
  have hb := rounding_budget p u hp
  have he : 2/(2 : ℝ)^(46*p)≤1/(2 : ℝ)^(45*p) := by
    have hpow : (2 : ℝ)^(45*p+1)≤(2 : ℝ)^(46*p) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc _≤2/(2 : ℝ)^(45*p+1) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
      _=1/(2 : ℝ)^(45*p) := by rw [pow_succ]; field_simp
  calc _≤1/(2 : ℝ)^(46*p)+1/(2 : ℝ)^(46*p) :=
        hr.trans (add_le_add (le_refl _) hb)
    _=2/(2 : ℝ)^(46*p) := by ring
    _≤_ := he

end IntegerMultBounds.NLogN.PhaseCellRow
