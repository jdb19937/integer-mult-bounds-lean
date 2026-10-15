module

public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters

/-! Candidate next dyadic saving by increasing the dimension exponent.
This is parameter arithmetic only: runtime sizing and precision must be retuned
before it supplies a multiplication-time theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactDimension
noncomputable section

def epsilon : ℝ := (2^4:ℝ)⁻¹
def kappa : ℝ := (2^36:ℝ)⁻¹

/-- Existing supplier accuracy prevents the next dyadic saving at the prior thirty-second-root
 dimension exponent, even if the layer bound approaches `sigma`. -/
theorem prior_dimension_obstruction {layer : ℝ} (h : Parameters.sigma ≤ layer) :
    ((2^5:ℝ)⁻¹) * (1-layer) < kappa := by
  have he : 0 ≤ ((2^5:ℝ)⁻¹) := by norm_num
  have hb : ((2^5:ℝ)⁻¹) * (1-Parameters.sigma) < kappa := by
    norm_num [Parameters.sigma,kappa]
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left h 1) he).trans_lt hb

/-- All five analytic stage margins cover the next dyadic saving after doubling
 epsilon; this does not establish the larger executable dimension or its guard. -/
def margin : Fin 5 → ℝ := ![
  epsilon*CompactInterim.spacing*(1-Parameters.tau),
  epsilon*(1-CompactInterim.lam'),
  epsilon*(1-CompactInterim.spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/8-3*epsilon/2]

theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin,kappa,epsilon,CompactInterim.spacing,
    CompactInterim.lam',Parameters.tau]

theorem layer_margin : margin 1 = kappa := by
  norm_num [margin,kappa,epsilon,CompactInterim.lam']

/-- The old twentieth-power width requirement cannot survive a sixteenth-root
 dimension: the executable precision contracts must be sharpened first. -/
theorem twentieth_power_exceeds_sixteenth {d : ℕ} (hd : 2≤d) : d^16 < d^20 := by
  exact Nat.pow_lt_pow_right (by omega : 1<d) (by decide : 16<20)

/-- At the proposed sixteenth-root dimension the existing complex supplier
 still cannot support the following dyadic saving by layer tuning alone. -/
theorem next_supplier_obstruction {layer : ℝ} (h : Parameters.sigma ≤ layer) :
    epsilon * (1-layer) < (2^35:ℝ)⁻¹ := by
  have he : 0 ≤ epsilon := by norm_num [epsilon]
  have hb : epsilon * (1-Parameters.sigma) < (2^35:ℝ)⁻¹ := by
    norm_num [epsilon,Parameters.sigma]
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left h 1) he).trans_lt hb

/-- Doubling the dimension again violates the current Gaussian-stage margin. -/
theorem next_gaussian_obstruction :
    (1:ℝ)/8-3*(2^3:ℝ)⁻¹/2 = -(2^4:ℝ)⁻¹ := by norm_num

namespace Eighth
/-- Candidate dimension after sharpening the logarithmic overhead. -/
def epsilon : ℝ := (2^3:ℝ)⁻¹
def delta : ℝ := (2^5:ℝ)⁻¹
def kappa : ℝ := (2^35:ℝ)⁻¹

def margin : Fin 5 → ℝ := ![
  epsilon*CompactInterim.spacing*(1-Parameters.tau),
  epsilon*(1-CompactInterim.lam'),
  epsilon*(1-CompactInterim.spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/4-delta-3*epsilon/2]

/-- Analytic feasibility only; larger runtime sizing and sharper stage-cost
 matching must still be proved before exposing this saving. -/
theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin,kappa,epsilon,delta,CompactInterim.spacing,
    CompactInterim.lam',Parameters.tau]

theorem gaussian_margin : margin 4 = (2^5:ℝ)⁻¹ := by
  norm_num [margin,epsilon,delta]
end Eighth

end
end IntegerMultBounds.MathlibTM2.Cost.CompactDimension
