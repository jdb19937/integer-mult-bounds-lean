module

public import IntegerMultBounds.Parameters

/-! Arithmetic limits of the direct size-25 supplier (`Parameters.directSigma`) and the coarse
Gaussian estimate.
These are route-specific constraints, not obstructions to better algorithms.
The non-root dimension candidate below asserts arithmetic feasibility only. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactSupplierCeiling
noncomputable section

/-- The direct supplier leaves a positive, exactly known exponent saving. -/
theorem supplier_saving :
    1 - Parameters.directSigma = (418 : ℝ) / 10^12 ∧
    0 < 1 - Parameters.directSigma := by
  norm_num [Parameters.directSigma]

/-- Positive coarse Gaussian margin forces dimension exponent below one sixth. -/
theorem dimension_lt_sixth {epsilon loss : ℝ} (hloss : 0 ≤ loss)
    (hmargin : 0 < 1/4 - loss - 3*epsilon/2) : epsilon < 1/6 := by
  linarith

/-- With the direct supplier and this Gaussian estimate, every admissible dimension
and layer give a saving strictly below the displayed dyadic ceiling. -/
theorem saving_lt_ceiling {epsilon layer loss : ℝ} (hepsilon : 0 ≤ epsilon)
    (hlayer : Parameters.directSigma ≤ layer) (hloss : 0 ≤ loss)
    (hmargin : 0 < 1/4 - loss - 3*epsilon/2) :
    epsilon * (1-layer) < (2^33 : ℝ)⁻¹ := by
  have hdim := dimension_lt_sixth hloss hmargin
  have hsaving := supplier_saving.2
  calc
    epsilon * (1-layer) ≤ epsilon * (1-Parameters.directSigma) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hlayer 1) hepsilon
    _ < (1/6) * (1-Parameters.directSigma) := mul_lt_mul_of_pos_right hdim hsaving
    _ < (2^33 : ℝ)⁻¹ := by norm_num [Parameters.directSigma]

namespace NineSixtyFourths

def epsilon : ℝ := 9 / 2^6
def spacing : ℝ := (2^2 : ℝ)⁻¹
def layer : ℝ := 1 - 57 / 2^37
def delta : ℝ := (2^5 : ℝ)⁻¹
def kappa : ℝ := (2^34 : ℝ)⁻¹

/-- The proposed layer remains strictly above the existing supplier exponent. -/
theorem supplier_slack : Parameters.sigma < layer ∧ layer < 1 := by
  norm_num [Parameters.sigma, layer]

/-- The existing compact recurrence exponents and chunk count fit below the
candidate layer; these inequalities alone do not retune executable sizing. -/
theorem recurrence_slack :
    Parameters.lam < layer ∧ Parameters.sigma < Parameters.lam ∧
    Parameters.tau < Parameters.lam ∧ 1-spacing < layer := by
  norm_num [Parameters.lam, Parameters.sigma, Parameters.tau, layer, spacing]

def margin : Fin 5 → ℝ := ![
  epsilon*spacing*(1-Parameters.tau),
  epsilon*(1-layer),
  epsilon*(1-spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/4-delta-3*epsilon/2]

/-- Each arithmetic stage margin covers this candidate saving. This supplies
neither executable sizing contracts nor a multiplication-time theorem. -/
theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin, kappa, epsilon, spacing, layer, delta, Parameters.tau]

theorem gaussian_margin : margin 4 = (2^7 : ℝ)⁻¹ := by
  norm_num [margin, epsilon, delta]

theorem layer_margin : margin 1 = 513 / (2^43 : ℝ) := by
  norm_num [margin, epsilon, layer]

end NineSixtyFourths

namespace NineThirtySeconds

def epsilon : ℝ := 9 / 2^5
def spacing : ℝ := (2^2 : ℝ)⁻¹
def layer : ℝ := 1 - 57 / 2^37
def delta : ℝ := (2^5 : ℝ)⁻¹
def kappa : ℝ := (2^33 : ℝ)⁻¹

/-- The stage margins with the retuned band width `α ≤ 2√d`: the resampling margin is
`1/2 - δ - 3ε/2`, with no coarse `b^{1/4}` Gaussian factor. -/
def margin : Fin 5 → ℝ := ![
  epsilon*spacing*(1-Parameters.tau),
  epsilon*(1-layer),
  epsilon*(1-spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/2-delta-3*epsilon/2]

theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin, kappa, epsilon, spacing, layer, delta, Parameters.tau]

theorem resampling_margin : margin 4 = 3 / (2^6 : ℝ) := by
  norm_num [margin, epsilon, delta]

theorem layer_margin : margin 1 = 513 / (2^42 : ℝ) := by
  norm_num [margin, epsilon, layer]

end NineThirtySeconds
end
end IntegerMultBounds.MathlibTM2.Cost.CompactSupplierCeiling
