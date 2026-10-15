module

public import IntegerMultBounds.Parameters

/-! Arithmetic candidate for the first compact-runtime integration. These
inequalities are not a multiplication-time theorem. Actual caller and cost
assembly must replace the old full-width chunk estimate before using them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactInterim
noncomputable section

/-- Preserve the actual dimension exponent. -/
def epsilon : ℝ := (2^3:ℝ)⁻¹
/-- Larger chunks become possible after removing the old chunk-width power. -/
def spacing : ℝ := (2^3:ℝ)⁻¹
/-- Absorb the full-depth compact recurrence and all polylogarithmic factors. -/
def lam' : ℝ := 1-(2^32:ℝ)⁻¹
/-- Dyadic allowance for the unchanged quasi-linear multiplier. -/
def delta : ℝ := (2^5:ℝ)⁻¹
/-- Candidate public saving, contingent on complete executable integration. -/
def kappa : ℝ := (2^35:ℝ)⁻¹

/-- The compact recurrence and reserved axes fit strictly below the target
layer exponent; this does not assert the old full-width recurrence condition. -/
theorem compact_slacks :
    0 < epsilon ∧ 0 < spacing ∧ spacing < 1 ∧
      Parameters.tau < Parameters.lam ∧ Parameters.sigma < Parameters.lam ∧
      Parameters.lam < lam' ∧ 1-spacing < lam' ∧ lam' < 1 := by
  norm_num [epsilon,spacing,lam',Parameters.tau,Parameters.sigma,Parameters.lam]

/-- Exact candidate margins for layout, compact layers, direct rounds, CRT,
and the unchanged Gaussian stage. -/
def margin : Fin 5 → ℝ := ![
  epsilon*spacing*(1-Parameters.tau),
  epsilon*(1-lam'),
  epsilon*(1-spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/4-delta-3*epsilon/2]

theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin,kappa,epsilon,spacing,lam',delta,Parameters.tau]

theorem layer_margin : margin 1 = kappa := by
  norm_num [margin,kappa,epsilon,lam']

/-- The obsolete full-width internal inequality fails for these chunks. All
uses of that estimate on the compact branch must be replaced. -/
theorem old_internal_exceeds_one : 1 < Parameters.tau*(1+2*spacing) := by
  norm_num [Parameters.tau,spacing]

end
end IntegerMultBounds.MathlibTM2.Cost.CompactInterim
