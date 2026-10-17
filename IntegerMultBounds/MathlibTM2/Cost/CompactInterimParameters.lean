module

public import IntegerMultBounds.Parameters

/-! Arithmetic candidate for the first compact-runtime integration. These
inequalities are not a multiplication-time theorem. Actual caller and cost
assembly must replace the old full-width chunk estimate before using them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactInterim
noncomputable section

/-- Preserve the actual dimension exponent. -/
def epsilon : ℝ := 79 / (2^8:ℝ)
/-- Larger chunks become possible after removing the old chunk-width power. -/
def spacing : ℝ := (2^2:ℝ)⁻¹
/-- Absorb the full-depth compact recurrence and all polylogarithmic factors. -/
def lam' : ℝ := 1-459/(2^40:ℝ)
/-- Dyadic allowance for the unchanged quasi-linear multiplier. -/
def delta : ℝ := (2^5:ℝ)⁻¹
/-- The public saving: exactly the compact layer margin `ε (1-λ')`, about `1.1 · 2^-33`. -/
def kappa : ℝ := 36261/(2^48:ℝ)

/-- The compact recurrence and reserved axes fit strictly below the target
layer exponent; this does not assert the old full-width recurrence condition. -/
theorem compact_slacks :
    0 < epsilon ∧ 0 < spacing ∧ spacing < 1 ∧
      Parameters.tau < Parameters.lam ∧ Parameters.sigma < Parameters.lam ∧
      Parameters.lam < lam' ∧ 1-spacing < lam' ∧ lam' < 1 := by
  norm_num [epsilon,spacing,lam',Parameters.tau,Parameters.sigma,Parameters.lam]

/-- Exact candidate margins for layout, compact layers, direct rounds, CRT,
and the resampling stage with the retuned band width `α ≤ 2√d`. -/
def margin : Fin 5 → ℝ := ![
  epsilon*spacing*(1-Parameters.tau),
  epsilon*(1-lam'),
  epsilon*(1-spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/2-delta-3*epsilon/2]

theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin,kappa,epsilon,spacing,lam',delta,Parameters.tau]

theorem layer_margin : margin 1 = kappa := by
  norm_num [margin,kappa,epsilon,lam']

/-- The saving strictly exceeds `2^-33`. -/
theorem kappa_gt : (2^33:ℝ)⁻¹ < kappa := by
  norm_num [kappa]

/-- The obsolete full-width internal inequality fails for these chunks. All
uses of that estimate on the compact branch must be replaced. -/
theorem old_internal_exceeds_one : 1 < Parameters.tau*(1+2*spacing) := by
  norm_num [Parameters.tau,spacing]

end
end IntegerMultBounds.MathlibTM2.Cost.CompactInterim
