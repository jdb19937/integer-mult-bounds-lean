module

public import IntegerMultBounds.Parameters

/-! Arithmetic candidate for the first compact-runtime integration. These
inequalities are not a multiplication-time theorem. Actual caller and cost
assembly must replace the old full-width chunk estimate before using them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactInterim
noncomputable section

/-- Preserve the actual dimension exponent. -/
def epsilon : ℝ := 31 / (2^6:ℝ)
/-- Larger chunks become possible after removing the old chunk-width power. -/
def spacing : ℝ := 7/(2^3:ℝ)
/-- The layer exponent of the T16 node: above `τ` and above `log_m (F / NW) < 999/1000`
(`Cost.br_branching_999`). -/
def lam : ℝ := 1-28/(10^10:ℝ)
/-- Absorb the full-depth compact recurrence and all polylogarithmic factors. -/
def lam' : ℝ := 1-23/(2^33:ℝ)
/-- Dyadic allowance for the unchanged quasi-linear multiplier. -/
def delta : ℝ := (2^7:ℝ)⁻¹
/-- The public saving: the layout margin `ε s (1-τ)` rounded down to `2^-46`, about `2^-29.57`. -/
def kappa : ℝ := 88279/(2^46:ℝ)

/-- The compact recurrence and reserved axes fit strictly below the target
layer exponent; this does not assert the old full-width recurrence condition. -/
theorem compact_slacks :
    0 < epsilon ∧ 0 < spacing ∧ spacing < 1 ∧
      Parameters.tau < lam ∧ 999/1000 < lam ∧
      lam < lam' ∧ 1-spacing < lam' ∧ lam' < 1 := by
  norm_num [epsilon,spacing,lam,lam',Parameters.tau]

/-- Exact candidate margins for layout, compact layers, direct rounds, CRT,
and the resampling stage with the logarithmic band width `α ≤ 4 b^{ε/2^33}`. -/
def margin : Fin 5 → ℝ := ![
  epsilon*spacing*(1-Parameters.tau),
  epsilon*(1-lam'),
  epsilon*(1-spacing),
  (1-epsilon)*(1-Parameters.tau),
  1/2-delta-epsilon*(1+(2^33:ℝ)⁻¹)]

theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin,kappa,epsilon,spacing,lam',delta,Parameters.tau]

/-- The obsolete full-width internal inequality fails for these chunks. All
uses of that estimate on the compact branch must be replaced. -/
theorem old_internal_exceeds_one : 1 < Parameters.tau*(1+2*spacing) := by
  norm_num [Parameters.tau,spacing]

end
end IntegerMultBounds.MathlibTM2.Cost.CompactInterim
