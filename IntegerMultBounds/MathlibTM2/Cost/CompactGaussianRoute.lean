module

public import IntegerMultBounds.Parameters

/-! Arithmetic reach of the faster Gaussian route with the existing supplier.
Replacing the coarse Gaussian margin `1/4 - δ - 3ε/2` by the selected
phase-cell margin `min (1-ε-δ) (r-δ)` (with `ε + r < 1` and `ε > (1-r)/2`)
lets every stage margin cover `2^-32` at `ε = 5/8`, `r = 1/4`, without
changing the supplier. Conversely no Gaussian improvement alone reaches
`2^-31`, since the layer margin stays below `1 - σ`. These are arithmetic
route certificates, not multiplication-time theorems. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactGaussianRoute
noncomputable section

/-- With the existing supplier, the layer margin is below `2^-31` for every
dimension exponent at most one, whatever the Gaussian estimate. -/
theorem layer_lt_ceiling {epsilon layer : ℝ} (hepsilon : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hlayer : Parameters.sigma ≤ layer) :
    epsilon*(1-layer) < (2^31 : ℝ)⁻¹ := by
  have h1 : 1-layer ≤ 1-Parameters.sigma := by linarith
  have hσ : 1-Parameters.sigma = 418/10^12 := by norm_num [Parameters.sigma]
  have h0 : 0 ≤ 1-Parameters.sigma := by rw [hσ]; norm_num
  calc epsilon*(1-layer) ≤ 1*(1-Parameters.sigma) := by
        by_cases hl : 0 ≤ 1-layer
        · exact mul_le_mul hone h1 hl zero_le_one
        · nlinarith
    _ < (2^31 : ℝ)⁻¹ := by rw [one_mul, hσ]; norm_num

namespace FiveEighths

def epsilon : ℝ := 5/8
def spacing : ℝ := (2^2 : ℝ)⁻¹
def layer : ℝ := 1-417/10^12
def delta : ℝ := (2^5 : ℝ)⁻¹
def r : ℝ := (2^2 : ℝ)⁻¹
def kappa : ℝ := (2^32 : ℝ)⁻¹

/-- The selected phase-cell parameter band. -/
theorem band : epsilon+r < 1 ∧ (1-r)/2 < epsilon := by
  norm_num [epsilon, r]

/-- The layer stays strictly between the compact recurrence exponent and one. -/
theorem layer_slack : Parameters.sigma < layer ∧ Parameters.lam < layer ∧ layer < 1 ∧
    1-spacing < layer := by
  norm_num [Parameters.sigma, Parameters.lam, layer, spacing]

def margin : Fin 5 → ℝ := ![
  epsilon*spacing*(1-Parameters.tau),
  epsilon*(1-layer),
  epsilon*(1-spacing),
  (1-epsilon)*(1-Parameters.tau),
  min (1-epsilon-delta) (r-delta)]

/-- Every stage margin covers `2^-32` once the Gaussian margin is the
phase-cell margin. -/
theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin, kappa, epsilon, spacing, layer, delta, r, Parameters.tau]

/-- The binding margin is the layer margin `5/8 · 417/10^12`, above `2^-32`. -/
theorem layer_margin : margin 1 = 5/8*(417/10^12) := by
  norm_num [margin, epsilon, layer]

end FiveEighths
end
end IntegerMultBounds.MathlibTM2.Cost.CompactGaussianRoute
