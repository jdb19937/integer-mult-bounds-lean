module

import IntegerMultBounds.NLogN.Neumann
import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Quantitative perturbation of a two-sided operator inverse

The existing Neumann-series theorem supplies the inverse of the relative
perturbation. This bridge gives explicit norm and inverse-difference bounds
for actual continuous linear maps. In the selected phase-cell application,
`N` is the exact normalized operator and `H` the structured rounded operator.
The estimate on `H - N` remains an explicit premise: no row-error bound,
rounded solver, or machine-cost assertion is supplied here.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.InversePerturbation

open ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- Stability of a two-sided inverse under an operator-norm perturbation.
The returned inverse is the Neumann inverse of `1 + J*(H-N)`, composed with `J`.
The assumptions permit the trivial space and zero perturbations. -/
theorem exists_inverse (N J H : V →L[ℂ] V) {M eta : ℝ}
    (hJN : J ∘L N = 1) (hNJ : N ∘L J = 1)
    (hJ : ‖J‖ ≤ M) (herror : ‖H - N‖ ≤ eta) (hsmall : M * eta < 1) :
    ∃ L : V →L[ℂ] V, L ∘L H = 1 ∧ H ∘L L = 1 ∧
      ‖L‖ ≤ M / (1 - M * eta) ∧
      ‖L - J‖ ≤ M ^ 2 * eta / (1 - M * eta) := by
  have hM : 0 ≤ M := (norm_nonneg J).trans hJ
  have heta : 0 ≤ eta := (norm_nonneg (H - N)).trans herror
  have hden : 0 < 1 - M * eta := by linarith
  change J * N = 1 at hJN
  change N * J = 1 at hNJ
  let E := J * (H - N)
  have hE : ‖E‖ ≤ M * eta := by
    calc ‖E‖ ≤ ‖J‖ * ‖H - N‖ := norm_mul_le _ _
      _ ≤ M * eta := mul_le_mul hJ herror (norm_nonneg _) hM
  obtain ⟨A, hAleft, hAright, hAnorm⟩ :=
    exists_inverse_of_norm_lt_one E (hE.trans_lt hsmall)
  change A * (1 + E) = 1 at hAleft
  change (1 + E) * A = 1 at hAright
  have hA : ‖A‖ ≤ 1 / (1 - M * eta) := by
    refine hAnorm.trans ?_
    apply div_le_div_of_nonneg_left zero_le_one hden
    linarith
  have hJH : J * H = 1 + E := by
    calc J * H = J * N + J * (H - N) := by noncomm_ring
      _ = 1 + E := by rw [hJN]
  have hH : H = N * (1 + E) := by
    dsimp [E]
    rw [mul_add, mul_one, ← mul_assoc, hNJ, one_mul]
    abel
  let L := A * J
  have hLH : L * H = 1 := by
    dsimp [L]
    rw [mul_assoc, hJH, hAleft]
  have hHL : H * L = 1 := by
    change H * (A * J) = 1
    rw [hH, ← mul_assoc, mul_assoc N, hAright, mul_one, hNJ]
  have hL : ‖L‖ ≤ M / (1 - M * eta) := by
    calc ‖L‖ ≤ ‖A‖ * ‖J‖ := norm_mul_le _ _
      _ ≤ (1 / (1 - M * eta)) * M :=
        mul_le_mul hA hJ (norm_nonneg _) (by positivity)
      _ = M / (1 - M * eta) := by ring
  have hdiff : L * (H - N) * J = J - L := by
    calc L * (H - N) * J = L * H * J - L * (N * J) := by noncomm_ring
      _ = J - L := by rw [hLH, hNJ, one_mul, mul_one]
  refine ⟨L, hLH, hHL, hL, ?_⟩
  calc ‖L - J‖ = ‖J - L‖ := norm_sub_rev _ _
    _ = ‖L * (H - N) * J‖ := by rw [hdiff]
    _ ≤ ‖L * (H - N)‖ * ‖J‖ := norm_mul_le _ _
    _ ≤ (‖L‖ * ‖H - N‖) * ‖J‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (M / (1 - M * eta) * eta) * M := by gcongr
    _ = M ^ 2 * eta / (1 - M * eta) := by ring

/-- With half the inverse gap reserved, the inverse norm grows by at most two
and its change is at most `2 M² eta`. The actual approximation estimate is
still required from the rounded-operator construction. -/
theorem exists_inverse_of_half_gap (N J H : V →L[ℂ] V) {M eta : ℝ}
    (hJN : J ∘L N = 1) (hNJ : N ∘L J = 1)
    (hJ : ‖J‖ ≤ M) (herror : ‖H - N‖ ≤ eta) (hsmall : M * eta ≤ 1 / 2) :
    ∃ L : V →L[ℂ] V, L ∘L H = 1 ∧ H ∘L L = 1 ∧
      ‖L‖ ≤ 2 * M ∧ ‖L - J‖ ≤ 2 * M ^ 2 * eta := by
  have hM : 0 ≤ M := (norm_nonneg J).trans hJ
  have heta : 0 ≤ eta := (norm_nonneg (H - N)).trans herror
  have hden : 0 < 1 - M * eta := by linarith
  obtain ⟨L, hLH, hHL, hL, hdiff⟩ := exists_inverse N J H hJN hNJ hJ herror (by linarith)
  refine ⟨L, hLH, hHL, hL.trans ?_, hdiff.trans ?_⟩
  · apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hM (show 0 ≤ 1 / 2 - M * eta by linarith)]
  · apply (div_le_iff₀ hden).mpr
    have hnum : 0 ≤ M ^ 2 * eta := by positivity
    nlinarith [mul_nonneg hnum (show 0 ≤ 1 / 2 - M * eta by linarith)]

end IntegerMultBounds.NLogN.InversePerturbation
