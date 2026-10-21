module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Width
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cost of the stage-2 core

At the atom width `w = atomWidth K e`, `n = e / w` atoms and `L = w^τ₁ + size w`, the nine
pieces of the core cost at most a constant times `V e^τ₂` (`core_le`): the header switches
`D size e V`, the shears `D (n + 1) V`, the two family runs the family bound, the leaf
`D w^τ₁ V`, and the eight sequencing steps.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Cost

noncomputable section
open Stage2Width (atomWidth tau2)
open FamilyRoot (bound)

/-- The family's exponent. -/
abbrev tauS : ℝ := 1 - (Stage2Moments.saving : ℝ)

theorem one_sub_q₁ : 0 < 1 - (Stage2Moments.q₁ : ℝ) := by
  have := Stage2Moments.q₁_lt_one; have : (Stage2Moments.q₁ : ℝ) < 1 := by exact_mod_cast this
  linarith

theorem one_sub_qτ : 0 < 1 - (Stage2Moments.qτ : ℝ) := by
  have := Stage2Moments.qτ_lt_one; have : (Stage2Moments.qτ : ℝ) < 1 := by exact_mod_cast this
  linarith

theorem tauS_nonneg : 0 ≤ tauS := by
  unfold tauS; norm_num [Stage2Moments.saving]

/-- The constant of the core. -/
def constant (C D : ℝ) : ℝ :=
  2 * (C / (1 - Stage2Moments.q₁)) + 6 * (2 * (C / (1 - Stage2Moments.qτ))) + 6 * (3 * D) + 8

/-- **The core's cost.** -/
theorem core_le {K : ℕ} (hK : 2 ≤ K) {τ₁ : ℝ} (hs1 : tauS ≤ τ₁) (hτ₁ : τ₁ ≤ 1)
    (hhalf : 1 / 2 ≤ τ₁) (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ tauS τ₁)
    (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ tauS τ₁)
    {C D V : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 1 ≤ V) {e : ℕ} (he : 2 ≤ e)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℕ}
    (hh : (c₁ + c₇ + c₉ : ℝ) ≤ D * Nat.size e * V)
    (hs : (c₂ + c₄ + c₆ : ℝ) ≤ D * ((e / atomWidth K e : ℕ) + 1) * V)
    (hf : (c₃ + c₅ : ℝ) ≤ 2 * (bound C ((atomWidth K e : ℝ) ^ τ₁ + Nat.size (atomWidth K e))
      (e / atomWidth K e) * V))
    (hl : (c₈ : ℝ) ≤ D * (atomWidth K e : ℝ) ^ τ₁ * V) :
    ((c₁ + 1 + c₂ + 1 + c₃ + 1 + c₄ + 1 + c₅ + 1 + c₆ + 1 + c₇ + 1 + c₈ + 1 + c₉ : ℕ) : ℝ) ≤
      constant C D * V * (e : ℝ) ^ tau2 (K : ℝ)⁻¹ tauS τ₁ := by
  set w := atomWidth K e
  set n := e / w
  set τ₂ := tau2 (K : ℝ)⁻¹ tauS τ₁
  set A := C / (1 - (Stage2Moments.q₁ : ℝ))
  set B := C / (1 - (Stage2Moments.qτ : ℝ))
  have hA : 0 ≤ A := div_nonneg hC one_sub_q₁.le
  have hB : 0 ≤ B := div_nonneg hC one_sub_qτ.le
  have hw := (Stage2Width.wrapped_le hK tauS_nonneg hs1 hτ₁ hhalf h2 hlin (A := 2 * A) (B := 2 * B)
    (D := 3 * D) (by positivity) (by positivity) (by positivity) he).2.2.2
  have hE : (1 : ℝ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
  have hEτ : 1 ≤ (e : ℝ) ^ τ₂ := Real.one_le_rpow hE (by linarith)
  have hfam : (c₃ + c₅ : ℝ) ≤ (2 * A * n + 2 * B * (n : ℝ) ^ tauS * ((w : ℝ) ^ τ₁ + Nat.size w)) * V := by
    refine hf.trans (le_of_eq ?_)
    simp only [bound, tauS, A, B]
    ring
  have hsum : (c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈ + c₉ : ℝ) ≤
      (2 * A * n + 2 * B * (n : ℝ) ^ tauS * ((w : ℝ) ^ τ₁ + Nat.size w) + 3 * D * (w : ℝ) ^ τ₁ +
        3 * D * Nat.size e + 3 * D * ((n : ℝ) + 1)) * V := by
    have hw0 : 0 ≤ D * (w : ℝ) ^ τ₁ * V := by positivity
    have hs0 : 0 ≤ D * Nat.size e * V := by positivity
    have hn0 : 0 ≤ D * ((n : ℝ) + 1) * V := by positivity
    nlinarith
  have hmain := mul_le_mul_of_nonneg_right hw (by linarith : (0 : ℝ) ≤ V)
  push_cast
  have h8 : (8 : ℝ) ≤ 8 * V * (e : ℝ) ^ τ₂ := by nlinarith
  calc _ = (c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈ + c₉ : ℝ) + 8 := by ring
    _ ≤ (2 * A + 6 * (2 * B) + 6 * (3 * D)) * (e : ℝ) ^ τ₂ * V + 8 * V * (e : ℝ) ^ τ₂ := by
        nlinarith
    _ = constant C D * V * (e : ℝ) ^ τ₂ := by unfold constant; ring

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Cost
