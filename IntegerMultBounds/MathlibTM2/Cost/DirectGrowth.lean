module

public import IntegerMultBounds.MathlibTM2.Cost.DirectScale
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Binary
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-! # Exponent margin for linear CRT routing

The routing margin is `(1-epsilon)*(1-tau)`, replacing the quadratic schedule's
`1-tau-epsilon*(2-tau)`. Other stages still constrain the final saving.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes

theorem tot_directCRT_le {n : ℕ} (h : Big n) (κ : ℝ)
    (hκ : κ ≤ (1 - epsilon) * (1 - Parameters.tau)) :
    totDirectCRT n ≤ 144 * ((n : ℝ) * (b n : ℝ) ^ (1 - κ)) := by
  have hB1 := tot_one_le_b h
  have hB : (0 : ℝ) < b n := by linarith
  have hD : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have hτ0 := tot_tau_nonneg
  have hτ1 := tot_tau_le_one
  have he := gr_epsilon_le_one
  have hexp : epsilon ≤ 1 - κ := by nlinarith
  have hcrt : epsilon * (1 - Parameters.tau) + Parameters.tau ≤ 1 - κ := by nlinarith
  have hd : (d n : ℝ) ≤ (b n : ℝ) ^ (1 - κ) :=
    (gr_d_le_rpow n).trans (Real.rpow_le_rpow_of_exponent_le hB1 hexp)
  have hDl : (d n : ℝ) * (ℓ n : ℝ) ^ Parameters.tau ≤ 2 * (b n : ℝ) ^ (1 - κ) := by
    have e1 : (d n : ℝ) * (ℓ n : ℝ) ^ Parameters.tau =
        (d n : ℝ) ^ (1 - Parameters.tau) * ((d n : ℝ) * ℓ n) ^ Parameters.tau := by
      rw [Real.mul_rpow hD.le (Nat.cast_nonneg _), ← mul_assoc, ← Real.rpow_add hD,
        sub_add_cancel, Real.rpow_one]
    have h1 : (d n : ℝ) ^ (1 - Parameters.tau) ≤
        1 * (b n : ℝ) ^ (epsilon * (1 - Parameters.tau)) := by
      rw [one_mul]; exact gr_d_rpow_le n (by linarith)
    have h2 : ((d n : ℝ) * ℓ n) ^ Parameters.tau ≤ 2 * (b n : ℝ) ^ Parameters.tau :=
      calc ((d n : ℝ) * ℓ n) ^ Parameters.tau ≤ (2 * (b n : ℝ)) ^ Parameters.tau :=
            Real.rpow_le_rpow (by positivity) (gr_dℓ_le h) hτ0
        _ = (2 : ℝ) ^ Parameters.tau * (b n : ℝ) ^ Parameters.tau :=
            Real.mul_rpow (by norm_num) hB.le
        _ ≤ 2 * (b n : ℝ) ^ Parameters.tau := by
            gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) hτ1
    rw [e1]
    have h3 := gr_mul_le hB (by positivity) (by norm_num) h1 h2
    have h4 := gr_le_rpow_of_le hB1 (by norm_num) h3 hcrt
    linarith
  have hsum : (d n : ℝ) * (1 + (ℓ n : ℝ) ^ Parameters.tau) ≤
      3 * (b n : ℝ) ^ (1 - κ) := by nlinarith
  have hTp := gr_Tp_le h.1
  unfold totDirectCRT
  calc (T n : ℝ) * p n * d n * (1 + (ℓ n : ℝ) ^ Parameters.tau) =
      ((T n : ℝ) * p n) * ((d n : ℝ) * (1 + (ℓ n : ℝ) ^ Parameters.tau)) := by ring
    _ ≤ (48 * n) * (3 * (b n : ℝ) ^ (1 - κ)) :=
      mul_le_mul hTp hsum (by positivity) (by positivity)
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
