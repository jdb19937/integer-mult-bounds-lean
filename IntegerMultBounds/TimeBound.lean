module

import IntegerMultBounds.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import IntegerMultBounds.BinaryWords
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import IntegerMultBounds.Parameters

/-! The complete time bound (§8). With precision `p = 6 lg n` and padded volume
`V = Θ(n)`, every operation of the multiplication algorithm costs a fixed
multiple of `V (log p)^k p^(1 - g)` for one of the seven margins `g`, or is a
setup cost polynomial in `p`, or is a fixed multiple of `V` times a quantity
eventually bounded. Since every margin exceeds `κ`, the total is eventually
`O(n (lg n)^(1 - κ))`, the target time of `Machine.ComputesWithin`. These are
statements about cost functions; the costs themselves are supplied by the
algorithm's components. -/

@[expose] public section

namespace IntegerMultBounds.TimeBound

open Filter Asymptotics Parameters

/-- The working precision, as a real number. -/
noncomputable def precision (n : ℕ) : ℝ := 6 * (lg n : ℝ)

theorem one_le_lg (n : ℕ) : 1 ≤ lg n := le_max_right _ _

theorem six_le_precision (n : ℕ) : 6 ≤ precision n := by
  unfold precision
  have : (1 : ℝ) ≤ lg n := by exact_mod_cast one_le_lg n
  linarith

theorem precision_pos (n : ℕ) : 0 < precision n := by linarith [six_le_precision n]

/-- `lg n` is at least `log n / log 2`. -/
theorem log_le_lg (n : ℕ) : Real.log n / Real.log 2 ≤ lg n := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ h2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hle : n ≤ 2 ^ lg n := by
    calc n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
      _ ≤ 2 ^ lg n := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have hle' : (n : ℝ) ≤ (2 : ℝ) ^ (lg n : ℕ) := by exact_mod_cast hle
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.log n ≤ Real.log ((2 : ℝ) ^ (lg n : ℕ)) :=
        (Real.log_le_log_iff hnpos (by positivity)).mpr hle'
    _ = (lg n : ℝ) * Real.log 2 := by rw [Real.log_pow]

theorem tendsto_precision : Tendsto precision atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => Real.log n / Real.log 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (Real.log_pos (by norm_num))
  have h2 : Tendsto (fun n : ℕ => (lg n : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => log_le_lg n) h1
  exact h2.const_mul_atTop (by norm_num)

section Rows

/-- A dominant row: normalized cost `C (log p)^k p^e`. -/
structure Row where
  C : ℝ
  k : ℝ
  e : ℝ

/-- The cost of a dominant row on volume `V` at precision `p`. -/
noncomputable def Row.cost (r : Row) (V p : ℝ) : ℝ := r.C * V * Real.log p ^ r.k * p ^ r.e

variable {κ : ℝ} (hκ1 : κ ≤ 1) (V : ℕ → ℝ) (cV : ℝ) (hV0 : ∀ n, 0 ≤ V n)
  (hV : ∀ n, V n ≤ cV * n)

end Rows

end IntegerMultBounds.TimeBound
