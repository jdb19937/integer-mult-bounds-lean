module

public import IntegerMultBounds.Schoenhage.RingPointwiseTarget
public import IntegerMultBounds.Machine.PackedMultiplierPolylogBudget
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The pointwise-product program at the main algorithm's sizes (`p = 6 lg n`,
`r = 2^ℓ`) costs at most a constant times its volume `T p` times the
`packedProducts` row times the `log log` overhead of
`PackedMultiplierPolylogBudget`, plus the header length
(`pointwise_le_packedProducts`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct Parameters Sizes TimeBound CostTable
open Machine.PackedMultiplierPolylogBudget

/-- `⌊log₂ x⌋ log 2 ≤ log x`. -/
theorem natLog_mul_log_two_le {x : ℕ} (hx : x ≠ 0) :
    (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
  have hpow : ((2 ^ Nat.log 2 x : ℕ) : ℝ) ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 hx
  have hlog := Real.log_le_log (by positivity) hpow
  rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hlog

/-- `⌊log₂ x⌋ + 1 ≤ 3 log x` once `x ≥ 6`. -/
theorem natLog_succ_le_three_log {x : ℕ} (hx : 6 ≤ x) :
    (Nat.log 2 x + 1 : ℝ) ≤ 3 * Real.log x := by
  have hmul := natLog_mul_log_two_le (x := x) (by omega)
  have hlog2 := Real.log_two_gt_d9
  have hlog6 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    have : (6 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hnat : (0 : ℝ) ≤ Nat.log 2 x := by positivity
  nlinarith

/-- The `log log` factor: `⌊log₂ (⌊log₂ x⌋ + 1)⌋ + 1 ≤ 4 (1 + max 0 (log log x))`. -/
theorem natLogLog_succ_le {x : ℕ} (hx : 6 ≤ x) :
    (Nat.log 2 (Nat.log 2 x + 1) + 1 : ℝ) ≤ 4 * (1 + max 0 (Real.log (Real.log x))) := by
  have hmul := natLog_mul_log_two_le (x := Nat.log 2 x + 1) (by omega)
  have hlog2 := Real.log_two_gt_d9
  have houter := natLog_succ_le_three_log hx
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hinner : Real.log ((Nat.log 2 x + 1 : ℕ) : ℝ) ≤ Real.log 3 + Real.log (Real.log x) := by
    rw [← Real.log_mul (by norm_num) hlogx.ne']
    exact Real.log_le_log (by positivity) (by push_cast; linarith)
  have hlog3 : Real.log 3 < 1.2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h32 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    have h2 := Real.log_two_lt_d9
    linarith
  have hmax := le_max_right 0 (Real.log (Real.log x))
  have hmax0 := le_max_left 0 (Real.log (Real.log x))
  have hnat : (0 : ℝ) ≤ Nat.log 2 (Nat.log 2 x + 1) := by positivity
  nlinarith

/-- At the main sizes, the pointwise program's time is at most a constant times
`T p` times the `packedProducts` row times its `log log` overhead, plus the header. -/
theorem pointwise_le_packedProducts (Cw : ℕ) (hCw : 2 ≤ Cw) :
    ∃ (t q a : ℕ) (M : Program t q a) (time : ℕ → ℕ → ℕ → ℕ → ℕ) (C : ℝ), 4 ≤ t ∧
      MeetsPointwise M Cw time ∧
      ∀ (n volume headerLength : ℕ),
        (time volume (6 * b n) (2 ^ ℓ n) headerLength : ℝ) ≤
          C * (volume * precision n * packedProducts n * overhead 1 n + headerLength) := by
  obtain ⟨t, q, a, M, C, ht, hM⟩ := pointwise_polylog Cw hCw
  refine ⟨t, q, a, M, _, 12 * C, ht, hM, fun n volume headerLength => ?_⟩
  set x := 2 ^ ℓ n * (6 * b n) with hx
  have hx6 : 6 ≤ x := by
    have := one_le_b n
    have := Nat.one_le_two_pow (n := ℓ n)
    nlinarith
  have hxreal : (x : ℝ) = r n * precision n := by
    rw [hx, precision_eq, r]; push_cast; ring
  have hrow : packedProducts n = Real.log x := by rw [hxreal]; rfl
  have hover : overhead 1 n = 1 + max 0 (Real.log (packedProducts n)) := by
    unfold overhead; rw [Real.rpow_one]
  have hA := natLog_succ_le_three_log hx6
  have hB := natLogLog_succ_le hx6
  rw [← hrow] at hA hB
  rw [← hover] at hB
  have hp : ((6 * b n : ℕ) : ℝ) = precision n := by rw [precision_eq]; push_cast; ring
  have hvol : (0 : ℝ) ≤ volume * precision n := by
    have := precision_pos n; positivity
  have hBnonneg : (0 : ℝ) ≤ Nat.log 2 (Nat.log 2 x + 1) + 1 := by positivity
  have hAnonneg : (0 : ℝ) ≤ Nat.log 2 x + 1 := by positivity
  rw [pow_one]
  push_cast
  rw [← precision_eq]
  have hC : (0 : ℝ) ≤ C := by positivity
  have hprod : (volume * precision n) * (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 (Nat.log 2 x + 1) + 1) ≤
      12 * (volume * precision n * packedProducts n * overhead 1 n) := by
    calc (volume * precision n) * (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 (Nat.log 2 x + 1) + 1)
        ≤ (volume * precision n) * (3 * packedProducts n) * (4 * overhead 1 n) := by
          gcongr
          · nlinarith
      _ = 12 * (volume * precision n * packedProducts n * overhead 1 n) := by ring
  have hH : (0 : ℝ) ≤ headerLength := by positivity
  nlinarith

end IntegerMultBounds.Schoenhage
