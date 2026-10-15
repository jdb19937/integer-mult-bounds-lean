module

public import IntegerMultBounds.MathlibTM2.Cost.CompactStageGrowth
public import IntegerMultBounds.MathlibTM2.Cost.DirectGrowth

/-! Stronger aggregate analytic envelope for the retuned compact multiplier.
The fixed-machine theorem still needs an actual execution-cost match to this envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactTotal
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Mult.Sizes hiding K cParam
noncomputable section

theorem regime (C : ℕ) : ∀ᶠ n in atTop,
    Big n ∧ 1≤K n ∧ Real.logb 2 (p n)≤K n ∧ (b n:ℝ)^C≤n ∧ 8≤n := by
  filter_upwards [tot_eventually C] with n ⟨h,hK,hlog,hbC,hn⟩
  have hk := Mult.CompactSizes.old_K_le_K n
  refine ⟨h,hK.trans hk,?_,hbC,hn⟩
  exact hlog.trans (by exact_mod_cast hk)

/-- The full stage envelope with direct CRT routing in both directions. -/
noncomputable def bound (C n : ℕ) : ℝ :=
  C * ((n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + conv n + T n * totMp n) +
    T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C))

/-- `0 ≤ bound C n ≤ 65536 C n B^{1-κ}` for all large `n`. -/
theorem bound_le (C : ℕ) :
    ∀ᶠ n in atTop, 0 ≤ bound C n ∧
      bound C n ≤ 65536 * C * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
  filter_upwards [regime C] with n ⟨h, hK, hlog, hbC, _⟩
  obtain ⟨he0, -⟩ := exp_facts
  have hB1 := tot_one_le_b h
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hBe : 1 ≤ (b n : ℝ) ^ (1 - kappa) := Real.one_le_rpow hB1 he0
  have hW : (n : ℝ) ≤ (n : ℝ) * (b n : ℝ) ^ (1 - kappa) := le_mul_of_one_le_right hN hBe
  have hmargin : kappa ≤ (1 - epsilon) * (1 - Parameters.tau) := by
    have hdirect := exp_facts.2.2.1
    nlinarith
  have hcrt := tot_directCRT_le h kappa hmargin
  have hres := resamp_le h
  have hconv := conv_le h hK hlog
  have hmp := mp_le h
  have hS : (S n : ℝ) * totMp n ≤ (T n : ℝ) * totMp n := by
    have : (S n : ℝ) ≤ T n := by exact_mod_cast h.S_lt_T.le
    exact mul_le_mul_of_nonneg_right this (tot_mp_nonneg n)
  have hTp := gr_Tp_le h.1
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have h0 : 0 ≤ (n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + conv n + T n * totMp n) +
      T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C) := by
    have c := @Nat.cast_nonneg ℝ _
    have a1 := conv_nonneg h
    have a2 := mt_directCRT_nonneg n
    have a3 : 0 ≤ totResamp n :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (c _) (c _)) (Real.rpow_nonneg (c _) _))
        (c _)) (tot_mp_nonneg n)
    have a4 : 0 ≤ (T n : ℝ) * totMp n := mul_nonneg (c _) (tot_mp_nonneg n)
    have a5 : 0 ≤ (S n : ℝ) * totMp n := mul_nonneg (c _) (tot_mp_nonneg n)
    have a6 : 0 ≤ (T n : ℝ) * p n := mul_nonneg (c _) (c _)
    have a7 : 0 ≤ (b n : ℝ) ^ C := pow_nonneg (c _) _
    linarith
  refine ⟨mul_nonneg hC h0, ?_⟩
  unfold bound
  have hsum : (n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + conv n + T n * totMp n) +
      T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C) ≤
        65536 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by
    have : 0 ≤ (n : ℝ) * (b n : ℝ) ^ (1 - kappa) := by positivity
    linarith
  calc (C : ℝ) * _ ≤ C * (65536 * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa))) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = 65536 * C * ((n : ℝ) * (b n : ℝ) ^ (1 - kappa)) := by ring

/-- **The total-time bound**: `bound C = O(n (log n)^{1-κ})` at `κ = kappa`. -/
theorem bound_isBigO (C : ℕ) :
    (fun n => bound C n) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - kappa) := by
  have h1 : (fun n => bound C n) =O[atTop]
      fun n : ℕ => (n : ℝ) * (b n : ℝ) ^ (1 - kappa) := by
    apply IsBigO.of_bound (65536 * C)
    filter_upwards [bound_le C] with n ⟨h0, h⟩
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
    exact h
  exact h1.trans (gr_isBigO_b_rpow exp_facts.1)

/-- **The hypothesis `htime` of `Fast.statement_of_dispatch`** at `κ = kappa`, for an
`ℕ`-valued `time` bounded by `bound C` for all large `n`. -/
theorem htime (C : ℕ) {time : ℕ → ℕ} (h : ∀ᶠ n in atTop, (time n : ℝ) ≤ bound C n) :
    (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - kappa) := by
  have h1 : (fun n => (time n : ℝ)) =O[atTop] fun n => bound C n := by
    apply IsBigO.of_bound 1
    filter_upwards [h, bound_le C] with n hn ⟨h0, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg h0, one_mul]
    exact hn
  exact h1.trans (bound_isBigO C)

end
end IntegerMultBounds.MathlibTM2.Cost.CompactTotal
