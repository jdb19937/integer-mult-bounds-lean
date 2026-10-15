module

public import IntegerMultBounds.MathlibTM2.Cost.DirectGrowth

/-! # Aggregate budget with linear CRT routing

This envelope charges both CRT passes linearly in the axis count. Its analytic
bound uses the direct routing margin. Connecting the executable pipeline to
this envelope remains a separate machine-cost obligation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter Asymptotics IntegerMultBounds

/-- The full stage envelope with direct CRT routing in both directions. -/
noncomputable def totDirectBound (C n : ℕ) : ℝ :=
  C * ((n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + totConv n + T n * totMp n) +
    T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C))

/-- `0 ≤ totDirectBound C n ≤ 40000 C n B^{1-κ}` for all large `n`. -/
theorem tot_direct_le (C : ℕ) :
    ∀ᶠ n in atTop, 0 ≤ totDirectBound C n ∧
      totDirectBound C n ≤ 40000 * C * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
  filter_upwards [tot_eventually C] with n ⟨h, hK, hlog, hbC, _⟩
  obtain ⟨he0, -⟩ := tot_exp_facts
  have hB1 := tot_one_le_b h
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hBe : 1 ≤ (b n : ℝ) ^ (1 - totKappa) := Real.one_le_rpow hB1 he0
  have hW : (n : ℝ) ≤ (n : ℝ) * (b n : ℝ) ^ (1 - totKappa) := le_mul_of_one_le_right hN hBe
  have hmargin : totKappa ≤ (1 - epsilon) * (1 - Parameters.tau) := by
    rw [tot_kappa_eq, epsilon_eq]; norm_num [Parameters.tau]
  have hcrt := tot_directCRT_le h totKappa hmargin
  have hres := tot_resamp_le h
  have hconv := tot_conv_le h hK hlog
  have hmp := tot_mp_le h
  have hS : (S n : ℝ) * totMp n ≤ (T n : ℝ) * totMp n := by
    have : (S n : ℝ) ≤ T n := by exact_mod_cast h.S_lt_T.le
    exact mul_le_mul_of_nonneg_right this (tot_mp_nonneg n)
  have hTp := gr_Tp_le h.1
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have h0 : 0 ≤ (n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + totConv n + T n * totMp n) +
      T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C) := by
    have c := @Nat.cast_nonneg ℝ _
    have a1 := tot_conv_nonneg h
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
  unfold totDirectBound
  have hsum : (n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + totConv n + T n * totMp n) +
      T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C) ≤
        40000 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
    have : 0 ≤ (n : ℝ) * (b n : ℝ) ^ (1 - totKappa) := by positivity
    linarith
  calc (C : ℝ) * _ ≤ C * (40000 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa))) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = 40000 * C * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by ring

/-- **The total-time bound**: `totDirectBound C = O(n (log n)^{1-κ})` at `κ = totKappa`. -/
theorem totDirectBound_isBigO_kappa (C : ℕ) :
    (fun n => totDirectBound C n) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - totKappa) := by
  have h1 : (fun n => totDirectBound C n) =O[atTop]
      fun n : ℕ => (n : ℝ) * (b n : ℝ) ^ (1 - totKappa) := by
    apply IsBigO.of_bound (40000 * C)
    filter_upwards [tot_direct_le C] with n ⟨h0, h⟩
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
    exact h
  exact h1.trans (gr_isBigO_b_rpow tot_exp_facts.1)

/-- **The hypothesis `htime` of `Fast.statement_of_dispatch`** at `κ = totKappa`, for an
`ℕ`-valued `time` bounded by `totDirectBound C` for all large `n`. -/
theorem tot_direct_htime (C : ℕ) {time : ℕ → ℕ} (h : ∀ᶠ n in atTop, (time n : ℝ) ≤ totDirectBound C n) :
    (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - totKappa) := by
  have h1 : (fun n => (time n : ℝ)) =O[atTop] fun n => totDirectBound C n := by
    apply IsBigO.of_bound 1
    filter_upwards [h, tot_direct_le C] with n hn ⟨h0, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg h0, one_mul]
    exact hn
  exact h1.trans (totDirectBound_isBigO_kappa C)

end IntegerMultBounds.MathlibTM2.Cost
