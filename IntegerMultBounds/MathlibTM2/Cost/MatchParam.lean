module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Fast.Input
public import IntegerMultBounds.MathlibTM2.Fast.Output

/-!
# Cost matching: parameters, input and output

The stages F1, F2 (parameter machine), F3 and F11 of `docs/fast-pipeline.md` against the terms
`n` and `n + B^C` of `Cost/Total.totBound` (`B = b n`, `n` the input length).

* `mt_pm_le` (F2, `pmParams_exec`): `pmCost n us ≤ (17 + 1100 |us|) n + 3361400001 B⁴` whenever
  every requested unary copy is a value at most `T` (`pmCost_le`, `pm_W_T_le`); the unary copies
  of `T` and `r` cost `O(n)` each. `mt_pm_vals_le_T`: the values `b, p, d, K, log T, T, ℓ, r,
  ℓ - 1, 2^(ℓ-1), numHalf, α, α², γ, q, S` are eventually at most `T`. `mt_pm_le_real`: the
  bound against `n + B^C` for every `C ≥ 4`.
* `mt_input_le` (F1, `readInput_exec`): `4 n + 6 ≤ 10 n` steps for the input of length `n ≥ 1`.
* `mt_digit_le` (F3, `digitRecords_exec`): `digitCost b p w S ≤ 3072 cw n` for `w ≤ cw p`.
* `mt_carry_le` (F11, `carryOut_exec`): `carryOutCost W b S ≤ 2304 (cW + 1) n` for words of
  `W ≤ cW p` bits.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! ### The parameter machine -/

/-- One unary copy of a value `x ≤ T` costs at most `1100 n`. -/
theorem mt_pm_unary_one {n x : ℕ} (hn : 2 ≤ n) (hx : x ≤ T n) :
    pmW n * (4 * x + 11) + 2 * x + 6 ≤ 1100 * n := by
  have h1 := pm_W_T_le hn
  have h2 : Nat.size n ≤ b n + 1 := pm_size_le
  have h3 := b_lt_two_mul hn
  have h4 := bT_lt hn
  have hb := one_le_b hn
  have hT : T n ≤ 8 * n := by nlinarith
  have h5 : pmW n * x ≤ pmW n * T n := Nat.mul_le_mul_left _ hx
  have hW : pmW n = 4 * Nat.size n + 16 := rfl
  have e : pmW n * (4 * x + 11) = 4 * (pmW n * x) + 11 * pmW n := by ring
  rw [e]
  omega

/-- The unary copies of values at most `T` cost at most `1100 n` each. -/
theorem mt_pm_unary_le {n : ℕ} (hn : 2 ≤ n) {α : Type} (us : List (Fin pmNV × α))
    (hus : ∀ x ∈ us, pmVals n x.1 ≤ T n) :
    pmUnaryCost (pmW n) (pmVals n) us ≤ 1100 * us.length * n + 1 := by
  unfold pmUnaryCost
  have : (us.map fun x => pmW n * (4 * pmVals n x.1 + 11) + 2 * pmVals n x.1 + 6).sum ≤
      us.length * (1100 * n) := by
    have := List.sum_le_card_nsmul (us.map fun x => pmW n * (4 * pmVals n x.1 + 11) +
      2 * pmVals n x.1 + 6) (1100 * n) (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact mt_pm_unary_one hn (hus x hx))
    simpa using this
  nlinarith

/-- **The parameter machine** (`pmParams_exec`): for `n ≥ 2` and unary copies of values at most
`T`, `pmCost n us ≤ (17 + 1100 |us|) n + 3361400001 B⁴`. -/
theorem mt_pm_le {n : ℕ} (hn : 2 ≤ n) {α : Type} (us : List (Fin pmNV × α))
    (hus : ∀ x ∈ us, pmVals n x.1 ≤ T n) :
    pmCost n us ≤ (17 + 1100 * us.length) * n + 3361400001 * b n ^ 4 := by
  have h1 := pmCost_le hn us
  have h2 := mt_pm_unary_le hn us hus
  have h3 : Nat.size n ≤ b n + 1 := pm_size_le
  have hb := one_le_b hn
  have h4 : (Nat.size n + 5) ^ 4 ≤ (7 * b n) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h5 : (7 * b n) ^ 4 = 2401 * b n ^ 4 := by ring
  have h6 : 1 ≤ b n ^ 4 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- `mt_pm_le` against `n + B^C` for `C ≥ 4`. -/
theorem mt_pm_le_real {n C : ℕ} (hn : 2 ≤ n) (hC : 4 ≤ C) {α : Type} (us : List (Fin pmNV × α))
    (hus : ∀ x ∈ us, pmVals n x.1 ≤ T n) :
    (pmCost n us : ℝ) ≤ (3361400018 + 1100 * us.length) * ((n : ℝ) + (b n : ℝ) ^ C) := by
  have h := mt_pm_le hn us hus
  have hb : 1 ≤ b n := one_le_b hn
  have hbC : b n ^ 4 ≤ b n ^ C := Nat.pow_le_pow_right hb hC
  have h' : (pmCost n us : ℝ) ≤ (17 + 1100 * us.length) * n + 3361400001 * (b n : ℝ) ^ C := by
    have : pmCost n us ≤ (17 + 1100 * us.length) * n + 3361400001 * b n ^ C := by
      have := Nat.mul_le_mul_left 3361400001 hbC
      omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (b n : ℝ) ^ C := by positivity
  have hl : (0 : ℝ) ≤ us.length := Nat.cast_nonneg _
  nlinarith

/-- The indices of the parameter values that are eventually at most `T`. -/
def mtPmSmall : List (Fin pmNV) :=
  [pmIb, pmIp, pmId, pmIK, pmIlogT, pmIT, pmIℓ, pmIr, pmIe, pmIR, pmInumHalf, pmIalpha,
    pmIalphaSq, pmIgamma, pmIq, pmIS]

/-- The values `b, p, d, K, log T, T, ℓ, r, ℓ - 1, 2^(ℓ-1), numHalf, α, α², γ, q, S` of the
parameter machine are eventually at most `T`; their unary copies cost `O(n)` (`mt_pm_le`). -/
theorem mt_pm_vals_le_T : ∀ᶠ n in atTop, ∀ i ∈ mtPmSmall, pmVals n i ≤ T n := by
  filter_upwards [eventually_big, mt_poly_r_le_T 6 1] with n h hP
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hbT : 6 * b n ≤ T n := by
    have : 6 * b n ^ 1 ≤ 6 * b n ^ 1 * r n := Nat.le_mul_of_pos_right _ hr1
    rw [pow_one] at this hP
    omega
  have hrT := mt_r_le_T h
  have hp : p n = 6 * b n := rfl
  have hd := mt_d_le_b n
  have hK := mt_K_le_b n
  have hlT := mt_logT_le_b h
  have hl := mt_ℓ_le_b h
  have hα := mt_alpha_le_p h
  have hα2 := h.alpha_sq_le_p
  have hγ := h.four_gamma_le_b
  have hnh := numHalf_lt h.one_le_d
  have hS := h.S_lt_T
  have hR : 2 ^ (ℓ n - 1) ≤ r n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hq : q n ≤ T n := by
    have h4 := four_mul_le_bT h.1
    have hb1 : 1 ≤ b n := one_le_b h.1
    unfold q
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : n ≤ T n * b n := by nlinarith
    omega
  intro i hi
  simp only [mtPmSmall, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · rw [pm_b_eq]; omega
  · rw [pm_p_eq]; omega
  · rw [pm_d_eq]; omega
  · rw [pm_K_eq]; omega
  · rw [pm_logT_eq]; omega
  · rw [pm_T_eq]
  · rw [pm_ℓ_eq]; omega
  · rw [pm_r_eq]; exact hrT
  · rw [pm_e_eq]; omega
  · rw [pm_R_eq]; omega
  · rw [pm_numHalf_eq]; omega
  · rw [pm_alpha_eq]; omega
  · rw [pm_alphaSq_eq]; omega
  · rw [pm_gamma_eq]; omega
  · rw [pm_q_eq]; exact hq
  · rw [pm_S_eq]; omega

/-- **The parameter machine against `n + B^C`**: for every list of unary copies `us` of the
values `mtPmSmall` and every `C ≥ 4`, eventually
`pmCost n us ≤ (3361400018 + 1100 |us|) (n + B^C)`. -/
theorem mt_pm_stage_le (C : ℕ) (hC : 4 ≤ C) {α : Type} (us : List (Fin pmNV × α))
    (hus : ∀ x ∈ us, x.1 ∈ mtPmSmall) :
    ∀ᶠ n in atTop,
      (pmCost n us : ℝ) ≤ (3361400018 + 1100 * us.length) * ((n : ℝ) + (b n : ℝ) ^ C) := by
  filter_upwards [eventually_big, mt_pm_vals_le_T] with n h hv
  exact mt_pm_le_real h.1 hC us fun x hx => hv x.1 (hus x hx)

/-! ### Input and output -/

/-- **Reading the input** (`readInput_exec`): `4 n + 6 ≤ 10 n` steps for an input of length
`n ≥ 1`. -/
theorem mt_input_le {n : ℕ} (hn : 1 ≤ n) : ((4 * n + 6 : ℕ) : ℝ) ≤ 10 * n := by
  have : 4 * n + 6 ≤ 10 * n := by omega
  exact_mod_cast this

/-- **The digit stage** (`digitRecords_exec` at `b n`, `p n`, `w`, `S n`): at most `3072 cw n`
steps for `p n ≤ w ≤ cw p n`. -/
theorem mt_digit_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, p n ≤ w → w ≤ cw * p n →
      (digitCost (b n) (p n) w (S n) : ℝ) ≤ 3072 * cw * n := by
  filter_upwards [eventually_big] with n h w hpw hwc
  have hb : 1 ≤ b n := one_le_b h.1
  have hbp : b n + 2 ≤ p n := by unfold p; omega
  have h1 := digitCost_le (S := S n) hb hbp hpw
  have hST : S n + 1 ≤ 2 * T n := by have := h.S_lt_T; have : 1 ≤ T n := Nat.one_le_two_pow; omega
  have hTp : T n * p n < 48 * n := (volume_bounds h.1).2
  have h2 : (S n + 1) * w ≤ 2 * T n * (cw * p n) := Nat.mul_le_mul hST hwc
  have h3 : 2 * T n * (cw * p n) = 2 * cw * (T n * p n) := by ring
  have h4 : 2 * cw * (T n * p n) ≤ 2 * cw * (48 * n) := Nat.mul_le_mul_left _ hTp.le
  have : digitCost (b n) (p n) w (S n) ≤ 3072 * cw * n := by nlinarith
  exact_mod_cast this

/-- **The carries and the output** (`carryOut_exec` on `S n` words of `W ≤ cW p n` bits, base
`2^(b n)`): at most `2304 (cW + 1) n` steps. -/
theorem mt_carry_le (cW : ℕ) :
    ∀ᶠ n in atTop, ∀ W : ℕ, W ≤ cW * p n →
      (carryOutCost W (b n) (S n) : ℝ) ≤ 2304 * (cW + 1) * n := by
  filter_upwards [eventually_big] with n h W hW
  have hb : 1 ≤ b n := one_le_b h.1
  have h1 := carryOutCost_le (W := W) (n := S n) hb
  have hST : S n + 1 ≤ 2 * T n := by have := h.S_lt_T; have : 1 ≤ T n := Nat.one_le_two_pow; omega
  have hTp : T n * p n < 48 * n := (volume_bounds h.1).2
  have hp : p n = 6 * b n := rfl
  have hb16 := h.sixteen_le_b
  have h2 : 10 * W + 6 * b n + 15 ≤ (10 * cW + 2) * p n := by nlinarith
  have h3 : (S n + 1) * (10 * W + 6 * b n + 15) ≤ 2 * T n * ((10 * cW + 2) * p n) :=
    Nat.mul_le_mul hST h2
  have h4 : 2 * T n * ((10 * cW + 2) * p n) = 2 * (10 * cW + 2) * (T n * p n) := by ring
  have h5 : 2 * (10 * cW + 2) * (T n * p n) ≤ 2 * (10 * cW + 2) * (48 * n) :=
    Nat.mul_le_mul_left _ hTp.le
  have : carryOutCost W (b n) (S n) ≤ 2304 * (cW + 1) * n := by nlinarith
  exact_mod_cast this

end IntegerMultBounds.MathlibTM2.Cost
