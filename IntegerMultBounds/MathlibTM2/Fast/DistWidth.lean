module

public import IntegerMultBounds.MathlibTM2.Fast.Dist
public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGen
public import IntegerMultBounds.MathlibTM2.Fast.ConvBox

/-!
# The widths of the pipeline

The coefficient width `dsW n = p + g + 3 + Σ aᵢ` (`g = chirpGuard d`, `Σ aᵢ = logT - ℓ`, the
address bits of the synthetic transform) and the table word size
`dsWW n = 16 p + 8 g + 3 ℓ + dsW n + 128`, and the width hypotheses of the stages at these
values:

* chirp (`ldChirpStage_exec`): `p + g + 3 ≤ w` (`ds_w_chirp`), `w < W` (`ds_w_lt_WT`),
  `s_k t_k² < 2^W` (`ds_chirp_sN`), `8 (p + g) + size t_k + 80 ≤ W` (`ds_chirp_W`);
* `Ã` (`rsaStage_exec`): `p + 3 ≤ w`, `w ≤ W`, `α² ((s + t)(windowA + 1))² 2^(13p+8) < 2^W`
  (`ds_A_W`);
* `B̃₀` (`rsbStage_exec`): `p + 2 ≤ w`, `w ≤ W`, the same with `fastWindow` (`ds_B_W`);
* ring and convolution (`ldRpStage_exec`, `cvBox_convBox`): `p + 2 ≤ w`, `Σ aᵢ ≤ w`
  (`ds_conv_w`, `ds_sum_cvAx`: `Σ aᵢ = logT - ℓ`);
* layout (`ldLayGenStage_exec`) at `es = List.ofFn (cvAx t)`, `W_L = dsWL n w`, `B = r w`,
  `E = dsE n`: `LayHyp` (`ds_layHyp`), the long-axis word (`ds_lay_E`), `E < 2^W_L`,
  `(N + 1)^N < 2^W_L`, `N + B + 4 ≤ W_L`, `ℓ < 2^W_L` (`ds_lay_widths`);
* the layer (`topProg_exec`): `s + w ≤ w'` constrains the per-round working width `w'` only;
* the distribution machine itself (`dsIoAll_runs`): `dsWW n < 2^pmW n`, `4 dsW n + 2 < 2^pmW n`,
  `pmW n ≤ dsWL n (dsW n)` (`ds_widths_dist`).

The bounds `ds_d_le_r` (`d ≤ r`), `ds_d_mul_r_le` (`d r ≤ T`), `dsS_le` (`s_i ≤ 2 r + 23`),
`dsP_le_Tr`, `dsG_le_Tr` (`P_i, G_i ≤ T / r`) hold for every `n ≥ 2`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The coefficient width: `10 p + chirpGuard d + 3 + Σ aᵢ`, `Σ aᵢ = logT - ℓ`; the banded `B̃₀` needs about `10 p`. -/
def dsW (n : ℕ) : ℕ := 10 * p n + Chirp.chirpGuard (d n) + 3 + (logT n - ℓ n)

/-- The table word size of the `Ã`, `B̃₀` and chirp loaders. -/
def dsWW (n : ℕ) : ℕ := 70 * p n + 8 * Chirp.chirpGuard (d n) + 3 * ℓ n + dsW n + 128

section Bounds

variable {n : ℕ}

theorem dsT_pow (n i : ℕ) : dsT n i = 2 ^ dsL n i := by
  unfold dsT pmTv dsL r; split_ifs <;> rfl

theorem dsP_pow (n : ℕ) : ∀ i, dsP n i = 2 ^ ∑ j ∈ Finset.range i, dsL n j
  | 0 => rfl
  | i + 1 => by rw [dsP_succ, dsP_pow n i, dsT_pow, Finset.sum_range_succ, pow_add]

/-- `Σ_{i < d - 1} log₂ t_i = logT - ℓ`. -/
theorem ds_sumL (hn : 2 ≤ n) : ∑ j ∈ Finset.range (d n - 1), dsL n j = logT n - ℓ n := by
  have h := dsP_last hn
  rw [dsP_pow, r, T, ← pow_add] at h
  have := Nat.pow_right_injective (le_refl 2) h
  omega

/-- `Σ aᵢ = logT - ℓ` for the axes of the synthetic transform. -/
theorem ds_sum_cvAx (hn : 2 ≤ n) :
    (List.ofFn (ConvSt.cvAx (t n))).sum = logT n - ℓ n := by
  rw [List.sum_ofFn, ← ds_sumL hn, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ds_log_t n _

theorem ds_one_le_ℓ (hn : 2 ≤ n) : 1 ≤ ℓ n := pm_one_le_ℓ hn

theorem ds_two_le_r (hn : 2 ≤ n) : 2 ≤ r n := by
  have := ds_one_le_ℓ hn
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ r n := Nat.pow_le_pow_right (by norm_num) this

/-- `d ≤ r`. -/
theorem ds_d_le_r (hn : 2 ≤ n) : d n ≤ r n := by
  rcases Nat.lt_or_ge (d n) 2 with h | h
  · have := ds_two_le_r hn; omega
  · have h1 := pm_room hn h
    have h2 : 2 ^ (ℓ n - 1) ≤ r n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    nlinarith

/-- `T / r = P_{d-1}`. -/
theorem ds_T_div_r (hn : 2 ≤ n) : T n / r n = dsP n (d n - 1) := by
  rw [← dsP_last hn, Nat.mul_div_cancel _ (by have := ds_two_le_r hn; omega)]

/-- `d r ≤ T`. -/
theorem ds_d_mul_r_le (hn : 2 ≤ n) : d n * r n ≤ T n := by
  rw [← dsP_last hn]
  refine Nat.mul_le_mul_right _ ?_
  rcases Nat.lt_or_ge (d n) 2 with h | h
  · have := one_le_d hn
    have e : d n = 1 := by omega
    rw [e]; exact le_rfl
  · have h1 := pm_room hn h
    have h2 : dsP n 1 ≤ dsP n (d n - 1) :=
      Nat.le_of_dvd (dsP_pos n _) (dsP_dvd n (by omega))
    have h3 : 2 ^ (ℓ n - 1) ≤ dsT n 0 := by
      unfold dsT pmTv r; split_ifs
      · exact le_rfl
      · exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    rw [show dsP n 1 = dsT n 0 by simp [dsP]] at h2
    nlinarith

/-- `s_i ≤ 2 r + 23`. -/
theorem dsS_le (hn : 2 ≤ n) {i : ℕ} (hi : i < d n) : dsS n i ≤ 2 * r n + 23 := by
  have h1 := pm_modulus_le_bound (N n) (pmX0 n) (numHalf n) i
  have h2 : pmModBound (N n) (pmX0 n) i ≤ 2 * 2 ^ (ℓ n - 1) + N n * (2 * d n + 5) + 2 :=
    pm_modBound_le (R := 2 ^ (ℓ n - 1)) (one_le_d hn) (pm_one_le_N n) hi
  have hR : 2 * 2 ^ (ℓ n - 1) = r n := by
    have := ds_one_le_ℓ hn
    unfold r
    rw [← pow_succ']; congr 1; omega
  unfold dsS
  rcases Nat.lt_or_ge (d n) 2 with h | h
  · have e : d n = 1 := by have := one_le_d hn; omega
    have hN : N n = 3 := by simp [N, e, oddProd, Finset.prod_range_succ]
    have h3 : N n * (2 * d n + 5) = 21 := by rw [e, hN]
    omega
  · have h3 := pm_room hn h
    have h4 : N n * (2 * d n + 5) ≤ 8 * d n ^ 2 * N n := by
      have : 2 * d n + 5 ≤ 8 * d n ^ 2 := by nlinarith
      calc N n * (2 * d n + 5) ≤ N n * (8 * d n ^ 2) := Nat.mul_le_mul_left _ this
        _ = 8 * d n ^ 2 * N n := by ring
    omega

/-- `P_i ≤ T / r` for `i < d`. -/
theorem dsP_le_Tr (hn : 2 ≤ n) {i : ℕ} (hi : i < d n) : dsP n i ≤ T n / r n := by
  rw [ds_T_div_r hn]
  exact Nat.le_of_dvd (dsP_pos n _) (dsP_dvd n (by omega))

/-- `G_i ≤ T / r`. -/
theorem dsG_le_Tr (hn : 2 ≤ n) (i : ℕ) : dsG n i ≤ T n / r n := by
  have hr := ds_two_le_r hn
  by_cases hi : i + 1 < d n
  · have h := dsG_mul hn hi
    rw [Nat.le_div_iff_mul_le (by omega), ← h]
    have h1 : 1 ≤ dsP n i * dsT n i := Nat.mul_pos (dsP_pos n i) (dsT_pos n i)
    calc dsG n i * r n = 1 * dsG n i * r n := by ring
      _ ≤ dsP n i * dsT n i * dsG n i * r n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
  · unfold dsG
    rw [if_neg hi, ds_T_div_r hn]
    exact dsP_pos n _

end Bounds

/-! ### The width hypotheses -/

section Widths

variable {n : ℕ}

theorem ds_w_chirp (n : ℕ) : p n + Chirp.chirpGuard (d n) + 3 ≤ dsW n := by unfold dsW; omega

theorem ds_w_A (n : ℕ) : p n + 3 ≤ dsW n := by unfold dsW; omega

theorem ds_w_B (n : ℕ) : p n + 2 ≤ dsW n := by unfold dsW; omega

theorem ds_w_lt_WT (n : ℕ) : dsW n < dsWW n := by unfold dsWW; omega

theorem ds_w_le_WT (n : ℕ) : dsW n ≤ dsWW n := (ds_w_lt_WT n).le

/-- The convolution: `Σ aᵢ ≤ w`. -/
theorem ds_conv_w (hn : 2 ≤ n) : (List.ofFn (ConvSt.cvAx (t n))).sum ≤ dsW n := by
  rw [ds_sum_cvAx hn]; unfold dsW; omega

theorem ds_t_le_pow (n : ℕ) (k : Fin (d n)) : t n k ≤ 2 ^ ℓ n := by
  rw [← dsT_eq]
  unfold dsT pmTv
  split_ifs
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  · exact le_rfl

/-- The chirp loader: `s_k t_k² < 2^W`. -/
theorem ds_chirp_sN (hbig : Big n) (k : Fin (d n)) : s n k * t n k * t n k < 2 ^ dsWW n := by
  have hst := hbig.good.lt k
  have ht := ds_t_le_pow n k
  have h1 : s n k * t n k * t n k < 2 ^ ℓ n * 2 ^ ℓ n * 2 ^ ℓ n := by
    have := Nat.mul_le_mul ht ht
    have hpos : 0 < t n k := by omega
    calc s n k * t n k * t n k < t n k * t n k * t n k := by
          apply Nat.mul_lt_mul_of_pos_right _ hpos
          exact Nat.mul_lt_mul_of_pos_right hst hpos
      _ ≤ 2 ^ ℓ n * 2 ^ ℓ n * 2 ^ ℓ n := Nat.mul_le_mul this ht
  have h2 : 2 ^ ℓ n * 2 ^ ℓ n * 2 ^ ℓ n = 2 ^ (3 * ℓ n) := by ring
  have h3 : 2 ^ (3 * ℓ n) ≤ 2 ^ dsWW n := Nat.pow_le_pow_right (by norm_num) (by unfold dsWW; omega)
  omega

/-- The chirp loader: `8 (p + g) + size t_k + 80 ≤ W`. -/
theorem ds_chirp_W (n : ℕ) (k : Fin (d n)) :
    8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ dsWW n := by
  have h : Nat.size (t n k) ≤ ℓ n + 1 :=
    Nat.size_le.2 ((ds_t_le_pow n k).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  unfold dsWW; omega

theorem ds_le_two_pow_self (x : ℕ) : x + 2 ≤ 2 ^ x ∨ x < 2 := by
  induction x with
  | zero => right; omega
  | succ k ih =>
    rcases ih with h | h
    · left; rw [pow_succ]; omega
    · rcases Nat.lt_or_ge k 1 with h1 | h1
      · right; omega
      · left; have : k = 1 := by omega
        subst this; norm_num

/-- The table bound of the `Ã` and `B̃₀` loaders for a window `m ≤ p + 1`. -/
theorem ds_tab_W (hbig : Big n) {m : ℕ} (hm : m ≤ p n + 1) (i : Fin (d n)) :
    alpha n ^ 2 * ((s n i + t n i) * (m + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ dsWW n := by
  have hp13 := hbig.thirteen_le_p
  have hα : alpha n ^ 2 ≤ 2 ^ p n := hbig.alpha_sq_le_p.trans Nat.lt_two_pow_self.le
  have hst : s n i + t n i ≤ 2 ^ (ℓ n + 1) := by
    have := hbig.good.lt i
    have := ds_t_le_pow n i
    rw [pow_succ]; omega
  have hm1 : m + 1 ≤ 2 ^ p n := by
    rcases ds_le_two_pow_self (p n) with h | h <;> omega
  have hsm : (s n i + t n i) * (m + 1) ≤ 2 ^ (ℓ n + 1 + p n) := by
    rw [pow_add]; exact Nat.mul_le_mul hst hm1
  have hsq : ((s n i + t n i) * (m + 1)) ^ 2 ≤ 2 ^ (2 * (ℓ n + 1 + p n)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left hsm 2
  have h1 : alpha n ^ 2 * ((s n i + t n i) * (m + 1)) ^ 2 * 2 ^ (13 * p n + 8) ≤
      2 ^ p n * 2 ^ (2 * (ℓ n + 1 + p n)) * 2 ^ (13 * p n + 8) :=
    Nat.mul_le_mul (Nat.mul_le_mul hα hsq) le_rfl
  have h2 : 2 ^ p n * 2 ^ (2 * (ℓ n + 1 + p n)) * 2 ^ (13 * p n + 8) =
      2 ^ (16 * p n + 2 * ℓ n + 10) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have h3 : 2 ^ (16 * p n + 2 * ℓ n + 10) < 2 ^ dsWW n :=
    Nat.pow_lt_pow_right (by norm_num) (by unfold dsWW; omega)
  omega

theorem ds_windowA_le (hbig : Big n) : Pipeline.windowA (p n) (alpha n) ≤ p n + 1 := by
  unfold Pipeline.windowA
  have h1 : p n * alpha n ^ 2 ≤ p n ^ 2 :=
    calc p n * alpha n ^ 2 ≤ p n * p n := Nat.mul_le_mul_left _ hbig.alpha_sq_le_p
      _ = p n ^ 2 := (sq _).symm
  have h2 := Nat.sqrt_le_sqrt h1
  rw [Nat.sqrt_eq'] at h2
  omega

/-- The `Ã` loader: the table entries fit `W` bits. -/
theorem ds_A_W (hbig : Big n) (i : Fin (d n)) :
    alpha n ^ 2 * ((s n i + t n i) * (Pipeline.windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ dsWW n :=
  ds_tab_W hbig (ds_windowA_le hbig) i

/-- The `B̃₀` loader: the table entries fit `W` bits. -/
theorem ds_B_W (hbig : Big n) (i : Fin (d n)) :
    alpha n ^ 2 * ((s n i + t n i) * (FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ dsWW n := by
  have := FastB0.fastWindow_le_third (two_le_alpha hbig.1) hbig.thirteen_le_p
  exact ds_tab_W hbig (by omega) i

/-- The banded `B̃₀` loader: the folded-row tables at precision `5p` and window `8m` fit `W`
bits. -/
theorem ds_B_W65 (hbig : Big n) (i : Fin (d n)) :
    alpha n ^ 2 * ((s n i + t n i) * (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (65 * p n + 8) < 2 ^ dsWW n := by
  have hp13 := hbig.thirteen_le_p
  have hm3 := FastB0.fastWindow_le_third (two_le_alpha hbig.1) hp13
  have hα : alpha n ^ 2 ≤ 2 ^ p n := hbig.alpha_sq_le_p.trans Nat.lt_two_pow_self.le
  have hst : s n i + t n i ≤ 2 ^ (ℓ n + 1) := by
    have := hbig.good.lt i
    have := ds_t_le_pow n i
    rw [pow_succ]; omega
  have hm1 : 8 * FastB0.fastWindow (p n) (alpha n) + 1 ≤ 2 ^ p n := by
    have : 3 * p n ≤ 2 ^ p n := by
      have := Nat.lt_two_pow_self (n := p n - 2)
      have e : 2 ^ p n = 4 * 2 ^ (p n - 2) := by
        rw [show p n = 2 + (p n - 2) by omega, pow_add]; norm_num
      omega
    omega
  have hsm : (s n i + t n i) * (8 * FastB0.fastWindow (p n) (alpha n) + 1) ≤
      2 ^ (ℓ n + 1 + p n) := by
    rw [pow_add]; exact Nat.mul_le_mul hst hm1
  have hsq : ((s n i + t n i) * (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 ≤
      2 ^ (2 * (ℓ n + 1 + p n)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left hsm 2
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul hα hsq) (le_refl (2 ^ (65 * p n + 8)))
  have h2 : 2 ^ p n * 2 ^ (2 * (ℓ n + 1 + p n)) * 2 ^ (65 * p n + 8) =
      2 ^ (68 * p n + 2 * ℓ n + 10) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have hℓ : ℓ n ≤ p n := by have := pm_ℓ_le hbig.1; have := hbig.sixteen_le_b; unfold p; omega
  have h3 : 2 ^ (68 * p n + 2 * ℓ n + 10) < 2 ^ dsWW n :=
    Nat.pow_lt_pow_right (by norm_num) (by unfold dsWW; omega)
  omega

end Widths

/-! ### The layout stage -/

section Layout

open IntegerMultBounds.MathlibTM2.Mult.Rounds

variable {n : ℕ}

theorem ds_length_cvAx (n : ℕ) : (List.ofFn (ConvSt.cvAx (t n))).length = d n - 1 := by simp

theorem ds_ax_cvAx {i : ℕ} (hi : i < d n - 1) :
    ax (List.ofFn (ConvSt.cvAx (t n))) i = dsL n i := by
  unfold ax
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  exact ds_log_t n _

/-- `LayHyp` of the synthetic transform: axes of `ℓ - 1` or `ℓ` bits, `1 ≤ K ≤ ℓ - 1`. -/
theorem ds_layHyp (hbig : Big n) : LayHyp (List.ofFn (ConvSt.cvAx (t n))) (ℓ n) (K n) := by
  refine ⟨fun e he => ?_, one_le_iroot cExp_ne hbig.one_le_d, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    show Nat.log 2 _ = _ ∨ Nat.log 2 _ = _
    rw [ds_log_t]; unfold dsL; split_ifs <;> simp
  · have := hbig.K_succ_le_ℓ; omega

theorem ds_testBit_E (n i : ℕ) :
    (dsE n).testBit i = decide (numHalf n ≤ i ∧ i < d n - 1) := by
  by_cases hh : numHalf n ≤ d n - 1
  · have e : dsE n = 2 ^ numHalf n * (2 ^ (d n - 1 - numHalf n) - 1) := by
      unfold dsE
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hh]
    rw [e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
    by_cases h1 : numHalf n ≤ i
    · simp [h1]; omega
    · simp [h1]
  · have e : dsE n = 0 := by
      unfold dsE; apply Nat.sub_eq_zero_of_le
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [e, Nat.zero_testBit]
    simp; omega

theorem ds_E_bit (n i : ℕ) :
    dsE n / 2 ^ i % 2 = if numHalf n ≤ i ∧ i < d n - 1 then 1 else 0 := by
  have h := ds_testBit_E n i
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  have h2 := Nat.mod_lt (dsE n / 2 ^ i) (show 0 < 2 by norm_num)
  split_ifs with hc
  · simpa [hc] using h
  · have : ¬ (dsE n / 2 ^ i % 2 = 1) := by simpa [hc] using h
    omega

/-- The long-axis word: bit `i` of `E` is set iff axis `i` has `ℓ` bits. -/
theorem ds_lay_E (hn : 2 ≤ n) :
    ∀ i < (List.ofFn (ConvSt.cvAx (t n))).length,
      ax (List.ofFn (ConvSt.cvAx (t n))) i = ℓ n - 1 + dsE n / 2 ^ i % 2 := by
  intro i hi
  rw [ds_length_cvAx] at hi
  rw [ds_ax_cvAx hi, ds_E_bit]
  have := ds_one_le_ℓ hn
  unfold dsL
  split_ifs <;> omega

theorem dsE_lt (n : ℕ) : dsE n < 2 ^ (d n - 1) := by
  unfold dsE
  have := Nat.two_pow_pos (numHalf n)
  have := Nat.two_pow_pos (d n - 1)
  omega

/-- The word sizes of the layout stage at `W_L = dsWL n w`, `B = r w`, `w ≥ 1`. -/
theorem ds_lay_widths (hn : 2 ≤ n) {w : ℕ} (hw : 1 ≤ w) :
    dsE n < 2 ^ dsWL n w ∧
      ((List.ofFn (ConvSt.cvAx (t n))).sum + 1) ^ (List.ofFn (ConvSt.cvAx (t n))).sum <
        2 ^ dsWL n w ∧
      (List.ofFn (ConvSt.cvAx (t n))).sum + r n * w + 4 ≤ dsWL n w ∧ ℓ n < 2 ^ dsWL n w ∧
      1 ≤ r n * w := by
  rw [ds_sum_cvAx hn]
  set N := logT n - ℓ n
  have hr := ds_two_le_r hn
  have hrw : r n ≤ r n * w := Nat.le_mul_of_pos_right _ hw
  have hWL : r n * w ≤ dsWL n w := by unfold dsWL; omega
  refine ⟨?_, ?_, by unfold dsWL; nlinarith, ?_, by nlinarith⟩
  · refine (dsE_lt n).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
    have := ds_d_le_r hn; omega
  · have h1 : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
    calc (N + 1) ^ N ≤ (2 ^ N) ^ N := Nat.pow_le_pow_left h1 N
      _ = 2 ^ (N * N) := by rw [← pow_mul]
      _ < 2 ^ dsWL n w := Nat.pow_lt_pow_right (by norm_num) (by unfold dsWL; nlinarith)
  · have h1 : ℓ n < r n := Nat.lt_two_pow_self
    exact (h1.trans_le (hrw.trans hWL)).trans Nat.lt_two_pow_self

end Layout

/-! ### The distribution machine at the pipeline widths -/

section Dist

variable {n : ℕ}

theorem ds_dsW_le (hn : 2 ≤ n) : dsW n ≤ 63 * b n + 9 := by
  have := pm_g_le n
  have := pm_logT_le hn
  unfold dsW p; omega

theorem ds_dsWW_le (hn : 2 ≤ n) : dsWW n ≤ 500 * (b n + 1) := by
  have := pm_g_le n
  have := pm_ℓ_le hn
  have := ds_dsW_le hn
  unfold dsWW p; omega

/-- Width comparison independent of the dimension implementation. -/
theorem parameter_width_le_core {b L r w a : ℕ}
    (hb : 1 ≤ b) (hL : L ≤ b + 1) (hw : 6 * b + 7 ≤ w)
    (hr : 2 ≤ r) (hsmall : b ≤ 2 → 4 ≤ r) :
    4 * L + 32 ≤ r * w + (a ^ 2 + a + 4) := by
  by_cases h : b ≤ 2
  · have h4 := hsmall h
    have := Nat.mul_le_mul_right w h4
    nlinarith
  · have := Nat.mul_le_mul_right w hr
    nlinarith

/-- The candidate dimension is one at the smallest precisions. -/
theorem parameter_width_small_r {n : ℕ} (hn : 2≤n) (hb : b n≤2) : 4≤r n := by
  have hd : d n=1 := by
    have hcap := d_seventh_le n
    change d n^7≤b n at hcap
    have hd1 := one_le_d hn
    by_contra h
    have h2 : 2≤d n := by omega
    have hp := Nat.pow_le_pow_left h2 7
    norm_num at hp
    omega
  have hn4 : n≤4 := (le_two_pow_b n).trans (Nat.pow_le_pow_right (by decide) hb)
  rw [r, ℓ, hd]
  interval_cases n <;> decide

/-- The hypotheses of `dsIoAll_runs` at `w = dsW n`, `Wt = dsWW n`. -/
theorem ds_widths_dist (hn : 2 ≤ n) :
    dsWW n < 2 ^ pmW n ∧ 4 * dsW n + 2 < 2 ^ pmW n ∧ pmW n ≤ dsWL n (dsW n) := by
  have h1 := ds_dsWW_le hn
  have h2 := ds_dsW_le hn
  refine ⟨ds_small n (by omega), ds_small n (by omega), ?_⟩
  have hw : 6 * b n + 7 ≤ dsW n := by
    have : 4 ≤ Chirp.chirpGuard (d n) := by unfold Chirp.chirpGuard; omega
    unfold dsW p; omega
  exact parameter_width_le_core (one_le_b hn) pm_size_le hw (ds_two_le_r hn)
    (parameter_width_small_r hn)

end Dist

end IntegerMultBounds.MathlibTM2.Fast.TableVM
