module

public import IntegerMultBounds.MathlibTM2.Cost.Total
import IntegerMultBounds.MathlibTM2.Cost.CompactLogGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CRTSwap
public import IntegerMultBounds.MathlibTM2.Fast.CMul
import IntegerMultBounds.MathlibTM2.Fast.ParamMachine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.MathlibTM2.Node.SlotXor

/-!
# Cost matching: shared bounds

The stage machines of the fast multiplier have step bounds in the host's stack count `Tm` (the
number of stacks of the final machine), the coefficient width `w` and the parameters of
`Mult/Sizes.lean`. This file collects the comparisons that every stage matching
(`Cost/Match*.lean`) uses against the terms of `Cost/Total.totBound`.

* `mt_poly_r_le_T`: a polynomial in `B = b n` times `r` is eventually below `T`: the tables and
  writers of the stages (`O(r · poly(B))` steps) cost `o(T)`.
* `mt_mLogLog_le`, `mt_cmul_le`, `mt_rmul_le`: one Schönhage–Strassen product at width
  `w ≤ cw · p` costs at most a constant (`mtCM cw`) times `M(p) = p^{1+δ}` (`totMp`), from
  `compact_mLogLog_le`.
* `mt_swapN_le`, `mt_swap_le`: the vendored interchange bound `crtSwapCostN V h w` is at most
  `swapConst V max(1, h, w)^τ + 1`; `mt_rpow_tau_le`: `max(1, h, w)^τ ≤ L^τ` for `h, w ≤ L`.
* `mt_length_sxBits_le`: a canonical binary header of `x` has at most `x` bits.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds
  IntegerMultBounds.Machine

/-! ### Polynomials in `b` against `T / r` -/

/-- `T = 2^(logT - ℓ) · r` with `b ≤ 4 (logT - ℓ)`. -/
theorem mt_T_split {n : ℕ} (h : Big n) :
    T n = 2 ^ (logT n - ℓ n) * r n ∧ b n ≤ 4 * (logT n - ℓ n) := by
  have hd : 16 ≤ d n := by have := h.2; omega
  have h1 := dℓ_lt h.one_le_d
  have h2 := h.logT_bounds
  have hdb : d n ≤ b n := d_le_b n
  have h16 : 16 * ℓ n ≤ d n * ℓ n := Nat.mul_le_mul_right _ hd
  have hl : ℓ n ≤ logT n := by omega
  refine ⟨?_, by omega⟩
  unfold T r
  rw [← pow_add, Nat.sub_add_cancel hl]

/-- **A polynomial in `b` times `r` is eventually below `T`.** -/
theorem mt_poly_r_le_T (A k : ℕ) : ∀ᶠ n in atTop, A * b n ^ k * r n ≤ T n := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (eventually_mul_pow_le_two_pow (A * 4 ^ k) k)
  filter_upwards [eventually_big, tendsto_b.eventually_ge_atTop (4 * M₀)] with n h hb
  obtain ⟨hT, hm⟩ := mt_T_split h
  set m := logT n - ℓ n
  have hmM : M₀ ≤ m := by omega
  have h1 : A * b n ^ k ≤ 2 ^ m :=
    calc A * b n ^ k ≤ A * (4 * m) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm k)
      _ = A * 4 ^ k * m ^ k := by rw [mul_pow]; ring
      _ ≤ 2 ^ m := hM₀ m hmM
  rw [hT]
  exact Nat.mul_le_mul_right _ h1

/-! ### Basic sizes in the large regime -/

section Basic

variable {n : ℕ}

theorem mt_p_pos (h : Big n) : (0 : ℝ) < p n := tot_p_pos h

theorem mt_one_le_p (h : Big n) : (1 : ℝ) ≤ p n := by
  have := h.thirteen_le_p; exact_mod_cast (show 1 ≤ p n by omega)

theorem mt_one_le_T (n : ℕ) : (1 : ℝ) ≤ T n := by
  have : 1 ≤ T n := Nat.one_le_two_pow
  exact_mod_cast this

theorem mt_one_le_r (n : ℕ) : (1 : ℝ) ≤ r n := by
  have : 1 ≤ r n := Nat.one_le_two_pow
  exact_mod_cast this

theorem mt_r_le_T (h : Big n) : r n ≤ T n := by
  rw [(mt_T_split h).1]
  exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

theorem mt_p_le_mp (h : Big n) : (p n : ℝ) ≤ totMp n := by
  rw [tot_mp_eq h]
  have : (1 : ℝ) ≤ (p n : ℝ) ^ totDelta :=
    Real.one_le_rpow (mt_one_le_p h) (by norm_num [totDelta])
  have := mt_p_pos h
  nlinarith

theorem mt_one_le_mp (h : Big n) : (1 : ℝ) ≤ totMp n :=
  (mt_one_le_p h).trans (mt_p_le_mp h)

theorem mt_mp_eq (n : ℕ) : totMp n = (p n : ℝ) ^ (129 / 128 : ℝ) := by
  rw [totMp, totDelta]; norm_num

theorem mt_Tp_nonneg (n : ℕ) : (0 : ℝ) ≤ (T n : ℝ) * p n :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem mt_Tmp_nonneg (n : ℕ) : (0 : ℝ) ≤ (T n : ℝ) * totMp n :=
  mul_nonneg (Nat.cast_nonneg _) (tot_mp_nonneg n)

/-- `T p ≤ T M(p)`. -/
theorem mt_Tp_le_Tmp (h : Big n) : (T n : ℝ) * p n ≤ T n * totMp n :=
  mul_le_mul_of_nonneg_left (mt_p_le_mp h) (Nat.cast_nonneg _)

/-! The parameters against `b`. -/

theorem mt_d_le_b (n : ℕ) : d n ≤ b n := d_le_b n

theorem mt_K_le_b (n : ℕ) : K n ≤ b n := (K_le_d n).trans (d_le_b n)

theorem mt_logT_le_b (h : Big n) : logT n ≤ b n := h.logT_bounds.2.le

theorem mt_ℓ_le_logT (h : Big n) : ℓ n ≤ logT n := by
  have hd : 16 ≤ d n := by have := h.2; omega
  have h1 := dℓ_lt h.one_le_d
  have h2 := h.logT_bounds
  have hdb : d n ≤ b n := d_le_b n
  have h16 : 16 * ℓ n ≤ d n * ℓ n := Nat.mul_le_mul_right _ hd
  omega

theorem mt_ℓ_le_b (h : Big n) : ℓ n ≤ b n := (mt_ℓ_le_logT h).trans (mt_logT_le_b h)

theorem mt_ℓ_le_p (h : Big n) : ℓ n ≤ p n := by have := mt_ℓ_le_b h; unfold p; omega

theorem mt_alpha_le_p (h : Big n) : alpha n ≤ p n := by
  have h1 := h.alpha_sq_le_p
  have : alpha n ≤ alpha n ^ 2 := by
    rcases Nat.eq_zero_or_pos (alpha n) with h0 | h0
    · rw [h0]; simp
    · nlinarith
  omega

/-! The axis lengths. -/

theorem mt_t_le_r (n : ℕ) (i : Fin (d n)) : t n i ≤ r n := by
  rw [t_eq]; split_ifs <;> omega

theorem mt_s_lt_t (h : Big n) (i : Fin (d n)) : s n i < t n i := h.good.lt i

theorem mt_prod_t (h : Big n) : ∏ i, t n i = T n := prod_t h.one_le_d

theorem mt_t_pos (n : ℕ) (i : Fin (d n)) : 0 < t n i := by
  rw [IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log n i]; exact Nat.two_pow_pos _

theorem mt_s_pos (h : Big n) (i : Fin (d n)) : 0 < s n i := (h.good.odd i).pos

/-! The terms. -/

theorem mt_crt_eq (n : ℕ) :
    totCRT n = (T n : ℝ) * p n * (d n : ℝ) ^ 2 + (T n : ℝ) * p n * (d n : ℝ) ^ 2 *
      (ℓ n : ℝ) ^ Parameters.tau := by
  unfold totCRT; ring

theorem mt_resamp_nonneg (n : ℕ) : 0 ≤ totResamp n := by
  unfold totResamp
  have := tot_mp_nonneg n
  have := Real.rpow_nonneg (Nat.cast_nonneg (p n)) (1 / 2 : ℝ)
  positivity

/-- `d T M(p) ≤ totResamp`. -/
theorem mt_dTmp_le_resamp (h : Big n) : (d n : ℝ) * T n * totMp n ≤ totResamp n := by
  unfold totResamp
  have hα : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hp : (1 : ℝ) ≤ (p n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (mt_one_le_p h) (by norm_num)
  have h1 : (1 : ℝ) ≤ (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n := by nlinarith
  have h0 : 0 ≤ (d n : ℝ) * T n * totMp n := by
    have := tot_mp_nonneg n
    positivity
  calc (d n : ℝ) * T n * totMp n = (d n : ℝ) * T n * totMp n * 1 := by ring
    _ ≤ (d n : ℝ) * T n * totMp n * ((p n : ℝ) ^ (1 / 2 : ℝ) * alpha n) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

end Basic

/-! ### Small terms -/

/-- Every `x ≤ A b^k r` is eventually at most `T`, and so at most `T p`. -/
theorem mt_small_le (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ x : ℕ, x ≤ A * b n ^ k * r n → (x : ℝ) ≤ (T n : ℝ) * p n := by
  filter_upwards [mt_poly_r_le_T A k, eventually_big] with n h hb x hx
  have h1 : (x : ℝ) ≤ T n := by exact_mod_cast hx.trans h
  have h2 : (T n : ℝ) ≤ T n * p n := by
    have := mt_one_le_p hb
    have := mt_one_le_T n
    nlinarith
  linarith

/-! ### Schönhage–Strassen products -/

/-- `mLogLog w ≤ 262144 cw² M(p)` for `1 ≤ w ≤ cw p`. -/
theorem mt_mLogLog_le {n w cw : ℕ} (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (mLogLog w : ℝ) ≤ 262144 * (cw : ℝ) ^ 2 * totMp n := by
  have h1 := compact_mLogLog_le hw
  have hcw : 1 ≤ cw := by
    rcases Nat.eq_zero_or_pos cw with rfl | hc
    · simp at hwc; omega
    · exact hc
  have hcw' : (1 : ℝ) ≤ cw := by exact_mod_cast hcw
  have hp := mt_p_pos h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have h2 : (w : ℝ) ^ (129 / 128 : ℝ) ≤ ((cw : ℝ) * p n) ^ (129 / 128 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hw' (by norm_num)
  have h3 : ((cw : ℝ) * p n) ^ (129 / 128 : ℝ) = (cw : ℝ) ^ (129 / 128 : ℝ) * (p n : ℝ) ^ (129 / 128 : ℝ) :=
    Real.mul_rpow (Nat.cast_nonneg _) hp.le
  have h4 : (cw : ℝ) ^ (129 / 128 : ℝ) ≤ (cw : ℝ) ^ 2 := by
    rw [show ((cw : ℝ) ^ 2) = (cw : ℝ) ^ (2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le hcw' (by norm_num)
  have h5 : (0 : ℝ) ≤ (p n : ℝ) ^ (129 / 128 : ℝ) := Real.rpow_nonneg hp.le _
  have e : (mLogLog w : ℝ) =
      ((w * (Nat.log 2 w + 1) * (Nat.log 2 (Nat.log 2 w) + 1) : ℕ) : ℝ) := rfl
  rw [e, mt_mp_eq]
  calc _ ≤ 262144 * (w : ℝ) ^ (129 / 128 : ℝ) := h1
    _ ≤ 262144 * ((cw : ℝ) ^ 2 * (p n : ℝ) ^ (129 / 128 : ℝ)) := by
        rw [h3] at h2
        have := mul_le_mul_of_nonneg_right h4 h5
        nlinarith
    _ = 262144 * (cw : ℝ) ^ 2 * (p n : ℝ) ^ (129 / 128 : ℝ) := by ring

/-- The constant of one complex fixed-point product at width `w ≤ cw p`, against
`M(p)`. -/
noncomputable def mtCM (cw : ℕ) : ℝ :=
  1048576 * ssMulConst * (cw : ℝ) ^ 2 + 256 * cw + 128

theorem mt_CM_nonneg (cw : ℕ) : 0 ≤ mtCM cw := by unfold mtCM; positivity

/-- `cmulCost w ≤ mtCM cw · M(p)`. -/
theorem mt_cmul_le {n w cw : ℕ} (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (cmulCost w : ℝ) ≤ mtCM cw * totMp n := by
  have h1 := mt_mLogLog_le h hw hwc
  have hm1 := mt_one_le_mp h
  have hpm := mt_p_le_mp h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwm : (w : ℝ) ≤ cw * totMp n := hw'.trans (mul_le_mul_of_nonneg_left hpm hcw)
  have hS : (0 : ℝ) ≤ ssMulConst := by positivity
  unfold cmulCost mtCM
  push_cast
  have h2 := mul_le_mul_of_nonneg_left h1 hS
  have hmp0 : 0 ≤ totMp n := tot_mp_nonneg n
  have hcw2 : (0 : ℝ) ≤ (cw : ℝ) ^ 2 * totMp n := by positivity
  nlinarith

/-- `rmulCost w ≤ mtCM cw · M(p)`. -/
theorem mt_rmul_le {n w cw : ℕ} (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (rmulCost w : ℝ) ≤ mtCM cw * totMp n := by
  have h1 := mt_mLogLog_le h hw hwc
  have hm1 := mt_one_le_mp h
  have hpm := mt_p_le_mp h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwm : (w : ℝ) ≤ cw * totMp n := hw'.trans (mul_le_mul_of_nonneg_left hpm hcw)
  have hS : (0 : ℝ) ≤ ssMulConst := by positivity
  unfold rmulCost mtCM
  push_cast
  have h2 := mul_le_mul_of_nonneg_left h1 hS
  have hmp0 : 0 ≤ totMp n := tot_mp_nonneg n
  have hcw2 : (0 : ℝ) ≤ (cw : ℝ) ^ 2 * totMp n := by positivity
  nlinarith

/-! ### The vendored interchange -/

theorem mt_swapConst_nonneg : 0 ≤ swapConst := swapConst_pos.le

/-- `crtSwapCostN V h w ≤ swapConst V max(1, h, w)^τ + 1`. -/
theorem mt_swapN_le (V h w : ℕ) :
    (crtSwapCostN V h w : ℝ) ≤
      swapConst * V * ((max 1 (max h w) : ℕ) : ℝ) ^ Parameters.tau + 1 := by
  unfold crtSwapCostN
  have : 0 ≤ swapConst * V * ((max 1 (max h w) : ℕ) : ℝ) ^ Parameters.tau := by
    have := mt_swapConst_nonneg
    positivity
  exact (Nat.ceil_lt_add_one this).le

/-- `max(1, h, w)^τ ≤ L^τ` for `h, w ≤ L`, `1 ≤ L`. -/
theorem mt_rpow_tau_le {h w L : ℕ} (hh : h ≤ L) (hw : w ≤ L) (hL : 1 ≤ L) :
    ((max 1 (max h w) : ℕ) : ℝ) ^ Parameters.tau ≤ (L : ℝ) ^ Parameters.tau := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ tot_tau_nonneg
  exact_mod_cast max_le hL (max_le hh hw)

/-- The vendored interchange of `[P] × [2^h] × [G] × [2^w] × [E]` with `|h - w| ≤ 1`, canonical
headers of its dimensions and `h, w ≤ L`: at most `swapConst V L^τ + 1` steps. -/
theorem mt_swap_le {P G E h w L : ℕ} (hs : Fin 5 → List Bool) (hP : 0 < P) (hG : 0 < G)
    (hE : 0 < E) (hhw : h ≤ w + 1) (hwh : w ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G E h w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hh : h ≤ L) (hw : w ≤ L) (hL : 1 ≤ L) :
    (BinaryInterchangeRun.cost P G E h w hs : ℝ) ≤
      swapConst * (P * 2 ^ h * G * 2 ^ w * E : ℕ) * (L : ℝ) ^ Parameters.tau + 1 := by
  have h1 : (BinaryInterchangeRun.cost P G E h w hs : ℝ) ≤
      (crtSwapCostN (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ w) E) h w : ℝ) := by
    exact_mod_cast crt_cost_le P G E h w hs hP hG hE hhw hwh hv hc
  have h2 := mt_swapN_le (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ w) E) h w
  have h3 := mt_rpow_tau_le hh hw hL
  have hV : (0 : ℝ) ≤ swapConst * (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ w) E : ℕ) :=
    mul_nonneg mt_swapConst_nonneg (Nat.cast_nonneg _)
  have h4 := mul_le_mul_of_nonneg_left h3 hV
  rw [BinaryAdjacentWidthInterchange.volume] at h1 h2 h4
  linarith

/-! ### Headers -/

/-- A canonical counter has at most as many bits as its value. -/
theorem mt_length_le_value {bs : List Bool} (hc : GrowingCounterData.Canonical bs) :
    bs.length ≤ Counter.value bs := by
  rcases hc with rfl | hc
  · simp
  · have h1 := IntegerMultBounds.MathlibTM2.Fast.TableVM.pm_value_ge bs hc
    have h2 : bs.length - 1 < 2 ^ (bs.length - 1) := Nat.lt_two_pow_self
    have h3 : bs ≠ [] := by rintro rfl; simp at hc
    have : 0 < bs.length := List.length_pos_of_ne_nil h3
    omega

/-- The canonical binary digits of `x` have at most `x` bits. -/
theorem mt_length_sxBits_le (x : ℕ) : (sxBits x).length ≤ x := by
  rw [IntegerMultBounds.MathlibTM2.Fast.TableVM.pm_length_sxBits]
  exact Nat.size_le.2 Nat.lt_two_pow_self

end IntegerMultBounds.MathlibTM2.Cost
