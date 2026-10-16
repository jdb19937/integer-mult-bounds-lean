module

public import IntegerMultBounds.MathlibTM2.Cost.DirectScale
public import IntegerMultBounds.MathlibTM2.Fast.PrepB

/-!
# Cost matching: the shared pieces of the `B̃₀` stage

The generic estimates of the `B̃₀` driver `rsbAllCostG` that `Cost/MatchBandB.lean` and
`Cost/MatchBandLoad.lean` use for the banded `B̃₀`: the bank and header lengths of an
interchange (`mt_rsb_bank_sum_le`, `mt_rsb_hs_le`), the interchanges of a non-last axis with the
last one (`mt_rsb_swap_le`), the unit `mtRsbV = T p (ℓ^τ + 1)` of the linear terms and its
constant `mtRsbCL` (`mt_rsb_V_facts`), the window and `α` facts (`mt_rsb_window_le`,
`mt_rsb_alpha_facts`), `mt_rsb_resamp_eq`, and the loader parameter size `mtRsbQ`.
The Neumann stage cost (`mt_rsb_stage_le_linear`) was removed with the Neumann `B̃₀`; restore
from `1cb2723b`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! ### The loader -/

/-- The small parameters of a loader record. -/
def mtRsbQ (D : PreAxB) (w : ℕ) : ℕ := D.m + D.α + D.p + D.W + w + D.L + D.Ld + 1

/-- A bank register holds at most one header and a separator. -/
theorem mt_rsb_bank_length_le {t₀ A : ℕ} (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool)
    (j : Fin (swapT t₀)) :
    (rsbBank (A := A) hd hs j).length ≤ 1 + ∑ k, (hs k).length := by
  unfold rsbBank
  split_ifs with h
  · simp only [List.length_cons, List.length_map]
    have := Finset.single_le_sum (f := fun k => (hs k).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Classical.choose h))
    omega
  · simp

/-- The bank of an interchange: at most `swapT t₀ (1 + Σ |hs k|)` symbols. -/
theorem mt_rsb_bank_sum_le {t₀ A : ℕ} (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) :
    ∑ j, (rsbBank (A := A) hd hs j).length ≤ swapT t₀ * (1 + ∑ k, (hs k).length) := by
  have := Finset.sum_le_card_nsmul Finset.univ (fun j => (rsbBank (A := A) hd hs j).length)
    (1 + ∑ k, (hs k).length) (fun j _ => mt_rsb_bank_length_le hd hs j)
  simpa using this

/-- The headers of an interchange of `[P] × [2^h] × [G] × [2^d] × [B]`. -/
theorem mt_rsb_hs_sum_le (P G B h e : ℕ) :
    ∑ k, (sxBits (BinaryInterchangeRun.values P G B h e k)).length ≤ 5 * (P + G + B + h + e) := by
  have : ∀ k, (sxBits (BinaryInterchangeRun.values P G B h e k)).length ≤ P + G + B + h + e := by
    intro k
    refine (mt_length_sxBits_le _).trans ?_
    fin_cases k <;> simp [BinaryInterchangeRun.values] <;> omega
  have := Finset.sum_le_card_nsmul Finset.univ
    (fun k => (sxBits (BinaryInterchangeRun.values P G B h e k)).length) (P + G + B + h + e)
    (fun k _ => this k)
  simpa using this

/-! ### The lines against `M(p)` -/

/-- `α² m ≤ (3/2) α √p` for the window `m = fastWindow p α`. -/
theorem mt_rsb_window_le {n : ℕ} (h : Big n) :
    (alpha n : ℝ) ^ 2 * (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      3 / 2 * ((alpha n : ℝ) * Real.sqrt (p n)) := by
  have hα2 : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hα0 : (0 : ℝ) < alpha n := by linarith
  have hsp : (alpha n : ℝ) ≤ Real.sqrt (p n) := by
    rw [Real.le_sqrt hα0.le (Nat.cast_nonneg _)]
    exact_mod_cast h.alpha_sq_le_p
  have hm : (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      Real.sqrt (p n) / (2 * alpha n) + 1 := by
    unfold Mult.FastB0.fastWindow
    push_cast
    have h1 : ((Nat.sqrt (p n) / (2 * alpha n) : ℕ) : ℝ) ≤
        ((Nat.sqrt (p n) : ℕ) : ℝ) / ((2 * alpha n : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : ((Nat.sqrt (p n) : ℕ) : ℝ) ≤ Real.sqrt (p n) := Real.nat_sqrt_le_real_sqrt
    have h3 : ((Nat.sqrt (p n) : ℕ) : ℝ) / ((2 * alpha n : ℕ) : ℝ) ≤
        Real.sqrt (p n) / (2 * alpha n) := by
      push_cast
      exact div_le_div_of_nonneg_right h2 (by positivity)
    linarith
  have e : (alpha n : ℝ) ^ 2 * (Real.sqrt (p n) / (2 * alpha n) + 1) =
      (alpha n : ℝ) * Real.sqrt (p n) / 2 + (alpha n : ℝ) ^ 2 := by
    field_simp
  have h4 : (alpha n : ℝ) ^ 2 ≤ (alpha n : ℝ) * Real.sqrt (p n) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hsp hα0.le
  calc (alpha n : ℝ) ^ 2 * (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      (alpha n : ℝ) ^ 2 * (Real.sqrt (p n) / (2 * alpha n) + 1) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ _ := by rw [e]; linarith

/-- `1 ≤ α √p` and `α² ≤ α √p`. -/
theorem mt_rsb_alpha_facts {n : ℕ} (h : Big n) :
    1 ≤ (alpha n : ℝ) * Real.sqrt (p n) ∧
      (alpha n : ℝ) ^ 2 ≤ (alpha n : ℝ) * Real.sqrt (p n) := by
  have hα2 : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hα0 : (0 : ℝ) < alpha n := by linarith
  have hsp : (alpha n : ℝ) ≤ Real.sqrt (p n) := by
    rw [Real.le_sqrt hα0.le (Nat.cast_nonneg _)]
    exact_mod_cast h.alpha_sq_le_p
  have hs1 : (1 : ℝ) ≤ Real.sqrt (p n) := Real.one_le_sqrt.2 (mt_one_le_p h)
  refine ⟨by nlinarith, ?_⟩
  rw [sq]; exact mul_le_mul_of_nonneg_left hsp hα0.le

/-! ### The axes of the pipeline -/

section Axes

variable {n : ℕ}

theorem mt_rsb_last (hd0 : 0 < d n) : rsbAx hd0 0 = ⟨d n - 1, by omega⟩ :=
  Fin.ext (by simp [rsbAx])

/-- Before, along, between and the last axis: the whole box. -/
theorem mt_rsb_prod_eq (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n) :
    rsbPre (t n) i * (t n i * (rsbMid (t n) i * t n (rsbAx hd0 0))) = T n := by
  have h1 := rsbPre_mul (t n) i
  rw [rsb_suf_last (t n) i hi, mt_prod_t h] at h1
  rw [mt_rsb_last hd0]
  exact h1

/-- `rsbPre t i ≤ T` and `rsbMid t i ≤ T`. -/
theorem mt_rsb_PG_le (h : Big n) (i : Fin (d n)) :
    rsbPre (t n) i ≤ T n ∧ rsbMid (t n) i ≤ T n := by
  have h1 := rsbPre_mul (t n) i
  rw [mt_prod_t h] at h1
  have hT : 0 < T n := Nat.two_pow_pos _
  have hP : 0 < rsbPre (t n) i := Nat.pos_of_ne_zero (fun e => by rw [e] at h1; omega)
  have hS : 0 < t n i * rsbSuf (t n) i := Nat.pos_of_ne_zero (fun e => by rw [e] at h1; omega)
  have hS' : 0 < rsbSuf (t n) i := Nat.pos_of_mul_pos_left hS
  have hti : 0 < t n i := mt_t_pos n i
  refine ⟨?_, ?_⟩
  · calc rsbPre (t n) i = rsbPre (t n) i * 1 := (mul_one _).symm
      _ ≤ rsbPre (t n) i * (t n i * rsbSuf (t n) i) := Nat.mul_le_mul_left _ hS
      _ = T n := h1
  · have hdvd : rsbMid (t n) i ∣ rsbSuf (t n) i :=
      (List.dropLast_sublist _).prod_dvd_prod
    have hMS := Nat.le_of_dvd hS' hdvd
    have hST : rsbSuf (t n) i ≤ T n := by
      calc rsbSuf (t n) i ≤ rsbPre (t n) i * (t n i * rsbSuf (t n) i) := by
            have : rsbSuf (t n) i ≤ t n i * rsbSuf (t n) i := Nat.le_mul_of_pos_left _ hti
            exact this.trans (Nat.le_mul_of_pos_left _ hP)
        _ = T n := h1
    omega

/-- The volume of the interchange of axis `i` with the last axis: `3 T w`. -/
theorem mt_rsb_vol (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n) (E : ℕ) :
    rsbPre (t n) i * 2 ^ Nat.log 2 (t n i) * rsbMid (t n) i *
        2 ^ Nat.log 2 (t n (rsbAx hd0 0)) * E = T n * E ∧
      rsbPre (t n) i * 2 ^ Nat.log 2 (t n (rsbAx hd0 0)) * rsbMid (t n) i *
        2 ^ Nat.log 2 (t n i) * E = T n * E := by
  rw [← IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log n i, ← IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log n (rsbAx hd0 0)]
  have := mt_rsb_prod_eq h hd0 i hi
  constructor
  · rw [← this]; ring
  · rw [← this]; ring

theorem mt_rsb_P_pos (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n) :
    0 < rsbPre (t n) i ∧ 0 < rsbMid (t n) i := by
  have h1 := mt_rsb_prod_eq h hd0 i hi
  have hT : 0 < T n := Nat.two_pow_pos _
  refine ⟨Nat.pos_of_ne_zero (fun e => by rw [e] at h1; omega),
    Nat.pos_of_ne_zero (fun e => by rw [e] at h1; simp at h1; omega)⟩

/-- The widths of the axes: `ℓ - 1` or `ℓ`, and `ℓ` for the last one. -/
theorem mt_rsb_logs (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) :
    (Nat.log 2 (t n i) = ℓ n - 1 ∨ Nat.log 2 (t n i) = ℓ n) ∧
      Nat.log 2 (t n (rsbAx hd0 0)) = ℓ n :=
  ⟨pre_log_t i, pre_log_last h hd0⟩

/-- **The interchanges of axis `i` with the last axis**, both directions: at most
`swapConst · 3 T w · ℓ^τ + 1` steps each. -/
theorem mt_rsb_swap_le (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n)
    {w : ℕ} (hw : 1 ≤ w) :
    (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w) (Nat.log 2 (t n i))
        (Nat.log 2 (t n (rsbAx hd0 0))) (preHsB n w hd0 i) : ℝ) ≤
        swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau + 1 ∧
      (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
        (Nat.log 2 (t n (rsbAx hd0 0))) (Nat.log 2 (t n i))
        (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) : ℝ) ≤
        swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau + 1 := by
  obtain ⟨hP, hG⟩ := mt_rsb_P_pos h hd0 i hi
  obtain ⟨hl, hlast⟩ := mt_rsb_logs h hd0 i
  have h2 := h.two_le_ℓ
  have hlt := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n i
  obtain ⟨v1, v2⟩ := mt_rsb_vol h hd0 i hi (3 * w)
  constructor
  · have := mt_swap_le (E := 3 * w) (h := Nat.log 2 (t n i)) (w := Nat.log 2 (t n (rsbAx hd0 0)))
      (L := ℓ n) (preHsB n w hd0 i) hP hG (by omega)
      (by rcases hl with e | e <;> omega) (by rcases hl with e | e <;> omega)
      (fun k => by simp only [preHsB]; exact value_sxBits _)
      (fun k => canonical_sxBits _) hlt (by omega) (by omega)
    rwa [v1] at this
  · have := mt_swap_le (E := 3 * w) (h := Nat.log 2 (t n (rsbAx hd0 0))) (w := Nat.log 2 (t n i))
      (L := ℓ n) (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) hP hG (by omega)
      (by rcases hl with e | e <;> omega) (by rcases hl with e | e <;> omega)
      (fun k => by simp only [preHsB]; rw [value_sxBits, ResampA.rsa_values_swap34])
      (fun k => canonical_sxBits _) (by omega) hlt (by omega)
    rwa [v2] at this

/-- The headers of axis `i`: at most `5 (2 T + 3 w + 2 ℓ)` bits, either order. -/
theorem mt_rsb_hs_le (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (w : ℕ) :
    ∑ k, (preHsB n w hd0 i k).length ≤ 5 * (2 * T n + 3 * w + 2 * ℓ n) ∧
      ∑ k, (preHsB n w hd0 i (Equiv.swap 3 4 k)).length ≤ 5 * (2 * T n + 3 * w + 2 * ℓ n) := by
  obtain ⟨hP, hG⟩ := mt_rsb_PG_le h i
  have hl1 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n i
  have hl2 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsbAx hd0 0)
  constructor
  · have := mt_rsb_hs_sum_le (rsbPre (t n) i) (rsbMid (t n) i) (3 * w) (Nat.log 2 (t n i))
      (Nat.log 2 (t n (rsbAx hd0 0)))
    simp only [preHsB]
    omega
  · have := mt_rsb_hs_sum_le (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
      (Nat.log 2 (t n (rsbAx hd0 0))) (Nat.log 2 (t n i))
    simp only [preHsB, ResampA.rsa_values_swap34]
    omega

end Axes


/-! ### One step of `B̃₀` along a non-last axis -/

/-- The constant of the linear part of one step: the two interchanges, the bank, the
headers. -/
noncomputable def mtRsbCL (Tm t₀ cw : ℕ) : ℝ :=
  6 * (Tm + 12 * swapT t₀ + 5 : ℕ) * swapConst * cw + 2 * (Tm + 12 * swapT t₀ + 5 : ℕ) +
    12 * swapT t₀ * (21 + 15 * cw) + 200 * cw + 4 * Tm + 12 * swapT t₀ + 300

theorem mt_rsb_CL_nonneg (Tm t₀ cw : ℕ) : 0 ≤ mtRsbCL Tm t₀ cw := by
  unfold mtRsbCL
  have := mt_swapConst_nonneg
  positivity

/-- The unit of the linear terms of one axis: `T p (ℓ^τ + 1)`. -/
noncomputable def mtRsbV (n : ℕ) : ℝ := (T n : ℝ) * p n * ((ℓ n : ℝ) ^ Parameters.tau + 1)

theorem mt_rsb_V_facts {n w cw : ℕ} (h : Big n) (hwc : w ≤ cw * p n) :
    1 ≤ mtRsbV n ∧ (T n : ℝ) ≤ mtRsbV n ∧ (p n : ℝ) ≤ mtRsbV n ∧ (ℓ n : ℝ) ≤ mtRsbV n ∧
      (T n : ℝ) * w ≤ cw * mtRsbV n ∧ (w : ℝ) ≤ cw * mtRsbV n ∧
      (T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau ≤ cw * mtRsbV n := by
  have hT1 := mt_one_le_T n
  have hp1 := mt_one_le_p h
  have hΛ : 0 ≤ (ℓ n : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hlp : (ℓ n : ℝ) ≤ p n := by exact_mod_cast mt_ℓ_le_p h
  have hTp : (T n : ℝ) ≤ T n * p n := le_mul_of_one_le_right (by linarith) hp1
  have hpT : (p n : ℝ) ≤ T n * p n := le_mul_of_one_le_left (by linarith) hT1
  have hV : (T n : ℝ) * p n ≤ mtRsbV n := by
    unfold mtRsbV
    have : (0 : ℝ) ≤ T n * p n := by positivity
    nlinarith
  have hTw : (T n : ℝ) * w ≤ cw * (T n * p n) := by
    have := mul_le_mul_of_nonneg_left hw' (show (0 : ℝ) ≤ T n by linarith)
    linarith
  refine ⟨by nlinarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · nlinarith
  · have : (w : ℝ) ≤ cw * (T n * p n) := by nlinarith
    nlinarith
  · have h1 : (T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau ≤
        cw * (T n * p n) * (ℓ n : ℝ) ^ Parameters.tau := mul_le_mul_of_nonneg_right hTw hΛ
    have h2 : cw * (T n * p n) * (ℓ n : ℝ) ^ Parameters.tau ≤ cw * mtRsbV n := by
      unfold mtRsbV
      have : (0 : ℝ) ≤ cw * (T n * p n) := by positivity
      nlinarith
    linarith

/-! ### All axes -/

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-! ### Against the terms of `totBound` -/

/-- `d T α √p M(p) = totResamp`. -/
theorem mt_rsb_resamp_eq (n : ℕ) :
    (d n : ℝ) * ((T n : ℝ) * ((alpha n : ℝ) * Real.sqrt (p n) * totMp n)) = totResamp n := by
  rw [totResamp, Real.sqrt_eq_rpow]; ring

end IntegerMultBounds.MathlibTM2.Cost
