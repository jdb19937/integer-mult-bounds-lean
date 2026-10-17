module

public import IntegerMultBounds.MathlibTM2.Fast.MainProg
public import IntegerMultBounds.MathlibTM2.Cost.DirectTotal
import IntegerMultBounds.MathlibTM2.Cost.MatchRound
import IntegerMultBounds.MathlibTM2.Cost.MatchChirp
public import IntegerMultBounds.MathlibTM2.Cost.MatchParam
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The time bound of the fast multiplier, given the bound of the source-transform runs

`mn_time_le_of_runs`: if the three source-transform runs `mnRuns D Y n` cost at most
`C_r (totDirectCRT + totResamp + totConv + T M(p) + T p)` for all large `n`, then
`mnTime D Y c n ≤ totDirectBound C n` for all large `n`, with a natural constant `C`.

The other stages are matched with `Cost/MatchStages`: the input and the unary length (`22 n`),
the parameter machine (`mt_pm_stage_le`, `n + B^k`), the distribution (its cost bound
`C n + C (B + 1)^k`), the two digit stages (`mt_digit_le`), the transfers and clears of boxes
(`T w ≤ c_w T p`), the pointwise product (`mt_ch_point_le`), the transfers of the coefficient
streams (`S w`, `S W_o ≤ c_w T p`), the rounding stage (`mt_rnd_stage_le`, operand width
`w + 2 size S ≤ (c_w + 3) p`, word size `2 B + 2 size S + 6 ≤ p`) and the output stage
(`mt_carry_le`). All of them are bounded by a constant times
`Z n = n + totDirectCRT + totResamp + totConv + T M(p) + S M(p) + T p + B^k`, and the cleanup
`2 (n + c · mnPreCost) + 2 mnT + 4` is linear in `mnPreCost` and `n`. `totDirectBound C n` is at least
`C · Z n` for `C ≥ k`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter

noncomputable section

attribute [local irreducible] mnT

/-- `size S ≤ b + 6`, from `S < T` and `T p < 48 n ≤ 48 · 2^b`. -/
theorem mn_size_S_le {n : ℕ} (h : Big n) : Nat.size (S n) ≤ b n + 6 := by
  rw [Nat.size_le]
  have h1 := h.S_lt_T
  have h2 := (volume_bounds h.1).2
  have hp : 1 ≤ p n := by have := h.sixteen_le_b; unfold p; omega
  have h3 := le_two_pow_b n
  have h4 : T n ≤ T n * p n := Nat.le_mul_of_pos_right _ hp
  have h5 : 2 ^ (b n + 6) = 2 ^ b n * 64 := by rw [pow_add]; norm_num
  rw [h5]
  omega

/-- The word size of the coefficients is at most `p`. -/
theorem mn_Wo_le_p {n : ℕ} (h : Big n) : mnWo n ≤ 1 * p n := by
  have := mn_size_S_le h
  have := h.sixteen_le_b
  unfold mnWo p
  omega

/-- The operand width of the rounding products is at most `(c_w + 3) p`. -/
theorem mn_Mw_le {n w cw : ℕ} (h : Big n) (hw : w ≤ cw * p n) :
    mnMw n w ≤ (cw + 3) * p n := by
  have := mn_size_S_le h
  have := h.sixteen_le_b
  unfold mnMw
  have e : (cw + 3) * p n = cw * p n + 3 * p n := by ring
  rw [e]
  unfold p at hw ⊢
  omega

/-- `(B + 1)^j ≤ 2^j B^k` for `1 ≤ B`, `j ≤ k`. -/
theorem mn_succ_pow_le {B j k : ℕ} (hB : 1 ≤ B) (hjk : j ≤ k) :
    (B + 1) ^ j ≤ 2 ^ j * B ^ k := by
  calc (B + 1) ^ j ≤ (2 * B) ^ j := Nat.pow_le_pow_left (by omega) j
    _ = 2 ^ j * B ^ j := by rw [mul_pow]
    _ ≤ 2 ^ j * B ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB hjk)

/-- `mnUs` has six entries. -/
theorem mn_length_us : mnUs.length = 6 := rfl

/-- The unary copies of `mnUs` are of values eventually at most `T`. -/
theorem mn_us_small : ∀ x ∈ mnUs, x.1 ∈ mtPmSmall := by
  intro x hx
  simp only [mnUs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mtPmSmall]

/-- **The time bound**, given the bound of the three source-transform runs. -/
theorem mn_time_le_of_runs {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (Y : MnSyn K Lb w σ) (c : ℕ) {Cr : ℝ}
    (hR : ∀ᶠ n in atTop, (mnRuns D Y n : ℝ) ≤
      Cr * (IntegerMultBounds.MathlibTM2.Cost.totDirectCRT n + IntegerMultBounds.MathlibTM2.Cost.totResamp n + IntegerMultBounds.MathlibTM2.Cost.totConv n +
        (T n : ℝ) * IntegerMultBounds.MathlibTM2.Cost.totMp n + (T n : ℝ) * p n)) :
    ∃ C : ℕ, ∀ᶠ n in atTop, (mnTime D Y c n : ℝ) ≤ IntegerMultBounds.MathlibTM2.Cost.totDirectBound C n := by
  obtain ⟨cw, cW, hrat⟩ := D.ratio
  obtain ⟨Cd, kd, hcost⟩ := D.costBound
  set k := kd + 4 with hk
  set Pm : ℝ := 2^36 + 2^12 * 6 with hPm
  set CP : ℝ := mtCM mnT cw + 6 * cw + 10 with hCP
  set CR : ℝ := mtRndC mnT (cw + 3) cw 1 with hCR
  set Cr' : ℝ := max Cr 0 with hCr'
  -- the coefficients of `n`, `B^k`, `totDirectCRT`, `totResamp`, `totConv`, `T M(p)`, `S M(p)`, `T p`
  set A1 : ℝ := 22 + Pm + Cd + 2 * 3072 * cw + 20 + 8 + 2304 * (1 + 1) with hA1
  set A2 : ℝ := Pm + Cd * 2 ^ kd with hA2
  set A3 : ℝ := Cr' with hA3
  set A6 : ℝ := Cr' + CP with hA6
  set A8 : ℝ := Cr' + 20 * cw + 4 * cw + 4 with hA8
  set M : ℝ := A1 + A2 + A3 + A3 + A3 + A6 + CR + A8 with hM
  set C : ℕ := max k ⌈(1 + 2 * (c : ℝ)) * M + 2 * (mnT : ℝ) + 6⌉₊ with hC
  refine ⟨C, ?_⟩
  filter_upwards [eventually_big, hrat, hcost, D.widths, hR,
    mt_pm_stage_le k (by omega) mnUs mn_us_small, mt_digit_le cw, mt_ch_point_le mnT cw,
    mt_rnd_stage_le mnT (cw + 3) cw 1, mt_carry_le 1] with n h hr hc hwd hRn hpm hdig hpt hrnd hcar
  obtain ⟨hwc, -⟩ := hr
  obtain ⟨hpw0, -⟩ := hwd
  have hpw : p n ≤ w n := by omega
  have hb1 : 1 ≤ b n := by have := h.sixteen_le_b; omega
  have hn2 : 2 ≤ n := h.1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hST : S n ≤ T n := h.S_lt_T.le
  have hprod := mt_prod_t h
  have hWo := mn_Wo_le_p h
  have hMw := mn_Mw_le h hwc
  -- nonnegative atoms
  have hcrt0 := mt_directCRT_nonneg n
  have hres0 := mt_resamp_nonneg n
  have hconv0 := tot_conv_nonneg h
  have hTmp0 := mt_Tmp_nonneg n
  have hSmp0 : (0 : ℝ) ≤ (S n : ℝ) * totMp n := mul_nonneg (Nat.cast_nonneg _) (tot_mp_nonneg n)
  have hTp0 := mt_Tp_nonneg n
  have hbk0 : (0 : ℝ) ≤ (b n : ℝ) ^ k := by positivity
  have hCd0 : (0 : ℝ) ≤ Cd := Nat.cast_nonneg _
  have hcw0 : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hCP0 : 0 ≤ CP := by have := mt_CM_nonneg mnT cw; rw [hCP]; positivity
  have hCR0 : 0 ≤ CR := mt_rnd_C_nonneg _ _ _ _
  have hCr'0 : 0 ≤ Cr' := le_max_right _ _
  -- the stages
  have t1 : (((4 * n + 6) + (4 * n + 8) : ℕ) : ℝ) ≤ 22 * n := by push_cast; linarith
  have t2 : (pmCost n mnUs : ℝ) ≤ Pm * n + Pm * (b n : ℝ) ^ k := by
    rw [mn_length_us] at hpm
    have e : ((6 : ℕ) : ℝ) = 6 := by norm_num
    rw [e] at hpm
    linarith
  have t3 : (D.cost n : ℝ) ≤ Cd * n + Cd * 2 ^ kd * (b n : ℝ) ^ k := by
    have h1 := mn_succ_pow_le hb1 (show kd ≤ k by omega)
    have h2 : D.cost n ≤ Cd * n + Cd * (2 ^ kd * b n ^ k) :=
      hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _)
    have h3 : (D.cost n : ℝ) ≤ ((Cd * n + Cd * (2 ^ kd * b n ^ k) : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h3
    linarith
  have t4 : ((2 * digitCost (b n) (p n) (w n) (S n) : ℕ) : ℝ) ≤ 2 * 3072 * cw * n := by
    have := hdig (w n) hpw hwc
    push_cast
    linarith
  have t5 : (mnRuns D Y n : ℝ) ≤ Cr' * (totDirectCRT n + totResamp n + totConv n +
      (T n : ℝ) * totMp n + (T n : ℝ) * p n) :=
    hRn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  -- `T w ≤ c_w T p`
  have hTw : ((T n * w n : ℕ) : ℝ) ≤ cw * ((T n : ℝ) * p n) := by
    have : T n * w n ≤ cw * (T n * p n) := by
      calc T n * w n ≤ T n * (cw * p n) := Nat.mul_le_mul_left _ hwc
        _ = cw * (T n * p n) := by ring
    exact_mod_cast this
  have hSw : ((S n * w n : ℕ) : ℝ) ≤ cw * ((T n : ℝ) * p n) := by
    have : S n * w n ≤ cw * (T n * p n) := by
      calc S n * w n ≤ T n * (cw * p n) := Nat.mul_le_mul hST hwc
        _ = cw * (T n * p n) := by ring
    exact_mod_cast this
  have hSWo : ((S n * mnWo n : ℕ) : ℝ) ≤ (T n : ℝ) * p n := by
    have : S n * mnWo n ≤ T n * p n := Nat.mul_le_mul hST (by omega)
    exact_mod_cast this
  have t6 : (mnGlue n (w n) : ℝ) ≤ 20 * n + 20 * cw * ((T n : ℝ) * p n) +
      CP * ((T n : ℝ) * totMp n) := by
    have hP := hpt (w n) (by omega) hwc
    have e : mnGlue n (w n) = 20 * (T n * w n) + 20 +
        ((∏ i, t n i) * (cmulCost mnT (w n) + 6 * w n + 2) + 8) := by
      unfold mnGlue; rw [hprod]; ring
    rw [e]
    generalize ((∏ i, t n i) * (cmulCost mnT (w n) + 6 * w n + 2) + 8) = P at hP ⊢
    have hTw' : ((T n * w n : ℕ) : ℝ) = (T n : ℝ) * w n := by push_cast; ring
    rw [hTw'] at hTw
    have e2 : ((20 * (T n * w n) + 20 + P : ℕ) : ℝ) = 20 * ((T n : ℝ) * w n) + 20 + P := by
      push_cast; ring
    rw [e2]
    have e3 : 20 * (cw : ℝ) * ((T n : ℝ) * p n) = 20 * ((cw : ℝ) * ((T n : ℝ) * p n)) := by ring
    rw [e3]
    linarith
  have t7 : (mnTail n (w n) : ℝ) ≤ (4 + 4 + 2304 * (1 + 1)) * n +
      (4 * cw + 4) * ((T n : ℝ) * p n) + CR * ((S n : ℝ) * totMp n) := by
    have hrd := hrnd (mnMw n (w n)) (w n) (mnWo n) (by unfold mnMw; omega) hMw hwc hWo
    have hcr := hcar (mnWo n) hWo
    have e : mnTail n (w n) = 4 * (S n * w n) + 4 +
        roundStageCost mnT (mnMw n (w n)) (w n) (b n) (p n) (mnWo n) (S n) +
        (4 * (S n * mnWo n) + 4) + carryOutCost (mnWo n) (b n) (S n) := by
      unfold mnTail; ring
    rw [e]
    generalize roundStageCost mnT (mnMw n (w n)) (w n) (b n) (p n) (mnWo n) (S n) = Rd at hrd ⊢
    generalize carryOutCost (mnWo n) (b n) (S n) = Ca at hcr ⊢
    have e2 : ((4 * (S n * w n) + 4 + Rd + (4 * (S n * mnWo n) + 4) + Ca : ℕ) : ℝ) =
        4 * ((S n * w n : ℕ) : ℝ) + 4 + Rd + (4 * ((S n * mnWo n : ℕ) : ℝ) + 4) + Ca := by
      push_cast; ring
    rw [e2]
    have e3 : (4 * (cw : ℝ) + 4) * ((T n : ℝ) * p n) =
        4 * ((cw : ℝ) * ((T n : ℝ) * p n)) + 4 * ((T n : ℝ) * p n) := by ring
    rw [e3]
    have e4 : (2304 : ℝ) * ((1 : ℕ) + 1) = 4608 := by norm_num
    rw [e4] at hcr
    linarith
  -- the sum before the cleanup
  set Z : ℝ := n + totDirectCRT n + totResamp n + totConv n + (T n : ℝ) * totMp n +
    (S n : ℝ) * totMp n + (T n : ℝ) * p n + (b n : ℝ) ^ k with hZ
  have hpre : (mnPreCost D Y n : ℝ) ≤ M * Z := by
    have e : (mnPreCost D Y n : ℝ) = (((4 * n + 6) + (4 * n + 8) : ℕ) : ℝ) + pmCost n mnUs +
        D.cost n + ((2 * digitCost (b n) (p n) (w n) (S n) : ℕ) : ℝ) + mnRuns D Y n +
        mnGlue n (w n) + mnTail n (w n) := by
      unfold mnPreCost; push_cast; ring
    rw [e]
    have l1 : A1 * (n : ℝ) ≤ A1 * Z := mul_le_mul_of_nonneg_left (by rw [hZ]; linarith)
      (by rw [hA1]; positivity)
    have l2 : A2 * (b n : ℝ) ^ k ≤ A2 * Z := mul_le_mul_of_nonneg_left (by rw [hZ]; linarith)
      (by rw [hA2]; positivity)
    have l3 : A3 * totDirectCRT n ≤ A3 * Z := mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hCr'0
    have l4 : A3 * totResamp n ≤ A3 * Z :=
      mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hCr'0
    have l5 : A3 * totConv n ≤ A3 * Z := mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hCr'0
    have l6 : A6 * ((T n : ℝ) * totMp n) ≤ A6 * Z :=
      mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) (by rw [hA6]; positivity)
    have l7 : CR * ((S n : ℝ) * totMp n) ≤ CR * Z :=
      mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hCR0
    have l8 : A8 * ((T n : ℝ) * p n) ≤ A8 * Z :=
      mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) (by rw [hA8]; positivity)
    have hsum : (((4 * n + 6) + (4 * n + 8) : ℕ) : ℝ) + pmCost n mnUs + D.cost n +
        ((2 * digitCost (b n) (p n) (w n) (S n) : ℕ) : ℝ) + mnRuns D Y n + mnGlue n (w n) +
        mnTail n (w n) ≤
        A1 * n + A2 * (b n : ℝ) ^ k + A3 * totDirectCRT n + A3 * totResamp n + A3 * totConv n +
          A6 * ((T n : ℝ) * totMp n) + CR * ((S n : ℝ) * totMp n) + A8 * ((T n : ℝ) * p n) := by
      have e5 : Cr' * (totDirectCRT n + totResamp n + totConv n + (T n : ℝ) * totMp n +
          (T n : ℝ) * p n) = Cr' * totDirectCRT n + Cr' * totResamp n + Cr' * totConv n +
          Cr' * ((T n : ℝ) * totMp n) + Cr' * ((T n : ℝ) * p n) := by ring
      rw [e5] at t5
      rw [hA1, hA2, hA3, hA6, hA8]
      linarith
    have e2 : M * Z = A1 * Z + A2 * Z + A3 * Z + A3 * Z + A3 * Z + A6 * Z + CR * Z + A8 * Z := by
      rw [hM]; ring
    rw [e2]
    linarith
  -- the cleanup
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnZ : (n : ℝ) ≤ Z := by rw [hZ]; linarith
  have hM0 : 0 ≤ M := by
    rw [hM, hA1, hA2, hA3, hA6, hA8]; positivity
  have hZ0 : 0 ≤ Z := by linarith
  have htime : (mnTime D Y c n : ℝ) ≤ ((1 + 2 * c) * M + 2 * mnT + 6) * Z := by
    have e : (mnTime D Y c n : ℝ) = (1 + 2 * c) * (mnPreCost D Y n : ℝ) + 2 * n +
        (2 * mnT + 4) := by
      unfold mnTime; push_cast; ring
    rw [e]
    have h1 : (1 + 2 * (c : ℝ)) * (mnPreCost D Y n : ℝ) ≤ (1 + 2 * c) * (M * Z) :=
      mul_le_mul_of_nonneg_left hpre (by positivity)
    have h2 : (2 * (mnT : ℝ) + 4) ≤ (2 * mnT + 4) * Z := by
      have : (2 * (mnT : ℝ) + 4) * 1 ≤ (2 * mnT + 4) * Z :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have e2 : ((1 + 2 * c) * M + 2 * mnT + 6) * Z =
        (1 + 2 * c) * (M * Z) + 2 * Z + (2 * mnT + 4) * Z := by ring
    rw [e2]
    linarith
  -- against `totDirectBound`
  have hCk : k ≤ C := le_max_left _ _
  have hCM : (1 + 2 * c) * M + 2 * mnT + 6 ≤ (C : ℝ) := by
    have h1 : ⌈(1 + 2 * (c : ℝ)) * M + 2 * (mnT : ℝ) + 6⌉₊ ≤ C := le_max_right _ _
    have h2 : ((⌈(1 + 2 * (c : ℝ)) * M + 2 * (mnT : ℝ) + 6⌉₊ : ℕ) : ℝ) ≤ C := by exact_mod_cast h1
    exact (Nat.le_ceil _).trans h2
  have hbC : (b n : ℝ) ^ k ≤ (b n : ℝ) ^ C :=
    pow_le_pow_right₀ (by exact_mod_cast hb1) hCk
  have hZC : Z ≤ (n : ℝ) + 2 * totDirectCRT n + 3 * (totResamp n + totConv n + (T n : ℝ) * totMp n) +
      (T n : ℝ) * totMp n + (S n : ℝ) * totMp n + (T n : ℝ) * p n + ((n : ℝ) + (b n : ℝ) ^ C) := by
    rw [hZ]; linarith
  have hfin : ((1 + 2 * c) * M + 2 * mnT + 6) * Z ≤ (C : ℝ) * Z :=
    mul_le_mul_of_nonneg_right hCM hZ0
  have hfin2 : (C : ℝ) * Z ≤ totDirectBound C n := by
    unfold totDirectBound
    exact mul_le_mul_of_nonneg_left hZC (Nat.cast_nonneg _)
  linarith

end

end IntegerMultBounds.MathlibTM2.Fast.Main
