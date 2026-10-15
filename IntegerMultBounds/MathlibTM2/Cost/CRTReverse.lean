module

public import IntegerMultBounds.MathlibTM2.Fast.CRTReverseFull
public import IntegerMultBounds.MathlibTM2.Cost.MatchCRT

/-! # Linear-axis cost of the executable paired reversal -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

noncomputable section

/-- A distant pair costs no more than the existing full-volume interchange
budget. The physical gap changes geometry, not the number of interchanges. -/
theorem crtReversePairCost_le {T pre gap post aj ak B L am : ℕ}
    (hL : pre + aj + gap + ak + post = L) (hj : aj ≤ am) (hk : ak ≤ am) :
    crtReversePairCost T pre gap post aj ak B ≤
      crtStepBound T L B (2 ^ L * B) am := by
  have hswap := crtSwapCostN_mono (V := 3 * (2 ^ L * B))
    (h' := am) (w' := am) (show max aj ak ≤ max am am by simpa using max_le hj hk)
  have hswap' := Nat.mul_le_mul_left (T + 12 * swapT 6 + 5) hswap
  have haj : aj ≤ L := by omega
  have hak : ak ≤ L := by omega
  have he₁ := Nat.mul_le_mul_left aj haj
  have he₂ := Nat.mul_le_mul_left ak hak
  have he₃ : (aj + ak) * L ≤ L * L := Nat.mul_le_mul_right L (by omega)
  unfold crtReversePairCost crtStepBound
  rw [hL]
  nlinarith

/-- Exactly one interchange budget per endpoint pair, plus the final test. -/
theorem crtReverseLoopCost_le {d : ℕ} (a : Fin d → ℕ) (T B am L : ℕ)
    (ha : ∀ j, a j ≤ am) (o pre post : List (Fin d))
    (hL : crtW a pre + crtW a o + crtW a post = L) :
    crtReverseLoopCost T a B o pre post ≤
      (o.length / 2) * (crtStepBound T L B (2 ^ L * B) am + 3) + 2 := by
  induction o using List.bidirectionalRecOn generalizing pre post with
  | H0 => simp [crtReverseLoopCost]
  | H1 j => simp [crtReverseLoopCost]
  | Hn j gap k ih =>
    have hsum : crtW a pre + a j + crtW a gap + a k + crtW a post = L := by
      simpa [crtW, List.map_append, List.sum_append, Nat.add_assoc] using hL
    have hchild : crtW a (pre ++ [k]) + crtW a gap + crtW a (j :: post) = L := by
      simp [crtW, List.map_append, List.sum_append] at hsum ⊢
      omega
    have hc := ih (pre ++ [k]) (j :: post) hchild
    have hp := crtReversePairCost_le (T := T) (B := B) hsum (ha j) (ha k)
    have hhalf : (j :: (gap ++ [k])).length / 2 = gap.length / 2 + 1 := by simp; omega
    simp only [crtReverseLoopCost, List.bidirectionalRecOn, List.bidirectionalRec_cons_append]
    rw [hhalf, Nat.add_mul, one_mul]
    change crtReversePairCost T (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) B + 3 +
      crtReverseLoopCost T a B gap (pre ++ [k]) (j :: post) ≤ _
    omega

/-- Input-only budget for the full setup, reversal, stream restoration, and
scratch cleanup. It is linear in the number of axes. -/
def crtReverseBudget (T L B d am : ℕ) : ℕ :=
  d * (crtStepBound T L B (2 ^ L * B) am + 3) + 20 * L + 32 * d + 30

lemma crtEnts_map_length {d A : ℕ} (a : Fin d → ℕ) (o : List (Fin d)) :
    (crtEnts (A := A) (o.map a)).length = crtW a o + 2 * o.length := by
  induction o with
  | nil => simp [crtEnts, crtW]
  | cons j o ih =>
    simp [crtEnts_cons, crtEnt, crtW] at ih ⊢
    omega

/-- The budget in the actual execution theorem fits the linear-axis budget. -/
theorem crtReverseFull_cost_le {d A : ℕ} (a : Fin d → ℕ) (T B am : ℕ)
    (ha : ∀ j, a j ≤ am) (o : List (Fin d)) :
    crtReverseLoopCost T a B o [] [] + 14 * (crtEnts (A := A) (o.map a)).length +
      6 * crtW a o + 4 * o.length + 28 ≤
      crtReverseBudget T (crtW a o) B o.length am := by
  have h := crtReverseLoopCost_le a T B am (crtW a o) ha o [] [] (by simp [crtW])
  have hm := Nat.mul_le_mul_right (crtStepBound T (crtW a o) B (2 ^ crtW a o * B) am + 3)
    (Nat.div_le_self o.length 2)
  rw [crtEnts_map_length]
  unfold crtReverseBudget
  omega

/-- Natural-number matching: a linear number of full-volume interchanges,
with all setup and cleanup terms absorbed into a separate linear budget. -/
theorem mt_crt_reverse_arith {Tm cw L B d am p X : ℕ}
    (hX : X = 2 ^ L) (hB : B ≤ cw * p) (hLp : L ≤ p) (hp : 1 ≤ p)
    (hd : 1 ≤ d) :
    crtReverseBudget Tm L B d am ≤
      d * ((Tm + 12 * swapT 6 + 5) * crtSwapCostN (3 * (X * B)) am am) +
        (mtCrtK0 Tm cw + 85) * (d * (X * p)) := by
  have hs := mt_crt_step_le (Tm := Tm) (am := am) hX hB hLp hp
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_two_pow
  have hpX : p ≤ X * p := Nat.le_mul_of_pos_left _ hX1
  have hL : L ≤ d * (X * p) := hLp.trans (hpX.trans (Nat.le_mul_of_pos_left _ hd))
  have hd' : d ≤ d * (X * p) := Nat.le_mul_of_pos_right _ (by nlinarith)
  have h₁ : 1 ≤ d * (X * p) := hd.trans hd'
  have hm := Nat.mul_le_mul_left d hs
  unfold crtReverseBudget
  rw [← hX]
  nlinarith


open IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- Explicit constant for a linear-axis reversal in the pipeline. -/
def mtCrtReverseC (Tm cw : ℕ) : ℝ :=
  3 * (mtCrtc1 Tm : ℝ) * swapConst * cw + (mtCrtc1 Tm : ℝ) + (mtCrtK0 Tm cw + 85)

/-- The executable reversal has one axis factor, rather than the old
quadratic adjacent-walk factor. This holds throughout the large-input regime. -/
theorem mt_crt_reverse_le (Tm cw : ℕ) {n : ℕ} (h : Big n) (B am : ℕ)
    (hB : B ≤ cw * p n) (ham : am ≤ ℓ n) :
    (crtReverseBudget Tm (logT n) B (d n) am : ℝ) ≤
      mtCrtReverseC Tm cw * ((T n : ℝ) * p n * d n * (1 + (ℓ n : ℝ) ^ Parameters.tau)) := by
  have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
  have hLp : logT n ≤ p n := by have := mt_logT_le_b h; unfold p; omega
  have hℓ1 : 1 ≤ ℓ n := by have := h.two_le_ℓ; omega
  have hN := mt_crt_reverse_arith (Tm := Tm) (cw := cw) (am := am) (X := T n)
    rfl hB hLp hp1 h.one_le_d
  -- the interchange
  have hsw := mt_swapN_le (3 * (2 ^ logT n * B)) am am
  have hτ' : ((max 1 (max am am) : ℕ) : ℝ) ^ Parameters.tau ≤ (ℓ n : ℝ) ^ Parameters.tau := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ tot_tau_nonneg
    exact_mod_cast max_le hℓ1 (max_le ham ham)
  have hV : ((3 * (2 ^ logT n * B) : ℕ) : ℝ) ≤ 3 * cw * ((T n : ℝ) * p n) := by
    have : 3 * (2 ^ logT n * B) ≤ 3 * cw * (T n * p n) := by
      change 3 * (T n * B) ≤ 3 * cw * (T n * p n)
      calc 3 * (T n * B) ≤ 3 * (T n * (cw * p n)) := by gcongr
        _ = 3 * cw * (T n * p n) := by ring
    exact_mod_cast this
  rw [show Tm + 12 * swapT 6 + 5 = mtCrtc1 Tm from rfl] at hN
  set c1 : ℝ := (mtCrtc1 Tm : ℝ) with hc1
  have hc10 : 0 ≤ c1 := Nat.cast_nonneg _
  have hsc := mt_swapConst_nonneg
  have hℓτ : 0 ≤ (ℓ n : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hD : (0 : ℝ) ≤ (d n : ℝ) := Nat.cast_nonneg _
  have hTp := mt_Tp_nonneg n
  have hNr : (crtSwapCostN (3 * (2 ^ logT n * B)) am am : ℝ) ≤
      3 * swapConst * cw * ((T n : ℝ) * p n * (ℓ n : ℝ) ^ Parameters.tau) + 1 := by
    have e1 : swapConst * ((3 * (2 ^ logT n * B) : ℕ) : ℝ) *
        ((max 1 (max am am) : ℕ) : ℝ) ^ Parameters.tau ≤
        swapConst * (3 * cw * ((T n : ℝ) * p n)) * (ℓ n : ℝ) ^ Parameters.tau :=
      mul_le_mul (mul_le_mul_of_nonneg_left hV hsc) hτ' (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg hsc (by positivity))
    have e2 : swapConst * (3 * cw * ((T n : ℝ) * p n)) * (ℓ n : ℝ) ^ Parameters.tau =
        3 * swapConst * cw * ((T n : ℝ) * p n * (ℓ n : ℝ) ^ Parameters.tau) := by ring
    linarith
  have hcast : (crtReverseBudget Tm (logT n) B (d n) am : ℝ) ≤
      (d n : ℝ) * (c1 * crtSwapCostN (3 * (2 ^ logT n * B)) am am) +
        ((mtCrtK0 Tm cw + 85) : ℝ) * ((d n : ℝ) * ((T n : ℝ) * p n)) := by
    have := (Nat.cast_le (α := ℝ)).2 hN
    rw [hc1]
    push_cast at this
    exact this
  have hT1 : (1 : ℝ) ≤ (T n : ℝ) * p n := by
    have := mt_one_le_T n; have := mt_one_le_p h; nlinarith
  rw [mul_add, mul_one]
  set D := (d n : ℝ)
  set Z := (T n : ℝ) * p n
  set E := (ℓ n : ℝ) ^ Parameters.tau
  set N := (crtSwapCostN (3 * (2 ^ logT n * B)) am am : ℝ)
  set K := ((mtCrtK0 Tm cw + 85) : ℝ)
  have hK0 : (0 : ℝ) ≤ K := by
    change 0 ≤ (mtCrtK0 Tm cw : ℝ) + 85
    exact add_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have k1 : D * (c1 * N) ≤ 3 * c1 * swapConst * cw * (Z * D * E) + c1 * D :=
    calc D * (c1 * N) ≤ D * (c1 * (3 * swapConst * cw * (Z * E) + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNr hc10) hD
      _ = 3 * c1 * swapConst * cw * (Z * D * E) + c1 * D := by ring
  have k2 : c1 * D ≤ c1 * (Z * D) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hD hT1) hc10
  have k3 : K * (D * Z) = K * (Z * D) := by ring
  have hZD : 0 ≤ Z * D := mul_nonneg hTp hD
  have k4 : 0 ≤ 3 * c1 * swapConst * cw * (Z * D) := by
    have : 0 ≤ 3 * c1 * swapConst * cw := by positivity
    exact mul_nonneg this hZD
  have k5 : 0 ≤ (c1 + K) * (Z * D * E) := mul_nonneg (by linarith) (mul_nonneg hZD hℓτ)
  have k6 : (3 * c1 * swapConst * cw + c1 + K) * (Z * D + Z * D * E) =
      3 * c1 * swapConst * cw * (Z * D * E) + c1 * (Z * D) + K * (Z * D) +
        (3 * c1 * swapConst * cw * (Z * D) + (c1 + K) * (Z * D * E)) := by ring
  unfold mtCrtReverseC
  rw [← hc1, k6]
  linarith

end
end IntegerMultBounds.MathlibTM2.Cost
