module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBandLoad

/-!
# Cost matching: the banded `B̃₀` stage

The lines of the banded `B̃₀` (`bandAxisCost`, `Fast/BandAxis.lean`) cost `mtBandX` per
record: two passes over a band of `B = 2·8m + 1` entries, `m = fastWindow p α ≤ √p/(2α) + 1`,
each a product of width `w`, so `mtBandX ≤ mtBandCX · α √p M(p)` (`mt_band_X_le`), the order
of the Neumann lines.

`mt_rsbG_all_le` is `mt_rsb_all_le` for the generic driver `rsbAllCostG`: any per-axis line cost
of at most `T X + 4` and any loader cost bounds; the interchanges, banks and headers are as in
`Cost/MatchResampB.lean`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! ### The lines -/

/-- The per-record factor of one line of the banded `B̃₀`. -/
def mtBandX (Tm w B : ℕ) : ℕ := (2 * B + 4) * (rmulCost Tm w + 40 * w + 60) + 30 * (B * w) +
  400 * w + 1500

theorem mt_band_lineCost_le {Tm w s t B : ℕ} (hst : s ≤ t) (ht : 1 ≤ t) :
    bandLineCost Tm w s t B + 2 + 2 * (t * w) ≤ t * mtBandX Tm w B := by
  unfold bandLineCost bandLineInCost bandLinePassCost bandLineOutCost bandFwdStepCost mtBandX
  set R := rmulCost Tm w
  have h1 : s * (B * R) ≤ t * (B * R) := Nat.mul_le_mul_right _ hst
  have h2 : s * (B * w) ≤ t * (B * w) := Nat.mul_le_mul_right _ hst
  have h3 : s * B ≤ t * B := Nat.mul_le_mul_right _ hst
  have h4 : s * R ≤ t * R := Nat.mul_le_mul_right _ hst
  have h5 : s * w ≤ t * w := Nat.mul_le_mul_right _ hst
  have h6 : B * w ≤ t * (B * w) := Nat.le_mul_of_pos_left _ ht
  have h7 : w ≤ t * w := Nat.le_mul_of_pos_left _ ht
  have h8 : (t - s) * w ≤ t * w := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h9 : B ≤ t * B := Nat.le_mul_of_pos_left _ ht
  nlinarith

theorem mt_band_axisCost_le {Tm w s t B : ℕ} (N : ℕ) (hst : s ≤ t) (ht : 1 ≤ t) :
    bandAxisCost Tm w s t B (N / t) ≤ N * mtBandX Tm w B + 4 := by
  unfold bandAxisCost
  have h1 := mt_band_lineCost_le (Tm := Tm) (w := w) (B := B) hst ht
  have h2 : N / t * t ≤ N := Nat.div_mul_le_self N t
  set X := mtBandX Tm w B
  set M := N / t
  have h3 : M * (bandLineCost Tm w s t B + 2) + 2 * (M * t * w) ≤ M * (t * X) := by
    have : M * (bandLineCost Tm w s t B + 2 + 2 * (t * w)) ≤ M * (t * X) :=
      Nat.mul_le_mul_left _ h1
    have e : M * (bandLineCost Tm w s t B + 2 + 2 * (t * w)) =
        M * (bandLineCost Tm w s t B + 2) + 2 * (M * t * w) := by ring
    omega
  have h4 : M * (t * X) ≤ N * X := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h2
  omega

/-- The constant of one banded line against `α √p M(p)` per record. -/
noncomputable def mtBandCX (Tm cw : ℕ) : ℝ := 54 * mtCM Tm cw + 3310 * cw + 4740

/-- The band of the pipeline: `B = 2·8m + 1 ≤ 25 α √p`. -/
theorem mt_band_B_le {n : ℕ} (h : Big n) :
    ((2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1 : ℕ) : ℝ) ≤
      25 * ((alpha n : ℝ) * Real.sqrt (p n)) := by
  have hwin := mt_rsb_window_le h
  obtain ⟨hy1, -⟩ := mt_rsb_alpha_facts h
  have hα2 : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hm0 : (0 : ℝ) ≤ (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) := Nat.cast_nonneg _
  have hm : (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      (alpha n : ℝ) ^ 2 * (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) := by
    have : (1 : ℝ) ≤ (alpha n : ℝ) ^ 2 := by nlinarith
    nlinarith
  push_cast
  linarith

/-- **One banded line per record**: `mtBandX ≤ mtBandCX · α √p M(p)`. -/
theorem mt_band_X_le {n w cw : ℕ} (Tm : ℕ) (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (mtBandX Tm w (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1) : ℝ) ≤
      mtBandCX Tm cw * ((alpha n : ℝ) * Real.sqrt (p n) * totMp n) := by
  have hR := mt_rmul_le Tm h hw hwc
  have hc := mt_CM_nonneg Tm cw
  have hM1 := mt_one_le_mp h
  have hpM := mt_p_le_mp h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwM : (w : ℝ) ≤ cw * totMp n := hw'.trans (mul_le_mul_of_nonneg_left hpM hcw)
  have hB := mt_band_B_le h
  obtain ⟨hy1, -⟩ := mt_rsb_alpha_facts h
  set Bn := 2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1
  set y : ℝ := (alpha n : ℝ) * Real.sqrt (p n)
  set M := totMp n
  set R : ℝ := (rmulCost Tm w : ℝ)
  set c := mtCM Tm cw
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (Bn : ℝ) := Nat.cast_nonneg _
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have e : (mtBandX Tm w Bn : ℝ) =
      (2 * Bn + 4) * (R + 40 * w + 60) + 30 * (Bn * w) + 400 * w + 1500 := by
    simp only [mtBandX, R]; push_cast; ring
  rw [e]
  have k1 : R + 40 * w + 60 ≤ (c + 40 * cw + 60) * M := by nlinarith
  have k1' : 0 ≤ R + 40 * w + 60 := by positivity
  have k2 : (2 * (Bn : ℝ) + 4) ≤ 54 * y := by linarith
  have k3 : (2 * (Bn : ℝ) + 4) * (R + 40 * w + 60) ≤ 54 * y * ((c + 40 * cw + 60) * M) := by
    calc (2 * (Bn : ℝ) + 4) * (R + 40 * w + 60) ≤ 54 * y * (R + 40 * w + 60) := by gcongr
      _ ≤ 54 * y * ((c + 40 * cw + 60) * M) := by gcongr
  have k4 : 30 * ((Bn : ℝ) * w) ≤ 750 * cw * (y * M) := by
    have : (Bn : ℝ) * w ≤ 25 * y * (cw * M) := by
      calc (Bn : ℝ) * w ≤ 25 * y * w := by gcongr
        _ ≤ 25 * y * (cw * M) := by gcongr
    nlinarith
  have k5 : 400 * (w : ℝ) + 1500 ≤ (400 * cw + 1500) * (y * M) := by
    have hyM : (1 : ℝ) ≤ y * M := by nlinarith
    have : (400 * (w : ℝ) + 1500) ≤ (400 * cw + 1500) * M := by nlinarith
    have h0 : (0 : ℝ) ≤ (400 * cw + 1500) * M := by positivity
    nlinarith
  have : mtBandCX Tm cw * (y * M) = 54 * y * ((c + 40 * cw + 60) * M) + 750 * cw * (y * M) +
      (400 * cw + 1500) * (y * M) := by
    simp only [mtBandCX, c]; ring
  rw [this]
  linarith

/-! ### One step of the generic driver along a non-last axis -/

/-- The arithmetic of `rsbStepAxCostG`. -/
theorem mt_rsbG_stepAx_arith {Tm t₀ w a N c₁ c₂ b₁ b₂ e X B E : ℕ} {C : ℝ}
    (hax : a ≤ N * X + 4) (hc₁ : (c₁ : ℝ) ≤ C)
    (hc₂ : (c₂ : ℝ) ≤ C) (hb₁ : b₁ ≤ B) (hb₂ : b₂ ≤ B) (he : e ≤ E) :
    (rsbStepAxCostG Tm t₀ w a N c₁ c₂ b₁ b₂ e : ℝ) ≤
      (N * X + 4 : ℕ) + 2 * ((Tm + 12 * swapT t₀ + 5 : ℕ) * C) +
        (12 * B + 68 * (N * w) + 4 * Tm + 12 * swapT t₀ + 8 * E + 62 : ℕ) := by
  unfold rsbStepAxCostG rsbSwapCost
  have hK : (0 : ℝ) ≤ (Tm + 12 * swapT t₀ + 5 : ℕ) := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc₁ hK
  have h2 := mul_le_mul_of_nonneg_left hc₂ hK
  have h3 : (a : ℝ) ≤ (N * X + 4 : ℕ) := by exact_mod_cast hax
  have h4 : ((6 * b₁ + 34 * (N * w) + 2 * Tm + 6 * swapT t₀ + 23 + (4 * e + 8) + 6 * b₂ +
      34 * (N * w) + 2 * Tm + 6 * swapT t₀ + 23 + (4 * e + 8) : ℕ) : ℝ) ≤
      (12 * B + 68 * (N * w) + 4 * Tm + 12 * swapT t₀ + 8 * E + 62 : ℕ) := by
    exact_mod_cast (by omega)
  push_cast at h1 h2 h3 h4 ⊢
  linarith

/-- **One step of the generic driver along the non-last axis `i`**: the lines `T X + 4` and the
linear part `mtRsbCL · T p (ℓ^τ + 1)` (interchanges, banks, headers, stream copies). -/
theorem mt_rsbG_stepAx_le {n : ℕ} (Tm t₀ A : ℕ) (h : Big n) (hd0 : 0 < d n) (i : Fin (d n))
    (hi : (i : ℕ) + 1 < d n) {w cw a X : ℕ} (hw : 1 ≤ w) (hwc : w ≤ cw * p n)
    (hd : Fin 5 → Fin t₀) (hax : a ≤ (∏ i, t n i) * X + 4) :
    (rsbStepAxCostG Tm t₀ w a (∏ i, t n i)
        (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w) (Nat.log 2 (t n i))
          (Nat.log 2 (t n (rsbAx hd0 0))) (preHsB n w hd0 i))
        (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
          (Nat.log 2 (t n (rsbAx hd0 0))) (Nat.log 2 (t n i))
          (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)))
        (∑ j, (rsbBank (A := A) hd (preHsB n w hd0 i) j).length)
        (∑ j, (rsbBank (A := A) hd (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) j).length)
        ((preHsB n w hd0 i 3).length + (preHsB n w hd0 i 4).length + 2) : ℝ) ≤
      (T n : ℝ) * X + 4 + mtRsbCL Tm t₀ cw * mtRsbV n := by
  obtain ⟨c1, c2⟩ := mt_rsb_swap_le h hd0 i hi hw
  obtain ⟨hs1, hs2⟩ := mt_rsb_hs_le h hd0 i w
  have hb1 := mt_rsb_bank_sum_le (A := A) hd (preHsB n w hd0 i)
  have hb2 := mt_rsb_bank_sum_le (A := A) hd (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k))
  have he : (preHsB n w hd0 i 3).length + (preHsB n w hd0 i 4).length + 2 ≤
      5 * (2 * T n + 3 * w + 2 * ℓ n) + 2 := by
    have : (preHsB n w hd0 i 3).length + (preHsB n w hd0 i 4).length ≤
        ∑ k, (preHsB n w hd0 i k).length := by
      rw [Fin.sum_univ_five]; omega
    omega
  have hb1' : ∑ j, (rsbBank (A := A) hd (preHsB n w hd0 i) j).length ≤
      swapT t₀ * (1 + 5 * (2 * T n + 3 * w + 2 * ℓ n)) :=
    hb1.trans (Nat.mul_le_mul_left _ (by omega))
  have hb2' : ∑ j, (rsbBank (A := A) hd (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) j).length ≤
      swapT t₀ * (1 + 5 * (2 * T n + 3 * w + 2 * ℓ n)) :=
    hb2.trans (Nat.mul_le_mul_left _ (by omega))
  have key := mt_rsbG_stepAx_arith (t₀ := t₀) (Tm := Tm) (w := w) hax c1 c2 hb1' hb2' he
  rw [mt_prod_t h] at key ⊢
  refine key.trans ?_
  obtain ⟨v1, vT, vp, vl, vTw, vw, vTwl⟩ := mt_rsb_V_facts h hwc
  have hCL0 : mtRsbCL Tm t₀ cw = 6 * (Tm + 12 * swapT t₀ + 5 : ℕ) * swapConst * cw +
      2 * (Tm + 12 * swapT t₀ + 5 : ℕ) + 12 * swapT t₀ * (21 + 15 * cw) + 200 * cw + 4 * Tm +
      12 * swapT t₀ + 300 := rfl
  rw [hCL0]
  generalize swapT t₀ = S
  set V := mtRsbV n
  have hK1 : (0 : ℝ) ≤ ((Tm + 12 * S + 5 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsT : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg _
  have hsc := mt_swapConst_nonneg
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hTm : (0 : ℝ) ≤ (Tm : ℝ) := Nat.cast_nonneg _
  push_cast
  push_cast at hK1
  have i1 : 2 * ((Tm + 12 * S + 5) * (swapConst * ((T n : ℝ) * (3 * w)) *
      (ℓ n : ℝ) ^ Parameters.tau + 1)) ≤
      6 * (Tm + 12 * S + 5) * swapConst * cw * V + 2 * (Tm + 12 * S + 5) * V := by
    have a : swapConst * ((T n : ℝ) * (3 * w)) * (ℓ n : ℝ) ^ Parameters.tau =
        3 * swapConst * ((T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau) := by ring
    have b : 3 * swapConst * ((T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau) ≤
        3 * swapConst * (cw * V) := by
      have : (0 : ℝ) ≤ 3 * swapConst := by linarith
      exact mul_le_mul_of_nonneg_left vTwl this
    have c : ((Tm : ℝ) + 12 * S + 5) * (swapConst * ((T n : ℝ) * (3 * w)) *
        (ℓ n : ℝ) ^ Parameters.tau + 1) ≤ ((Tm : ℝ) + 12 * S + 5) * (3 * swapConst * (cw * V) + V) := by
      apply mul_le_mul_of_nonneg_left _ hK1
      rw [a]; linarith
    have e : ((Tm : ℝ) + 12 * S + 5) * (3 * swapConst * (cw * V) + V) =
        3 * ((Tm + 12 * S + 5) * swapConst * cw * V) + (Tm + 12 * S + 5) * V := by ring
    linarith
  have i2 : 12 * ((S : ℝ) * (1 + 5 * (2 * (T n : ℝ) + 3 * w + 2 * ℓ n))) ≤
      12 * S * (21 + 15 * cw) * V := by
    have h1 : (1 + 5 * (2 * (T n : ℝ) + 3 * w + 2 * ℓ n)) ≤ (21 + 15 * cw) * V := by linarith
    have := mul_le_mul_of_nonneg_left h1 hsT
    linarith
  have i3 : 68 * ((T n : ℝ) * w) + 8 * (5 * (2 * (T n : ℝ) + 3 * w + 2 * ℓ n) + 2) ≤
      (200 * cw + 300) * V := by linarith
  have i4 : 4 * (Tm : ℝ) + 12 * S + 62 ≤ (4 * Tm + 12 * S + 62) * V := by
    have : (0 : ℝ) ≤ 4 * Tm + 12 * S + 62 := by linarith
    exact le_mul_of_one_le_right this v1
  clear_value V
  clear key hax c1 c2 hb1 hb2 hb1' hb2' he hs1 hs2
  nlinarith

/-! ### All axes -/

/-- **The generic driver along all axes**, at one length `n`: per axis the lines `T X + 4`,
the linear part `mtRsbCL · T p (ℓ^τ + 1)` and the loader bound `A₁`; the first loader `A₀`. -/
theorem mt_rsbG_all_le {n : ℕ} (Tm t₀ A : ℕ) (h : Big n) (hd0 : 0 < d n) {w cw X : ℕ}
    (hw : 1 ≤ w) (hwc : w ≤ cw * p n) (hd : Fin 5 → Fin t₀) (cax : Fin (d n) → ℕ → ℕ)
    (hax : ∀ i, cax i ((∏ i, t n i) / t n i) ≤ (∏ i, t n i) * X + 4) (cp : ℕ → ℕ) (A₀ A₁ : ℝ)
    (hcp0 : (cp 0 : ℝ) ≤ A₀) (hcp : ∀ j, (cp (j + 1) : ℝ) ≤ A₁) :
    (rsbAllCostG Tm t₀ w (d n) (t n) hd0 (fun i => Nat.log 2 (t n i)) (preHsB n w hd0) cax A hd
        cp (∏ i, t n i) : ℝ) ≤
      (d n : ℝ) * ((T n : ℝ) * X + mtRsbCL Tm t₀ cw * mtRsbV n + A₁ + 8) +
        ((T n : ℝ) * X + A₀ + 2 * d n + 8) := by
  set Bs : ℝ := (T n : ℝ) * X + mtRsbCL Tm t₀ cw * mtRsbV n + A₁ + 8
  let F : ℕ → ℕ := fun j =>
      cp (j + 1) +
        rsbStepAxCostG Tm t₀ w (cax (rsbAx hd0 (j + 1)) ((∏ i, t n i) / t n (rsbAx hd0 (j + 1))))
          (∏ i, t n i)
          (BinaryInterchangeRun.cost (rsbPre (t n) (rsbAx hd0 (j + 1)))
            (rsbMid (t n) (rsbAx hd0 (j + 1))) (3 * w) (Nat.log 2 (t n (rsbAx hd0 (j + 1))))
            (Nat.log 2 (t n (rsbAx hd0 0))) (preHsB n w hd0 (rsbAx hd0 (j + 1))))
          (BinaryInterchangeRun.cost (rsbPre (t n) (rsbAx hd0 (j + 1)))
            (rsbMid (t n) (rsbAx hd0 (j + 1))) (3 * w) (Nat.log 2 (t n (rsbAx hd0 0)))
            (Nat.log 2 (t n (rsbAx hd0 (j + 1))))
            (fun k => preHsB n w hd0 (rsbAx hd0 (j + 1)) (Equiv.swap 3 4 k)))
          (∑ i, (rsbBank hd (preHsB n w hd0 (rsbAx hd0 (j + 1))) i :
            List (Fin (A + 4))).length)
          (∑ i, (rsbBank hd (fun k => preHsB n w hd0 (rsbAx hd0 (j + 1)) (Equiv.swap 3 4 k)) i :
              List (Fin (A + 4))).length)
          ((preHsB n w hd0 (rsbAx hd0 (j + 1)) 3).length +
            (preHsB n w hd0 (rsbAx hd0 (j + 1)) 4).length + 2) + 4
  have hstep : ∀ j ∈ Finset.range (d n - 1), ((F j : ℕ) : ℝ) ≤ Bs := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hi : ((rsbAx hd0 (j + 1) : Fin (d n)) : ℕ) + 1 < d n := by simp [rsbAx]; omega
    have h1 := mt_rsbG_stepAx_le Tm t₀ A h hd0 (rsbAx hd0 (j + 1)) hi hw hwc hd
      (hax (rsbAx hd0 (j + 1)))
    have h2 := hcp j
    simp only [F]
    push_cast
    linarith
  have hall : rsbAllCostG Tm t₀ w (d n) (t n) hd0 (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)
      cax A hd cp (∏ i, t n i) =
      cp 0 + cax (rsbAx hd0 0) ((∏ i, t n i) / t n (rsbAx hd0 0)) +
        ((∑ j ∈ Finset.range (d n - 1), F j) + 2 * (d n - 1) + 4) := rfl
  have hS : (∑ j ∈ Finset.range (d n - 1), ((F j : ℕ) : ℝ)) ≤ (d n - 1 : ℕ) * Bs := by
    have := Finset.sum_le_card_nsmul (Finset.range (d n - 1)) (fun j => ((F j : ℕ) : ℝ)) Bs hstep
    simpa using this
  have hax0 : (cax (rsbAx hd0 0) ((∏ i, t n i) / t n (rsbAx hd0 0)) : ℝ) ≤ T n * X + 4 := by
    have := hax (rsbAx hd0 0)
    rw [mt_prod_t h] at this ⊢
    exact_mod_cast this
  have hBs : 0 ≤ Bs := by
    have := mt_rsb_CL_nonneg Tm t₀ cw
    have hV : 0 ≤ mtRsbV n := by
      unfold mtRsbV
      have := Real.rpow_nonneg (Nat.cast_nonneg (ℓ n)) Parameters.tau
      positivity
    have : (0 : ℝ) ≤ (T n : ℝ) * X := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ mtRsbCL Tm t₀ cw * mtRsbV n := mul_nonneg (by assumption) hV
    have : (0 : ℝ) ≤ A₁ := (Nat.cast_nonneg _).trans (hcp 0)
    simp only [Bs]
    linarith
  have hd1 : ((d n - 1 : ℕ) : ℝ) ≤ d n := by
    have : d n - 1 ≤ d n := Nat.sub_le _ _
    exact_mod_cast this
  have hdB : ((d n - 1 : ℕ) : ℝ) * Bs ≤ d n * Bs := mul_le_mul_of_nonneg_right hd1 hBs
  have hd2 : ((2 * (d n - 1) : ℕ) : ℝ) ≤ 2 * d n := by
    have : 2 * (d n - 1) ≤ 2 * d n := by omega
    exact_mod_cast this
  rw [hall]
  push_cast [Nat.cast_sum] at hS hd2 ⊢
  linarith

/-! ### Against the terms of `totBound` -/

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The small loader terms of all axes: `(d + 1) mtBandU ≤ A b^6 r`. -/
theorem mt_band_small_le {n : ℕ} (h : Big n) (Tm cw cW : ℕ) :
    (d n + 1) * mtBandU n Tm cw cW ≤
      2 * (4 * 10 ^ 9 * (ssMulConst + 1) * (Tm + 1)) * 6 ^ 5 * (cW + cw + 6) ^ 5 * b n ^ 6 *
        r n := by
  have hdb : d n + 1 ≤ 2 * b n := by have := d_le_b n; have := h.sixteen_le_b; omega
  unfold mtBandU p
  calc (d n + 1) * (4 * 10 ^ 9 * (ssMulConst + 1) * (Tm + 1) * r n *
        ((cW + cw + 6) * (6 * b n)) ^ 5) ≤
      (2 * b n) * (4 * 10 ^ 9 * (ssMulConst + 1) * (Tm + 1) * r n *
        ((cW + cw + 6) * (6 * b n)) ^ 5) := Nat.mul_le_mul_right _ hdb
    _ = _ := by ring

/-- The arithmetic of `mt_band_stage_le_linear` over plain reals. -/
theorem mt_band_tail {d T p w cw X Y CX CL V U R Crt tot : ℝ} (hd1 : 1 ≤ d) (hT1 : 1 ≤ T)
    (hp1 : 1 ≤ p) (hcw : 0 ≤ cw) (hw0 : 0 ≤ w) (hw' : w ≤ cw * p) (hX0 : 0 ≤ X) (hX : X ≤ CX * Y)
    (hres : d * (T * Y) = R) (hCX : 0 ≤ CX) (hCL : 0 ≤ CL) (hR0 : 0 ≤ R) (hdV : d * V = Crt)
    (hdTp : d * (T * p) ≤ Crt) (hU : (d + 1) * U ≤ T * p)
    (hall : tot ≤ d * (T * X + CL * V + (42 * (T * w) + 300 * T + 42 + U) + 8) +
      (T * X + (42 * (T * w) + 300 * T + 42 + U) + 2 * d + 8)) :
    tot ≤ (2 * CX + CL + 84 * cw + 704) * (R + Crt + T * p) := by
  have hT0 : 0 ≤ T := by linarith
  have hTp : 1 ≤ T * p := by nlinarith
  have hCrt : 0 ≤ Crt := le_trans (by positivity) hdTp
  have l2 : d * (T * X) ≤ CX * R := by
    rw [← hres]
    have := mul_le_mul_of_nonneg_left hX (mul_nonneg (by linarith : (0 : ℝ) ≤ d) hT0)
    nlinarith
  have l3 : T * X ≤ CX * R := by
    have : T * X ≤ d * (T * X) := le_mul_of_one_le_left (mul_nonneg hT0 hX0) hd1
    linarith
  have l4 : d * (CL * V) = CL * Crt := by rw [← hdV]; ring
  have hTw : T * w ≤ cw * (T * p) := by
    have := mul_le_mul_of_nonneg_left hw' hT0; linarith
  have hTTp : T ≤ T * p := le_mul_of_one_le_right hT0 hp1
  have hTp0 : 0 ≤ T * p := by linarith
  have hA' : 42 * (T * w) + 300 * T + 42 + 8 ≤ (42 * cw + 350) * (T * p) := by
    have e : (42 * cw + 350) * (T * p) = 42 * (cw * (T * p)) + 350 * (T * p) := by ring
    rw [e]; linarith
  have l5 : (d + 1) * (42 * (T * w) + 300 * T + 42 + 8) + 2 * d ≤ (84 * cw + 702) * Crt := by
    have hdd : d + 1 ≤ 2 * d := by linarith
    have h0 : 0 ≤ 42 * (T * w) + 300 * T + 42 + 8 := by
      have : 0 ≤ T * w := mul_nonneg hT0 hw0
      linarith
    have a1 : (d + 1) * (42 * (T * w) + 300 * T + 42 + 8) ≤
        (2 * d) * ((42 * cw + 350) * (T * p)) :=
      mul_le_mul hdd hA' h0 (by linarith)
    have a2 : 2 * d ≤ 2 * (d * (T * p)) := by nlinarith
    have e : (2 * d) * ((42 * cw + 350) * (T * p)) = (84 * cw + 700) * (d * (T * p)) := by ring
    have a3 : (84 * cw + 700) * (d * (T * p)) ≤ (84 * cw + 700) * Crt :=
      mul_le_mul_of_nonneg_left hdTp (by linarith)
    nlinarith
  have e : d * (T * X + CL * V + (42 * (T * w) + 300 * T + 42 + U) + 8) +
      (T * X + (42 * (T * w) + 300 * T + 42 + U) + 2 * d + 8) =
      d * (T * X) + T * X + d * (CL * V) +
        ((d + 1) * (42 * (T * w) + 300 * T + 42 + 8) + 2 * d) + (d + 1) * U := by ring
  rw [e] at hall
  have e2 : (2 * CX + CL + 84 * cw + 704) * (R + Crt + T * p) =
      2 * CX * R + 2 * (CX * Crt) + 2 * (CX * (T * p)) + CL * R + CL * Crt + CL * (T * p) +
        (84 * cw + 704) * R + (84 * cw + 702) * Crt + 2 * Crt + (84 * cw + 704) * (T * p) := by
    ring
  rw [e2]
  have p1 := mul_nonneg hCX hCrt
  have p2 := mul_nonneg hCX (by linarith : (0 : ℝ) ≤ T * p)
  have p3 := mul_nonneg hCL hR0
  have p4 := mul_nonneg hCL (by linarith : (0 : ℝ) ≤ T * p)
  have p5 := mul_nonneg (by linarith : (0 : ℝ) ≤ 84 * cw + 704) hR0
  have p8 : T * p ≤ (84 * cw + 704) * (T * p) := by nlinarith
  linarith

/-- **The cost of the banded `B̃₀` stage with its loader** (`bandStage_exec`) against
`totBound`: for fixed host stack count `Tm`, bank `t₀`, alphabet `prime + Ka` and width ratios
`cw`, `cW`, eventually, for every base file `σ₀` of the band stage whose cleared registers hold
at most `T w` symbols, the stage costs at most `C (totResamp + totDirectCRT + T p)`. -/
theorem mt_band_stage_le_linear (Tm t₀ Ka cw cW : ℕ) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W : ℕ)
      (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + Ka + 4))) (hd : Fin 5 → Fin t₀)
      (rest : List (Fin (prime + Ka + 4))),
      1 ≤ w → w ≤ cw * p n → W ≤ cW * p n → BandBase σ₀ w hd → 3 ≤ prime + Ka →
      (∀ r ∈ bandClrB hd, (σ₀ r).length ≤ T n * w) →
      (rsbAllCostG Tm t₀ w (d n) (t n) hd0 (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)
          (fun i nl => bandAxisCost Tm w (s n i) (t n i)
            (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1) nl)
          (prime + Ka) hd (bandCpB Tm σ₀ hd n w W hd0 rest) (∏ i, t n i) : ℝ) ≤
        C * (totResamp n + totDirectCRT n + T n * p n) := by
  refine ⟨2 * mtBandCX Tm cw + mtRsbCL Tm t₀ cw + 84 * cw + 704, ?_⟩
  filter_upwards [eventually_big,
    mt_small_le (2 * (4 * 10 ^ 9 * (ssMulConst + 1) * (Tm + 1)) * 6 ^ 5 * (cW + cw + 6) ^ 5) 6]
    with n h hsm hd0 w W σ₀ hd rest hw hwc hWc hbase hA3 hσ₀
  have hcp : ∀ k, (bandCpB Tm σ₀ hd n w W hd0 rest k : ℝ) ≤
      42 * ((T n : ℝ) * w) + 300 * T n + 42 + (mtBandU n Tm cw cW : ℝ) := fun k => by
    exact_mod_cast mt_band_cp_le h hd0 (Tm := Tm) hwc hWc hA3 σ₀ hd rest hbase hσ₀ k
  have hall := mt_rsbG_all_le Tm t₀ (prime + Ka) h hd0
    (X := mtBandX Tm w (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1)) hw hwc hd
    (fun i nl => bandAxisCost Tm w (s n i) (t n i)
      (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1) nl)
    (fun i => mt_band_axisCost_le _ (mt_s_lt_t h i).le (mt_t_pos n i))
    (bandCpB Tm σ₀ hd n w W hd0 rest) _ _ (hcp 0) (fun j => hcp (j + 1))
  have hU := hsm _ (mt_band_small_le h Tm cw cW)
  push_cast at hU
  exact mt_band_tail (by exact_mod_cast h.one_le_d) (mt_one_le_T n) (mt_one_le_p h)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hwc) (Nat.cast_nonneg _) (mt_band_X_le Tm h hw hwc)
    (mt_rsb_resamp_eq n) (by unfold mtBandCX; have := mt_CM_nonneg Tm cw; positivity)
    (mt_rsb_CL_nonneg Tm t₀ cw) (mt_resamp_nonneg n)
    (by unfold mtRsbV totDirectCRT; ring) (mt_directCRT_dTp_le n) hU hall

end IntegerMultBounds.MathlibTM2.Cost
