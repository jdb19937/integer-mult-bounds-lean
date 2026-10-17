module

import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Fast.CRTMachine
import IntegerMultBounds.MathlibTM2.Mult.Pipeline
public import IntegerMultBounds.MathlibTM2.Cost.Total
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Cost matching: the CRT layout machines (F4, F9)

`crtForward_runs` and `crtInverse_runs` (`Fast/CRTMachine`) run within
`crtCost Tm (crtPre a d) B d am amin` steps on a host of `Tm` stacks: total axis width
`L = crtPre a d`, records of `B` symbols, axis widths at most `am`. At the pipeline the axes are
the padded box `∏ [0, t_i)`: `a i = log₂ t_i`, so `L = logT` (`mt_crt_pre_eq`) and `2^L = T`;
`am ≤ ℓ` and the records are coefficients, `B ≤ cw p`.

* `mt_crt_step_le`, `mt_crt_rot_le`, `mt_crt_arith`: in `ℕ`, with `X = 2^L`,
  `crtCost ≤ d² (Tm + 12 swapT 6 + 5) N + mtCrtK Tm cw · d² X p`, where
  `N = crtSwapCostN (3 X B) am am` is the vendored interchange of one adjacent swap.
* `mt_crt_le`: eventually `crtCost Tm logT B d am amin ≤ mtCrtC Tm cw · totCRT`, with
  `totCRT = T p d² (1 + ℓ^τ)` and the explicit constant
  `mtCrtC Tm cw = 3 (Tm + 12 swapT 6 + 5) swapConst cw + (Tm + 12 swapT 6 + 5) + mtCrtK Tm cw`:
  the `d²` interchanges of volume `3 T B` give `d² T p ℓ^τ`, everything else `O(d² T p)`.
* `mt_crt_le_pre`: the same at `L = crtPre (fun j => log₂ t_j) d`, the form of the machines'
  contracts.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds

/-! ### The arithmetic in `ℕ` -/

/-- The host steps per interchange step of the CRT swaps, `Tm + 12 swapT 6 + 5`. -/
noncomputable def mtCrtc1 (Tm : ℕ) : ℕ := Tm + 12 * swapT 6 + 5

/-- The constant of the per-step part of `crtStepBound` against `X p`. -/
noncomputable def mtCrtK0 (Tm cw : ℕ) : ℕ :=
  (6 * swapT 6 + 10) * (3 * cw + 3) + 52 * cw + 2 * Tm + 6 * swapT 6 + 167

/-- The constant of the `O(d² X p)` part of `crtCost`. -/
noncomputable def mtCrtK (Tm cw : ℕ) : ℕ :=
  mtCrtK0 Tm cw + (24 * cw + 253) + 74 + 2 + (10 * cw + 39) + 36 * cw ^ 2 + 60 * cw + 112 + 4

/-- One adjacent swap: `crtStepBound + 2 ≤ (Tm + 12 swapT 6 + 5) N + mtCrtK0 · X p`. -/
theorem mt_crt_step_le {Tm cw L B am p X : ℕ} (hX : X = 2 ^ L) (hB : B ≤ cw * p)
    (hLp : L ≤ p) (hp : 1 ≤ p) :
    crtStepBound Tm L B (X * B) am + 2 ≤
      (Tm + 12 * swapT 6 + 5) * crtSwapCostN (3 * (X * B)) am am + mtCrtK0 Tm cw * (X * p) := by
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_two_pow
  have hLX : L ≤ X := by rw [hX]; exact (Nat.lt_two_pow_self).le
  have hpXp : p ≤ X * p := Nat.le_mul_of_pos_left _ hX1
  have h1 : 1 ≤ X * p := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hBX : X * B ≤ cw * (X * p) := by
    calc X * B ≤ X * (cw * p) := Nat.mul_le_mul_left _ hB
      _ = cw * (X * p) := by ring
  have hB' : B ≤ cw * (X * p) := hB.trans (Nat.mul_le_mul_left _ hpXp)
  have hL2 : L * (4 * L + 41) ≤ 45 * (X * p) := by
    have e1 : L * L ≤ X * p := Nat.mul_le_mul hLX hLp
    have e2 : L ≤ X * p := hLp.trans hpXp
    nlinarith
  have hL3 : L + 3 * B + 2 ≤ (3 * cw + 3) * (X * p) := by nlinarith
  have hS := Nat.mul_le_mul_left (6 * swapT 6 + 10) hL3
  have hT : 2 * Tm ≤ 2 * Tm * (X * p) := Nat.le_mul_of_pos_right _ h1
  have hs6 : 6 * swapT 6 ≤ 6 * swapT 6 * (X * p) := Nat.le_mul_of_pos_right _ h1
  unfold crtStepBound mtCrtK0
  nlinarith

/-- The rotation pass and the iteration's linear terms: at most `(24 cw + 253 + 74) X p`. -/
theorem mt_crt_rot_le {cw L B am amin p X d : ℕ} (hX : X = 2 ^ L) (hB : B ≤ cw * p)
    (hLp : L ≤ p) (hp : 1 ≤ p) (ham : 2 ^ am ≤ X) (hamp : am ≤ p) (hdp : d ≤ p) :
    crtRotU L am amin B + 12 * L + 8 * 2 ^ am + 4 * d + 50 ≤ (24 * cw + 253 + 74) * (X * p) := by
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_two_pow
  have hpXp : p ≤ X * p := Nat.le_mul_of_pos_left _ hX1
  have hXXp : X ≤ X * p := Nat.le_mul_of_pos_right _ hp
  have h1 : 1 ≤ X * p := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hBX : 2 ^ L * B ≤ cw * (X * p) := by
    rw [← hX]
    calc X * B ≤ X * (cw * p) := Nat.mul_le_mul_left _ hB
      _ = cw * (X * p) := by ring
  have hB' : B ≤ cw * (X * p) := hB.trans (Nat.mul_le_mul_left _ hpXp)
  have hsub : 2 ^ (L - amin) ≤ X := by rw [hX]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrot : 2 ^ (L - amin) * (10 * L + 61) ≤ 71 * (X * p) := by
    calc 2 ^ (L - amin) * (10 * L + 61) ≤ X * (71 * p) := Nat.mul_le_mul hsub (by omega)
      _ = 71 * (X * p) := by ring
  unfold crtRotU
  rw [← hX]
  nlinarith

/-- **The CRT cost in `ℕ`**: `crtCost ≤ d² (Tm + 12 swapT 6 + 5) N + mtCrtK · d² X p`. -/
theorem mt_crt_arith {Tm cw L B d am amin p X : ℕ} (hX : X = 2 ^ L) (hB : B ≤ cw * p)
    (hLp : L ≤ p) (hp : 1 ≤ p) (hpX : p ≤ X) (ham : 2 ^ am ≤ X) (hamp : am ≤ p) (hd : 1 ≤ d)
    (hdp : d ≤ p) :
    crtCost Tm L B d am amin ≤
      d * d * ((Tm + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ L * B)) am am) +
        mtCrtK Tm cw * (d * d * (X * p)) := by
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_two_pow
  have hpXp : p ≤ X * p := Nat.le_mul_of_pos_left _ hX1
  have hXXp : X ≤ X * p := Nat.le_mul_of_pos_right _ hp
  have h1 : 1 ≤ X * p := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hstep := mt_crt_step_le (Tm := Tm) (am := am) hX hB hLp hp
  have hrot := mt_crt_rot_le (amin := amin) (d := d) hX hB hLp hp ham hamp hdp
  subst hX
  set N := (Tm + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ L * B)) am am with hN
  set Z := 2 ^ L * p with hZ
  have hiter : crtIterU Tm L B d am amin ≤
      d * N + (mtCrtK0 Tm cw + (24 * cw + 253 + 74)) * (d * Z) := by
    unfold crtIterU
    have e1 : d * (crtStepBound Tm L B (2 ^ L * B) am + 2) ≤ d * N + mtCrtK0 Tm cw * (d * Z) :=
      calc d * (crtStepBound Tm L B (2 ^ L * B) am + 2) ≤ d * (N + mtCrtK0 Tm cw * Z) :=
            Nat.mul_le_mul_left d hstep
        _ = d * N + mtCrtK0 Tm cw * (d * Z) := by ring
    have e2 : (24 * cw + 253 + 74) * Z ≤ (24 * cw + 253 + 74) * (d * Z) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hd)
    have e3 : (mtCrtK0 Tm cw + (24 * cw + 253 + 74)) * (d * Z) =
        mtCrtK0 Tm cw * (d * Z) + (24 * cw + 253 + 74) * (d * Z) := by ring
    rw [e3]
    omega
  have hdZ : Z ≤ d * Z := Nat.le_mul_of_pos_left _ hd
  have hddZ : d * Z ≤ d * d * Z := by
    rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hd
  set W := d * d * Z with hW
  have hZW : Z ≤ W := hdZ.trans hddZ
  have hit2 : d * (crtIterU Tm L B d am amin + 2) ≤
      d * d * N + (mtCrtK0 Tm cw + (24 * cw + 253 + 74) + 2) * W := by
    have e1 := Nat.mul_le_mul_left d hiter
    have e2 : d * 2 ≤ 2 * W := by
      have : d ≤ W := (hdp.trans hpXp).trans hZW
      omega
    calc d * (crtIterU Tm L B d am amin + 2) = d * crtIterU Tm L B d am amin + d * 2 := by ring
      _ ≤ d * (d * N + (mtCrtK0 Tm cw + (24 * cw + 253 + 74)) * (d * Z)) + 2 * W :=
          Nat.add_le_add e1 e2
      _ = d * d * N + (mtCrtK0 Tm cw + (24 * cw + 253 + 74) + 2) * W := by rw [hW]; ring
  have hpad : 2 ^ L * (10 * B + 10 * L + 29) ≤ (10 * cw + 39) * W := by
    have : 10 * B + 10 * L + 29 ≤ (10 * cw + 39) * p := by nlinarith
    calc 2 ^ L * (10 * B + 10 * L + 29) ≤ 2 ^ L * ((10 * cw + 39) * p) :=
          Nat.mul_le_mul_left _ this
      _ = (10 * cw + 39) * Z := by rw [hZ]; ring
      _ ≤ (10 * cw + 39) * W := Nat.mul_le_mul_left _ hZW
  have hBB : 36 * B ^ 2 ≤ 36 * cw ^ 2 * W := by
    have e1 : B * B ≤ (cw * p) * (cw * p) := Nat.mul_le_mul hB hB
    have e2 : (cw * p) * (cw * p) ≤ cw ^ 2 * W := by
      calc (cw * p) * (cw * p) = cw ^ 2 * (p * p) := by ring
        _ ≤ cw ^ 2 * (2 ^ L * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpX)
        _ ≤ cw ^ 2 * W := Nat.mul_le_mul_left _ hZW
    have e3 : B ^ 2 = B * B := sq B
    have e4 : 36 * cw ^ 2 * W = 36 * (cw ^ 2 * W) := by ring
    rw [e3, e4]
    omega
  have hB' : 60 * B ≤ 60 * cw * W := by
    have : B ≤ cw * W := hB.trans (Nat.mul_le_mul_left _ (hpXp.trans hZW))
    have e : 60 * cw * W = 60 * (cw * W) := by ring
    omega
  have hL' : L ≤ W := (hLp.trans hpXp).trans hZW
  have hd' : d ≤ W := (hdp.trans hpXp).trans hZW
  have hdY : 4 * (d * 2 ^ am) ≤ 4 * W := by
    have : d * 2 ^ am ≤ W := by
      calc d * 2 ^ am ≤ d * 2 ^ L := Nat.mul_le_mul_left _ ham
        _ ≤ d * Z := Nat.mul_le_mul_left _ hXXp
        _ ≤ W := hddZ
    omega
  have hW1 : 1 ≤ W := h1.trans hZW
  have e : (mtCrtK0 Tm cw + (24 * cw + 253) + 74 + 2 + (10 * cw + 39) + 36 * cw ^ 2 + 60 * cw +
      112 + 4) * W = (mtCrtK0 Tm cw + (24 * cw + 253 + 74) + 2) * W + (10 * cw + 39) * W +
        36 * cw ^ 2 * W + 60 * cw * W + 112 * W + 4 * W := by ring
  unfold crtCost mtCrtK
  rw [e]
  omega

/-! ### The pipeline -/

/-- The total width of the padded box: `∑ log₂ t_i = logT`. -/
theorem mt_crt_pre_eq {n : ℕ} (h : Big n) :
    crtPre (fun j => Nat.log 2 (t n j)) (d n) = logT n := by
  rw [crtPre, crtLow_of_le le_rfl]
  apply Nat.pow_right_injective (le_refl 2)
  change 2 ^ (∑ j, Nat.log 2 (t n j)) = 2 ^ logT n
  rw [Finset.prod_pow_eq_pow_sum Finset.univ (fun j => Nat.log 2 (t n j)) 2 |>.symm]
  rw [show (2 : ℕ) ^ logT n = T n from rfl, ← prod_t h.one_le_d]
  exact Finset.prod_congr rfl fun j _ => (IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log n j).symm

/-- The constant of `mt_crt_le`. -/
noncomputable def mtCrtC (Tm cw : ℕ) : ℝ :=
  3 * (mtCrtc1 Tm : ℝ) * swapConst * cw + (mtCrtc1 Tm : ℝ) + mtCrtK Tm cw

/-- **The CRT layout machines against `totCRT`.** For records of `B ≤ cw p` symbols and axis
widths at most `am ≤ ℓ`, eventually `crtCost Tm logT B d am amin ≤ mtCrtC Tm cw · totCRT`. -/
theorem mt_crt_le (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ B am amin : ℕ, B ≤ cw * p n → am ≤ ℓ n →
      (crtCost Tm (logT n) B (d n) am amin : ℝ) ≤ mtCrtC Tm cw * totCRT n := by
  filter_upwards [eventually_big, mt_poly_r_le_T 6 1] with n h hpT B am amin hB ham
  have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hpX : p n ≤ T n := by
    have : p n ≤ 6 * b n ^ 1 * r n := by
      rw [pow_one]; unfold p; exact Nat.le_mul_of_pos_right _ hr1
    exact this.trans hpT
  have hamℓ : 2 ^ am ≤ T n :=
    (Nat.pow_le_pow_right (by norm_num) ham).trans (mt_r_le_T h)
  have hℓp := mt_ℓ_le_p h
  have hdp : d n ≤ p n := by have := mt_d_le_b n; unfold p; omega
  have hLp : logT n ≤ p n := by have := mt_logT_le_b h; unfold p; omega
  have hℓ1 : 1 ≤ ℓ n := by have := h.two_le_ℓ; omega
  have hN := mt_crt_arith (Tm := Tm) (cw := cw) (amin := amin) (X := T n) rfl hB hLp hp1 hpX
    hamℓ (ham.trans hℓp) h.one_le_d hdp
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
  have hD : (0 : ℝ) ≤ (d n : ℝ) * d n := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
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
  have hcast : (crtCost Tm (logT n) B (d n) am amin : ℝ) ≤
      (d n : ℝ) * d n * (c1 * crtSwapCostN (3 * (2 ^ logT n * B)) am am) +
        (mtCrtK Tm cw : ℝ) * ((d n : ℝ) * d n * ((T n : ℝ) * p n)) := by
    have := (Nat.cast_le (α := ℝ)).2 hN
    rw [hc1]
    push_cast at this
    exact this
  have hT1 : (1 : ℝ) ≤ (T n : ℝ) * p n := by
    have := mt_one_le_T n; have := mt_one_le_p h; nlinarith
  rw [mt_crt_eq]
  have hsq : (d n : ℝ) ^ 2 = (d n : ℝ) * d n := sq _
  rw [hsq]
  set D := (d n : ℝ) * d n
  set Z := (T n : ℝ) * p n
  set E := (ℓ n : ℝ) ^ Parameters.tau
  set N := (crtSwapCostN (3 * (2 ^ logT n * B)) am am : ℝ)
  set K := (mtCrtK Tm cw : ℝ)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
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
  unfold mtCrtC
  rw [← hc1, k6]
  linarith

/-- `mt_crt_le` at the total width of the machines' contracts, `crtPre (log₂ t) d`. -/
theorem mt_crt_le_pre (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ B am amin : ℕ, B ≤ cw * p n → am ≤ ℓ n →
      (crtCost Tm (crtPre (fun j => Nat.log 2 (t n j)) (d n)) B (d n) am amin : ℝ) ≤
        mtCrtC Tm cw * totCRT n := by
  filter_upwards [mt_crt_le Tm cw, eventually_big] with n hn h B am amin hB ham
  rw [mt_crt_pre_eq h]
  exact hn B am amin hB ham

end IntegerMultBounds.MathlibTM2.Cost
