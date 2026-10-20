module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Fast.ConvBox
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Cost matching: the complex convolution box without its transforms (F5, F6, F8)

`cvBox_convBox` (`Fast/ConvBox`) runs within
`cvBoxCost Tm p l w S M cF cO` steps on a host of `Tm` stacks; at the pipeline `p = p n`,
`l = ℓ n`, `M = cvM (cvAx t) = 2^S` records of `r = 2^ℓ` coefficients with `M r = T`
(`cv_M_mul_r`), `S = Σ_{i < d-1} log₂ t_i`, and `p + 2 ≤ w ≤ cw p`. The transforms `cF`, `cO`
are matched elsewhere; here `cF = cO = 0`.

* `mt_cv_fix_le`: the record-count-free part `rpFixCost` of the ring products (header decoding,
  constants, sealing) is at most `mtCvKf cw · X p` for `2^l, p ≤ X`.
* `mt_cv_arith`: in `ℕ`, `cvBoxCost Tm p l w S M 0 0 ≤ 3 X cmulCost Tm w +
  3 M rpRingBound (wOf p l w 2^l) + mtCvK cw · X p` for `M 2^l = X`.
* `mt_cv_ring_le`: the packed product on `N = wOf p l w · 2^l ≤ (6 + 4 cw) r p` bits costs at
  most `(4 costC + 261000) grRingConst (6 + 4 cw) · r p grLogLog (r p)` (`gr_ringBound_le`).
* `mt_cv_box_le`: eventually
  `cvBoxCost ≤ mtCvC Tm cw (T M(p) + T p grLogLog (r p))`, with the explicit constant
  `mtCvC Tm cw = 3 mtCM Tm cw + mtCvK cw + 3(4 costC + 261000) grRingConst (6 + 4 cw)`:
  the twists are `3 T M(p)` (the term `3 T M(p)` of `totBound`), the ring products
  `T p grLogLog (r p)` (the `grLogLog (r p)` part of `totConv`), the rest `O(T p)`.
* `mt_cv_box_le_conv`: the same against `totConv + T M(p)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds
  IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule
  IntegerMultBounds.Spec.SignedRingProduct

/-! ### The arithmetic in `ℕ` -/

/-- `wOf p l w ≤ 2 (2p + l + 2w)`. -/
theorem mt_cv_wOf_le (p l w : ℕ) (hp : 1 ≤ p) : wOf p l w ≤ 2 * (2 * p + l + 2 * w) := by
  unfold wOf mW
  have := gr_two_pow_size_le (x := p + p + l + w + w) (by omega)
  omega

/-- The constant of `rpFixCost` against `X p`. -/
noncomputable def mtCvKf (cw : ℕ) : ℕ :=
  3 * (260 * (4 + 2 * cw) + 5000 + 42 * (38 + 12 * cw ^ 2) + 210 + 10 * cw +
    2000 * (6 + 4 * cw) + 1000 * (6 + 4 * cw) + 6000 + 100 + 80 + 10 * cw +
    6 * (6 + 4 * cw) + 4 * (6 + 4 * cw) + 8 + 10 * (6 + 4 * cw) + 4 * (4 + 2 * cw) + 1060) + 600

/-- **The fixed part of the ring products**: `rpFixCost p l w ≤ mtCvKf cw · X p` for
`l ≤ p`, `w ≤ cw p`, `2^l ≤ X`, `p ≤ X`. -/
theorem mt_cv_fix_le {Tm cw p l w X : ℕ} (hp : 1 ≤ p) (hl : l ≤ p) (hw : w ≤ cw * p)
    (hrX : 2 ^ l ≤ X) (hpX : p ≤ X) : rpFixCost p l w ≤ mtCvKf cw * (X * p) := by
  set Q := X * p with hQ
  set r := 2 ^ l with hr
  have hX1 : 1 ≤ X := le_trans hp hpX
  have hpQ : p ≤ Q := Nat.le_mul_of_pos_left _ hX1
  have hXQ : X ≤ Q := Nat.le_mul_of_pos_right _ hp
  have hrQ : r ≤ Q := hrX.trans hXQ
  have hlQ : l ≤ Q := hl.trans hpQ
  have hwQ : w ≤ cw * Q := hw.trans (Nat.mul_le_mul_left _ hpQ)
  have hppQ : p * p ≤ Q := by rw [hQ, mul_comm X]; exact Nat.mul_le_mul_left _ hpX
  have hprQ : p * r ≤ Q := by rw [hQ, mul_comm X]; exact Nat.mul_le_mul_left _ hrX
  -- the packed width
  set V := wOf p l w with hV
  have hV1 : V ≤ (6 + 4 * cw) * p := by
    have := mt_cv_wOf_le p l w hp
    linarith
  have hVQ : V ≤ (6 + 4 * cw) * Q := hV1.trans (Nat.mul_le_mul_left _ hpQ)
  have hVr : V * r ≤ (6 + 4 * cw) * Q := by
    calc V * r ≤ (6 + 4 * cw) * p * r := Nat.mul_le_mul_right _ hV1
      _ = (6 + 4 * cw) * (p * r) := by ring
      _ ≤ (6 + 4 * cw) * Q := Nat.mul_le_mul_left _ hprQ
  -- the header
  set H := (header p r w).length with hH
  have hH1 : H ≤ 2 * (p + r + w) := ring_header_length_le p r w
  have hHQ : H ≤ (4 + 2 * cw) * Q := by linarith
  -- the header decoding
  have hsp : Nat.size p ≤ p := Nat.size_le.2 Nat.lt_two_pow_self
  have hsw : Nat.size w ≤ w := Nat.size_le.2 Nat.lt_two_pow_self
  have hsr : Nat.size r ≤ 2 * p := by
    have : Nat.size r ≤ l + 1 := Nat.size_le.2 (Nat.pow_lt_pow_right (by norm_num) (by omega))
    omega
  have e1 : Nat.size p * (Nat.size p + p + 10) ≤ 12 * Q := by
    have : Nat.size p * (Nat.size p + p + 10) ≤ p * (2 * p + 10 * p) :=
      Nat.mul_le_mul hsp (by omega)
    linarith
  have e2 : Nat.size r * (Nat.size r + r + 10) ≤ 26 * Q := by
    have : Nat.size r * (Nat.size r + r + 10) ≤ (2 * p) * (12 * p + r) :=
      Nat.mul_le_mul hsr (by omega)
    linarith
  have e3 : Nat.size w * (Nat.size w + w + 10) ≤ 12 * cw ^ 2 * Q := by
    have h1 : Nat.size w * (Nat.size w + w + 10) ≤ w * (12 * w) := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0]; simp
      · exact Nat.mul_le_mul hsw (by omega)
    have h2 : w * w ≤ cw ^ 2 * Q := by
      calc w * w ≤ (cw * p) * (cw * p) := Nat.mul_le_mul hw hw
        _ = cw ^ 2 * (p * p) := by ring
        _ ≤ cw ^ 2 * Q := Nat.mul_le_mul_left _ hppQ
    linarith
  have hhdr : headerCost p r w H ≤
      (260 * (4 + 2 * cw) + 5000 + 42 * (38 + 12 * cw ^ 2) + 210 + 10 * cw) * Q := by
    unfold headerCost
    have hQ1 : 1 ≤ Q := hX1.trans hXQ
    linarith
  have hconst : constCost p l w ≤ (2000 * (6 + 4 * cw) + 1000 * (6 + 4 * cw) + 6000) * Q := by
    unfold constCost
    rw [← hV, ← hr]
    have hQ1 : 1 ≤ Q := hX1.trans hXQ
    linarith
  have hrest : 100 * r + 60 * l + 10 * (p + l + w) + 6 * (V * r) + 4 * r * (V + 2) +
      10 * V + 4 * H + 1060 ≤
      (100 + 80 + 10 * cw + 6 * (6 + 4 * cw) + 4 * (6 + 4 * cw) + 8 + 10 * (6 + 4 * cw) +
        4 * (4 + 2 * cw) + 1060) * Q := by
    have hQ1 : 1 ≤ Q := hX1.trans hXQ
    have : 4 * r * (V + 2) = 4 * (V * r) + 8 * r := by ring
    linarith
  have hinner : headerCost p r w H + constCost p l w + 100 * r + 60 * l + 10 * (p + l + w) +
      6 * (V * r) + 4 * r * (V + 2) + 10 * V + 4 * H + 1060 ≤
      (260 * (4 + 2 * cw) + 5000 + 42 * (38 + 12 * cw ^ 2) + 210 + 10 * cw +
        2000 * (6 + 4 * cw) + 1000 * (6 + 4 * cw) + 6000 + 100 + 80 + 10 * cw +
        6 * (6 + 4 * cw) + 4 * (6 + 4 * cw) + 8 + 10 * (6 + 4 * cw) + 4 * (4 + 2 * cw) + 1060) *
          Q := by linarith
  have hT : 2 * Tm ≤ 2 * Tm * Q := Nat.le_mul_of_pos_right _ (hX1.trans hXQ)
  unfold rpFixCost mtCvKf
  rw [← hr, ← hV, ← hH]
  have hm := Nat.mul_le_mul_left 3 hinner
  have hQ1 : 1 ≤ Q := hX1.trans hXQ
  linarith

/-- The constant of the `O(X p)` part of `cvBoxCost`. -/
noncomputable def mtCvK (cw : ℕ) : ℕ :=
  3 * (180 * cw + 604) + 100 * cw + mtCvKf cw + 18 * cw + 42 + 16 * cw + 16 +
    6 * cw + 4 + 14 + 4 + 2 * cw + 2

/-- **The convolution box in `ℕ`** (transforms excluded): for `M 2^l = X`, `l, S ≤ p ≤ X`,
`w ≤ cw p`, `cvBoxCost Tm p l w S M 0 0 ≤ 3 X cmulCost Tm w +
3 M rpRingBound (wOf p l w · 2^l) + mtCvK cw · X p`. -/
theorem mt_cv_arith {Tm cw p l w S M X : ℕ} (hMX : M * 2 ^ l = X) (hp : 1 ≤ p) (hl : l ≤ p)
    (hS : S ≤ p) (hw : w ≤ cw * p) (hpX : p ≤ X) :
    cvBoxCost Tm p l w S M 0 0 ≤
      3 * (X * cmulCost Tm w) + 3 * (M * rpRingBound (wOf p l w * 2 ^ l)) +
        mtCvK cw * (X * p) := by
  have hX1 : 1 ≤ X := le_trans hp hpX
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0] at hMX; omega
    · exact h0
  have hrX : 2 ^ l ≤ X := by rw [← hMX]; exact Nat.le_mul_of_pos_left _ hM1
  have hMX' : M ≤ X := by rw [← hMX]; exact Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  set Q := X * p with hQ
  have hpQ : p ≤ Q := Nat.le_mul_of_pos_left _ hX1
  have hXQ : X ≤ Q := Nat.le_mul_of_pos_right _ hp
  have hQ1 : 1 ≤ Q := hX1.trans hXQ
  have hXw : X * w ≤ cw * Q := by
    calc X * w ≤ X * (cw * p) := Nat.mul_le_mul_left _ hw
      _ = cw * Q := by rw [hQ]; ring
  have hfix := mt_cv_fix_le (Tm := Tm) hp hl hw hrX hpX
  rw [← hQ] at hfix
  have hrp := rpCost_le p l w M
  -- the per-record part of `rpRecBound`
  have hrec : M * rpRecBound p l w ≤ 3 * (M * rpRingBound (wOf p l w * 2 ^ l)) +
      (3 * (180 * cw + 604) + 100 * cw) * Q := by
    unfold rpRecBound
    have e : M * (3 * (rpRingBound (wOf p l w * 2 ^ l) + 2 ^ l * (180 * w + 400) + 204) +
        100 * (2 ^ l * w)) = 3 * (M * rpRingBound (wOf p l w * 2 ^ l)) +
          (3 * ((M * 2 ^ l) * (180 * w + 400) + 204 * M) + 100 * ((M * 2 ^ l) * w)) := by
      ring
    rw [e, hMX]
    have h1 : X * (180 * w + 400) + 204 * M ≤ (180 * cw + 604) * Q := by
      have : X * (180 * w + 400) = 180 * (X * w) + 400 * X := by ring
      linarith
    have h2 := Nat.mul_le_mul_left 3 h1
    have h3 : 100 * (X * w) ≤ 100 * cw * Q := by linarith
    have e2 : (3 * (180 * cw + 604) + 100 * cw) * Q =
        3 * ((180 * cw + 604) * Q) + 100 * cw * Q := by ring
    rw [e2]
    omega
  unfold cvBoxCost cvSynthCost
  rw [hMX]
  have hSX : X * (6 * w + 4 * S + 14) ≤ (6 * cw + 4 + 14) * Q := by
    have : X * (6 * w + 4 * S + 14) = 6 * (X * w) + 4 * (X * S) + 14 * X := by ring
    have hXS : X * S ≤ Q := Nat.mul_le_mul_left _ hS
    linarith
  have hcm : 3 * (X * (cmulCost Tm w + 6 * w + 8) + 6) ≤ 3 * (X * cmulCost Tm w) +
      (18 * cw + 42) * Q := by
    have : X * (cmulCost Tm w + 6 * w + 8) = X * cmulCost Tm w + 6 * (X * w) + 8 * X := by ring
    linarith
  have e3 : mtCvK cw * Q = (3 * (180 * cw + 604) + 100 * cw) * Q +
      mtCvKf cw * Q + (18 * cw + 42) * Q + 16 * cw * Q + 16 * Q + (6 * cw + 4 + 14) * Q +
        4 * Q + 2 * cw * Q + 2 * Q := by unfold mtCvK; ring
  rw [e3]
  have h16 : 16 * (X * w) ≤ 16 * cw * Q := by linarith
  have h2w : 2 * (X * w) ≤ 2 * cw * Q := by linarith
  linarith

/-! ### The packed ring product -/

/-- The packed ring product on `N = wOf p l w · 2^l` bits, `2^l = r`, against
`r p grLogLog (r p)`. -/
theorem mt_cv_ring_le {cw p l w : ℕ} (hp : 1 ≤ p) (hl : l ≤ p) (hw : w ≤ cw * p) :
    (rpRingBound (wOf p l w * 2 ^ l) : ℝ) ≤
      (4 * (costC cA cB cC0 : ℝ) + 261000) * (grRingConst (6 + 4 * cw) *
        ((2 ^ l : ℕ) * (p : ℝ)) * grLogLog ((2 ^ l : ℕ) * (p : ℝ))) := by
  have hV := mt_cv_wOf_le p l w hp
  have hN : wOf p l w * 2 ^ l ≤ (6 + 4 * cw) * (2 ^ l * p) := by
    have : wOf p l w ≤ (6 + 4 * cw) * p := by linarith
    calc wOf p l w * 2 ^ l ≤ (6 + 4 * cw) * p * 2 ^ l := Nat.mul_le_mul_right _ this
      _ = (6 + 4 * cw) * (2 ^ l * p) := by ring
  have hN1 : 1 ≤ wOf p l w * 2 ^ l := by
    have : 1 ≤ wOf p l w := by unfold wOf; exact Nat.one_le_two_pow
    exact Nat.mul_le_mul this Nat.one_le_two_pow
  have hX : (1 : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) * (p : ℝ) := by
    have : 1 ≤ 2 ^ l * p := Nat.mul_le_mul Nat.one_le_two_pow hp
    exact_mod_cast this
  have hNr : ((wOf p l w * 2 ^ l : ℕ) : ℝ) ≤ ((6 + 4 * cw : ℕ) : ℝ) * (((2 ^ l : ℕ) : ℝ) * p) := by
    exact_mod_cast hN
  have h := gr_ringBound_le (c := (costC cA cB cC0 : ℝ)) (Nat.cast_nonneg _)
    (show 1 ≤ 6 + 4 * cw by omega) hX hN1 hNr
  unfold rpRingBound
  simp only [bitlen]
  push_cast
  push_cast at h
  linarith

/-! ### The pipeline -/

/-- The constant of `mt_cv_box_le`. -/
noncomputable def mtCvC (Tm cw : ℕ) : ℝ :=
  3 * mtCM Tm cw + mtCvK cw +
    (3 : ℝ) * ((4 * (costC cA cB cC0 : ℝ) + 261000) * grRingConst (6 + 4 * cw))

/-- `S = Σ_{i < d-1} log₂ t_i ≤ logT`, from `2^S r = T`. -/
theorem mt_cv_S_le {n : ℕ} (h : Big n) : (List.ofFn (cvAx (t n))).sum ≤ logT n := by
  have e := cv_M_mul_r h
  have h1 : 2 ^ (List.ofFn (cvAx (t n))).sum ≤ 2 ^ logT n := by
    change cvM (cvAx (t n)) ≤ T n
    rw [← e]; exact Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

/-- **The convolution box against its terms** (transforms excluded): eventually, for
`p + 2 ≤ w ≤ cw p`, `cvBoxCost ≤ mtCvC Tm cw (T M(p) + T p grLogLog (r p))`. -/
theorem mt_cv_box_le (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, p n + 2 ≤ w → w ≤ cw * p n →
      (cvBoxCost Tm (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) 0 0 : ℝ) ≤
        mtCvC Tm cw * ((T n : ℝ) * totMp n + (T n : ℝ) * p n * grLogLog ((r n : ℝ) * p n)) := by
  filter_upwards [eventually_big, mt_poly_r_le_T 6 1] with n h hpT w hw1 hw
  have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hpX : p n ≤ T n := by
    have : p n ≤ 6 * b n ^ 1 * r n := by
      rw [pow_one]; unfold p; exact Nat.le_mul_of_pos_right _ hr1
    exact this.trans hpT
  have hℓp := mt_ℓ_le_p h
  have hSp : (List.ofFn (cvAx (t n))).sum ≤ p n := by
    have := mt_cv_S_le h; have := mt_logT_le_b h; unfold p; omega
  have hMX : cvM (cvAx (t n)) * 2 ^ ℓ n = T n := cv_M_mul_r h
  have hA := mt_cv_arith (Tm := Tm) (cw := cw) hMX hp1 hℓp hSp hw hpX
  have hw1' : 1 ≤ w := by omega
  have hcm := mt_cmul_le Tm h hw1' hw
  have hring := mt_cv_ring_le (cw := cw) hp1 hℓp hw
  have hr : ((2 ^ ℓ n : ℕ) : ℝ) = r n := rfl
  rw [hr] at hring
  -- `M r p = T p`
  have hMr : ((cvM (cvAx (t n)) : ℕ) : ℝ) * ((r n : ℝ) * p n) = (T n : ℝ) * p n := by
    have : ((cvM (cvAx (t n)) : ℕ) : ℝ) * (r n : ℝ) = (T n : ℝ) := by exact_mod_cast cv_M_mul_r h
    rw [← this]; ring
  set M := ((cvM (cvAx (t n)) : ℕ) : ℝ) with hMdef
  have hcast : (cvBoxCost Tm (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) 0 0 : ℝ) ≤
      3 * ((T n : ℝ) * (cmulCost Tm w : ℝ)) +
        (3 : ℝ) * (M * (rpRingBound (wOf (p n) (ℓ n) w * 2 ^ ℓ n) : ℝ)) +
        (mtCvK cw : ℝ) * ((T n : ℝ) * p n) := by
    rw [hMdef]; exact_mod_cast hA
  set G := grLogLog ((r n : ℝ) * p n) with hG
  set c := (4 * (costC cA cB cC0 : ℝ) + 261000) with hc
  set Rc := grRingConst (6 + 4 * cw) with hRc
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hring' : M * (rpRingBound (wOf (p n) (ℓ n) w * 2 ^ ℓ n) : ℝ) ≤
      c * Rc * ((T n : ℝ) * p n * G) := by
    calc M * (rpRingBound (wOf (p n) (ℓ n) w * 2 ^ ℓ n) : ℝ) ≤ M * (c * (Rc * ((r n : ℝ) * p n) * G)) :=
          mul_le_mul_of_nonneg_left hring hM0
      _ = c * Rc * ((M * ((r n : ℝ) * p n)) * G) := by ring
      _ = c * Rc * ((T n : ℝ) * p n * G) := by rw [hMr]
  have hTm0 : (0 : ℝ) ≤ (3 : ℝ) := by positivity
  have hring'' := mul_le_mul_of_nonneg_left hring' hTm0
  have hT0 : (0 : ℝ) ≤ T n := Nat.cast_nonneg _
  have hcm' : (T n : ℝ) * (cmulCost Tm w : ℝ) ≤ mtCM Tm cw * ((T n : ℝ) * totMp n) := by
    calc (T n : ℝ) * (cmulCost Tm w : ℝ) ≤ (T n : ℝ) * (mtCM Tm cw * totMp n) :=
          mul_le_mul_of_nonneg_left hcm hT0
      _ = mtCM Tm cw * ((T n : ℝ) * totMp n) := by ring
  have hTp := mt_Tp_le_Tmp h
  have hK0 : (0 : ℝ) ≤ mtCvK cw := Nat.cast_nonneg _
  have hTpK : (mtCvK cw : ℝ) * ((T n : ℝ) * p n) ≤ (mtCvK cw : ℝ) * ((T n : ℝ) * totMp n) :=
    mul_le_mul_of_nonneg_left hTp hK0
  have hG1 : 1 ≤ G := by
    apply gr_one_le_logLog
    have := mt_one_le_r n; have := mt_one_le_p h; nlinarith
  have hTpG : 0 ≤ (T n : ℝ) * p n * G := mul_nonneg (mt_Tp_nonneg n) (by linarith)
  have hTmp := mt_Tmp_nonneg n
  have hcR : 0 ≤ c * Rc := by
    have h1 : (0 : ℝ) ≤ c := by
      rw [hc]; exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)
    have h2 : 0 ≤ Rc := by
      rw [hRc]
      have := gr_ringConst_ge (A := 6 + 4 * cw) (by omega)
      have : (0 : ℝ) ≤ 12 * ((6 + 4 * cw : ℕ) : ℝ) := by positivity
      linarith
    exact mul_nonneg h1 h2
  have hCM := mt_CM_nonneg Tm cw
  have e : mtCvC Tm cw * ((T n : ℝ) * totMp n + (T n : ℝ) * p n * G) =
      3 * mtCM Tm cw * ((T n : ℝ) * totMp n) + (mtCvK cw : ℝ) * ((T n : ℝ) * totMp n) +
        (3 : ℝ) * (c * Rc * ((T n : ℝ) * p n * G)) +
        (3 * mtCM Tm cw * ((T n : ℝ) * p n * G) + (mtCvK cw : ℝ) * ((T n : ℝ) * p n * G) +
          (3 : ℝ) * (c * Rc) * ((T n : ℝ) * totMp n)) := by
    unfold mtCvC; ring
  have k1 : 0 ≤ 3 * mtCM Tm cw * ((T n : ℝ) * p n * G) := by positivity
  have k2 : 0 ≤ (mtCvK cw : ℝ) * ((T n : ℝ) * p n * G) := mul_nonneg hK0 hTpG
  have k3 : 0 ≤ (3 : ℝ) * (c * Rc) * ((T n : ℝ) * totMp n) :=
    mul_nonneg (mul_nonneg hTm0 hcR) hTmp
  rw [e]
  linarith

/-- `mt_cv_box_le` against `totConv + T M(p)`: the box without its transforms costs at most
`mtCvC Tm cw (totConv + T M(p))`. -/
theorem mt_cv_box_le_conv (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, p n + 2 ≤ w → w ≤ cw * p n →
      (cvBoxCost Tm (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) 0 0 : ℝ) ≤
        mtCvC Tm cw * (totConv n + (T n : ℝ) * totMp n) := by
  filter_upwards [mt_cv_box_le Tm cw, eventually_big] with n hn h w hw1 hw
  refine (hn w hw1 hw).trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hI := tot_conv_inner_nonneg h
    have hdK : (0 : ℝ) ≤ (d n : ℝ) * K n := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hpK : (0 : ℝ) ≤ (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hℓd : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ totLam' :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hTp := mt_Tp_nonneg n
    have e : totConv n = (T n : ℝ) * p n * ((d n : ℝ) * K n +
        (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) + (ℓ n : ℝ) * (d n : ℝ) ^ totLam') +
        (T n : ℝ) * p n * grLogLog ((r n : ℝ) * p n) := by unfold totConv; ring
    have hrest : 0 ≤ (T n : ℝ) * p n * ((d n : ℝ) * K n +
        (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) + (ℓ n : ℝ) * (d n : ℝ) ^ totLam') :=
      mul_nonneg hTp (by linarith)
    rw [e]
    linarith
  · unfold mtCvC
    have := mt_CM_nonneg Tm cw
    have hR : 0 ≤ grRingConst (6 + 4 * cw) := by
      have := gr_ringConst_ge (A := 6 + 4 * cw) (by omega)
      have : (0 : ℝ) ≤ 12 * ((6 + 4 * cw : ℕ) : ℝ) := by positivity
      linarith
    have hK : (0 : ℝ) ≤ mtCvK cw := Nat.cast_nonneg _
    have hc : (0 : ℝ) ≤ 4 * (costC cA cB cC0 : ℝ) + 261000 := by positivity
    have hTm : (0 : ℝ) ≤ (3 : ℝ) := by positivity
    have := mul_nonneg hTm (mul_nonneg hc hR)
    linarith

end IntegerMultBounds.MathlibTM2.Cost
