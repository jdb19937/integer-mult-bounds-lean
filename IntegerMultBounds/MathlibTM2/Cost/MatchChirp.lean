module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Fast.LoadChirp
public import IntegerMultBounds.MathlibTM2.Fast.PointStage

/-!
# Cost matching: the chirp kernel and the entrywise box stages

The chirp kernel stage (`Fast/LoadChirp.ldChirpStage_exec`) and the entrywise stages of
`Fast/PointStage` against the terms `T M(p)` and `T p` of `Cost/Total.totBound`, at coefficient
width `w ≤ cw p` and table word size `W ≤ cW p` on a host of `Tm` stacks.

* `mt_ch_sum_take_le`: for lengths `t_k ≥ 2`, the prefix products sum to less than `2 ∏ t_k`.
* `mt_ch_chirpCost_le`: the kernel box built axis by axis costs at most the loads plus
  `8 V cmulCost` (`V = ∏ t_k`): the box of the first `j` axes has `∏_{k<j} t_k` entries, a
  geometric sum. (`cst_chirpCost_le` bounds every axis by the whole box, `4 d V cmulCost`,
  a factor `d` above `T M(p)`.)
* `mt_ch_axis_le`: one axis of the chirp table loader (`ldcAxisCost`, `ldc_axisCost_le`) is at
  most `100000 U³ r` steps for `p + g, w, W + 4 ≤ U`, `t_k, s_k ≤ r`: the tables are `o(T)`.
* `mt_ch_kernel_le`: the chirp kernel stage is `O(T M(p))`.
* `mt_ch_point_le` (`cst_point_runs`, F7 pointwise products), `mt_ch_chirpMul_le`
  (`cst_chirpMulKeep_runs`, chirp products and twists): `O(T M(p))`.
* `mt_ch_conj_le`, `mt_ch_conjKeep_le` (`cst_conj_runs`, `cst_conjKeep_runs`) and
  `mt_ch_scale_le` (`cst_scale_runs`, the exact scale by `2^γ`): `O(T p)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.Chirp

/-! ### The kernel box -/

/-- For lengths at least `2`, `∑_{j ≤ |ts|} ∏_{k < j} t_k + 1 ≤ 2 ∏ t_k`. -/
theorem mt_ch_sum_take_le :
    ∀ ts : List ℕ, (∀ x ∈ ts, 2 ≤ x) →
      ∑ j ∈ Finset.range (ts.length + 1), (ts.take j).prod + 1 ≤ 2 * ts.prod
  | [], _ => by simp
  | a :: ts, h => by
    have ha : 2 ≤ a := h a List.mem_cons_self
    have ih := mt_ch_sum_take_le ts fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.length_cons, Finset.sum_range_succ', List.prod_cons]
    simp only [List.take_succ_cons, List.prod_cons, List.take_zero, List.prod_nil]
    rw [← Finset.mul_sum]
    nlinarith

/-- **The kernel box, axis by axis**: for lengths `t_k ≥ 2`, the loads plus at most
`8 V cmulCost T w`, `V = ∏ t_k`. -/
theorem mt_ch_chirpCost_le (T w : ℕ) (ts : List ℕ) (bp : ℕ → ℕ) (hd : 1 ≤ ts.length)
    (hts : ∀ x ∈ ts, 2 ≤ x) :
    cstChirpCost T w ts bp ≤ ∑ k ∈ Finset.range ts.length, bp k + 8 * ts.prod * cmulCost T w := by
  have hts1 : ∀ x ∈ ts, 1 ≤ x := fun x hx => le_trans (by norm_num) (hts x hx)
  have hC := cst_cmulCost_ge T w
  have hV1 : 1 ≤ ts.prod := by
    have := cst_one_le_prod_take ts hts1 ts.length
    rwa [List.take_length] at this
  have hL0 : ts.getD 0 0 ≤ ts.prod := by
    have h := cst_prod_take_le ts hts1 1
    rw [cst_take_succ (by omega), List.take_zero, List.nil_append, List.prod_singleton] at h
    exact h
  -- each axis costs at most twice its prefix box
  have hstep : ∀ j ∈ Finset.range (ts.length - 1),
      bp (j + 1) + cstStepCost T w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3 ≤
        bp (j + 1) + (2 * cmulCost T w * (ts.take (j + 2)).prod + 3) := by
    intro j hj
    have hj' : j + 1 < ts.length := by have := Finset.mem_range.1 hj; omega
    have hL : 1 ≤ ts.getD (j + 1) 0 := by rw [cst_getD hj']; exact hts1 _ (List.getElem_mem hj')
    have h1 := cst_stepCost_le T w _ _ (cst_one_le_prod_take ts hts1 (j + 1)) hL
    have h2 : (ts.take (j + 1)).prod * ts.getD (j + 1) 0 = (ts.take (j + 2)).prod := by
      rw [cst_take_succ hj', List.prod_append, List.prod_singleton]
    rw [h2] at h1
    have : 2 * ((ts.take (j + 2)).prod) * cmulCost T w = 2 * cmulCost T w * (ts.take (j + 2)).prod := by
      ring
    omega
  -- the prefix boxes
  have hgeo : ∑ j ∈ Finset.range (ts.length - 1), (ts.take (j + 2)).prod + 1 ≤ 2 * ts.prod := by
    have h := mt_ch_sum_take_le ts hts
    have hsub : ∑ j ∈ Finset.range (ts.length - 1), (ts.take (j + 2)).prod ≤
        ∑ j ∈ Finset.range (ts.length + 1), (ts.take j).prod := by
      have e : ts.length + 1 = ts.length - 1 + 1 + 1 := by omega
      rw [e, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
    omega
  have hsum : ∑ j ∈ Finset.range (ts.length - 1),
      (bp (j + 1) + cstStepCost T w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3) ≤
        ∑ j ∈ Finset.range (ts.length - 1), bp (j + 1) +
          (2 * cmulCost T w * ∑ j ∈ Finset.range (ts.length - 1), (ts.take (j + 2)).prod +
            (ts.length - 1) * 3) := by
    refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, ← Finset.mul_sum]
  have hbp : ∑ k ∈ Finset.range ts.length, bp k =
      bp 0 + ∑ j ∈ Finset.range (ts.length - 1), bp (j + 1) := by
    obtain ⟨d', hd'⟩ : ∃ d', ts.length = d' + 1 := ⟨ts.length - 1, by omega⟩
    rw [hd', Finset.sum_range_succ', Nat.add_sub_cancel, Nat.add_comm]
  -- the number of axes is below the box size
  have hlen : ts.length ≤ 2 * ts.prod := by
    have h := mt_ch_sum_take_le ts hts
    have : ∑ j ∈ Finset.range (ts.length + 1), (ts.take j).prod ≥ ts.length + 1 := by
      have := Finset.card_nsmul_le_sum (Finset.range (ts.length + 1))
        (fun j => (ts.take j).prod) 1 (fun j _ => cst_one_le_prod_take ts hts1 j)
      simpa using this
    omega
  unfold cstChirpCost
  rw [hbp]
  have hLw : ts.getD 0 0 * w ≤ ts.prod * w := Nat.mul_le_mul_right _ hL0
  generalize ∑ j ∈ Finset.range (ts.length - 1),
    (bp (j + 1) + cstStepCost T w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3) = S at hsum ⊢
  generalize ∑ j ∈ Finset.range (ts.length - 1), bp (j + 1) = Sb at hsum ⊢
  generalize ∑ j ∈ Finset.range (ts.length - 1), (ts.take (j + 2)).prod = G at hsum hgeo
  generalize cmulCost T w = C at *
  generalize ts.prod = V at *
  generalize ts.getD 0 0 = L0 at *
  generalize ts.length = d at *
  have hVC : 128 * V ≤ V * C := by nlinarith
  have hVw : 128 * (V * w) ≤ V * C := by nlinarith
  have hVC1 : 128 ≤ V * C := by nlinarith
  have hG : 2 * C * G ≤ 4 * V * C := by
    have : 2 * C * G ≤ 2 * C * (2 * V) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hd3 : 5 * (d - 1) + 4 ≤ 10 * V + 4 := by omega
  nlinarith

/-! ### The table loader -/

/-- One axis of the chirp table loader: at most `100000 U³ r` steps for `p + g ≤ U`, `w ≤ U`,
`W + 4 ≤ U`, `N, s ≤ r`. -/
theorem mt_ch_axis_le {W w p g N s U r : ℕ} (hU : 1 ≤ U) (hpg : p + g ≤ U) (hw : w ≤ U)
    (hW : W + 4 ≤ U) (hN : N ≤ r) (hs : s ≤ r) (hr : 1 ≤ r) :
    ldcAxisCost W w p g N s ≤ 100000 * U ^ 3 * r := by
  have h := ldc_axisCost_le W w p g N s
  have hUr : U ≤ U * r := Nat.le_mul_of_pos_right U hr
  have a1 : N * (39 * (p + g) + 641) + 200 * (p + g) + 4 * w + 1503 ≤ 2400 * (U * r) := by
    have e1 : N * (39 * (p + g) + 641) ≤ r * (39 * U + 641) :=
      Nat.mul_le_mul hN (by omega)
    nlinarith
  have a2 : tblC W w ≤ 40 * U ^ 2 := by
    unfold tblC
    have : (W + 4) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hW 2
    nlinarith
  have a3 : (N * (39 * (p + g) + 641) + 200 * (p + g) + 4 * w + 1503) * tblC W w ≤
      2400 * (U * r) * (40 * U ^ 2) := Nat.mul_le_mul a1 a2
  have a4 : 2 * (N * w) ≤ 2 * (U * r) := by
    have : N * w ≤ r * U := Nat.mul_le_mul hN hw
    nlinarith
  have a5 : 2 * (p + g + N + s + w) * (4 * W + 10) ≤ 2 * (4 * (U * r)) * (14 * U) := by
    have b1 : p + g + N + s + w ≤ 4 * (U * r) := by
      have : r ≤ U * r := Nat.le_mul_of_pos_left r hU
      omega
    have b2 : 4 * W + 10 ≤ 14 * U := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 b1) b2
  have hU3 : U * r ≤ U ^ 3 * r := Nat.mul_le_mul_right _ (by nlinarith)
  have hU2 : U * U * r ≤ U ^ 3 * r := by
    have : U * U ≤ U ^ 3 := by nlinarith
    exact Nat.mul_le_mul_right _ this
  have e1 : 2400 * (U * r) * (40 * U ^ 2) = 96000 * (U ^ 3 * r) := by ring
  have e2 : 2 * (4 * (U * r)) * (14 * U) = 112 * (U * U * r) := by ring
  nlinarith

/-- The chirp guard is at most `d + 4`. -/
theorem mt_ch_guard_le (d : ℕ) : chirpGuard d ≤ d + 4 := by
  unfold chirpGuard
  have : Nat.clog 2 d ≤ d := by
    rw [Nat.clog_le_iff_le_pow one_lt_two]
    exact Nat.lt_two_pow_self.le
  omega

/-- The width bound of the loader: `U = (6 cw + 6 cW + 11) b`. -/
theorem mt_ch_U {n w W cw cW : ℕ} (h : Big n) (hw : w ≤ cw * p n) (hW : W ≤ cW * p n) :
    1 ≤ (6 * cw + 6 * cW + 11) * b n ∧ p n + chirpGuard (d n) ≤ (6 * cw + 6 * cW + 11) * b n ∧
      w ≤ (6 * cw + 6 * cW + 11) * b n ∧ W + 4 ≤ (6 * cw + 6 * cW + 11) * b n := by
  have hb := h.sixteen_le_b
  have hg := mt_ch_guard_le (d n)
  have hd := mt_d_le_b n
  have hp : p n = 6 * b n := rfl
  rw [hp] at hw hW
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **The chirp kernel stage** (`ldChirpStage_exec`): for `1 ≤ w ≤ cw p`, `W ≤ cW p`, the stage
costs eventually at most `C · T M(p)`. -/
theorem mt_ch_kernel_le (Tm cw cW : ℕ) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ w W : ℕ, 1 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (cstChirpCost Tm w (List.ofFn (t n)) (fun k =>
          ldcAxisCost W w (p n) (chirpGuard (d n)) ((List.ofFn (t n)).getD k 0)
            ((List.ofFn (s n)).getD k 0)) : ℝ) ≤ C * ((T n : ℝ) * totMp n) := by
  set c := 6 * cw + 6 * cW + 11 with hc
  refine ⟨1 + 8 * mtCM Tm cw, ?_⟩
  filter_upwards [eventually_big, mt_small_le (100000 * c ^ 3) 4] with n h hsm w W hw1 hw hW
  obtain ⟨hU1, hpg, hwU, hWU⟩ := mt_ch_U h hw hW
  set U := c * b n with hU
  have hlen : (List.ofFn (t n)).length = d n := List.length_ofFn
  have hts : ∀ x ∈ List.ofFn (t n), 2 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    have := h.two_le_ℓ
    rw [t_eq]
    unfold r
    split_ifs
    · rw [show ℓ n = ℓ n - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos (show 1 ≤ ℓ n - 1 by omega))
    · exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos (show 1 ≤ ℓ n by omega))
  have h1 := mt_ch_chirpCost_le Tm w (List.ofFn (t n)) (fun k =>
      ldcAxisCost W w (p n) (chirpGuard (d n)) ((List.ofFn (t n)).getD k 0)
        ((List.ofFn (s n)).getD k 0)) (by rw [hlen]; exact h.one_le_d) hts
  rw [hlen, List.prod_ofFn, mt_prod_t h] at h1
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hax : ∀ k ∈ Finset.range (d n), ldcAxisCost W w (p n) (chirpGuard (d n))
      ((List.ofFn (t n)).getD k 0) ((List.ofFn (s n)).getD k 0) ≤ 100000 * U ^ 3 * r n := by
    intro k hk
    have hk' : k < d n := Finset.mem_range.1 hk
    have hN : (List.ofFn (t n)).getD k 0 ≤ r n := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hk', mt_t_le_r]
    have hs : (List.ofFn (s n)).getD k 0 ≤ r n := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hk', dite_true, Option.getD_some]
      exact ((mt_s_lt_t h ⟨k, hk'⟩).le).trans (mt_t_le_r n _)
    exact mt_ch_axis_le hU1 hpg hwU hWU hN hs hr1
  have hsum : ∑ k ∈ Finset.range (d n), ldcAxisCost W w (p n) (chirpGuard (d n))
      ((List.ofFn (t n)).getD k 0) ((List.ofFn (s n)).getD k 0) ≤ 100000 * c ^ 3 * b n ^ 4 * r n := by
    refine (Finset.sum_le_sum hax).trans ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hd := mt_d_le_b n
    calc d n * (100000 * U ^ 3 * r n) ≤ b n * (100000 * U ^ 3 * r n) := Nat.mul_le_mul_right _ hd
      _ = 100000 * c ^ 3 * b n ^ 4 * r n := by rw [hU]; ring
  have h2 := hsm _ hsum
  have h3 := mt_cmul_le Tm h hw1 hw
  have hTp := mt_Tp_le_Tmp h
  have hT0 : (0 : ℝ) ≤ T n := Nat.cast_nonneg _
  have h1' : (cstChirpCost Tm w (List.ofFn (t n)) (fun k =>
      ldcAxisCost W w (p n) (chirpGuard (d n)) ((List.ofFn (t n)).getD k 0)
        ((List.ofFn (s n)).getD k 0)) : ℝ) ≤
      ((∑ k ∈ Finset.range (d n), ldcAxisCost W w (p n) (chirpGuard (d n))
        ((List.ofFn (t n)).getD k 0) ((List.ofFn (s n)).getD k 0) : ℕ) : ℝ) +
        8 * T n * (cmulCost Tm w : ℝ) := by exact_mod_cast h1
  have h4 : 8 * (T n : ℝ) * (cmulCost Tm w : ℝ) ≤ 8 * (T n : ℝ) * (mtCM Tm cw * totMp n) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith

/-! ### Entrywise stages on the box -/

/-- **Pointwise products** (`cst_point_runs` at the pipeline box): `O(T M(p))`. -/
theorem mt_ch_point_le (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, 1 ≤ w → w ≤ cw * p n →
      (((∏ i, t n i) * (cmulCost Tm w + 6 * w + 2) + 8 : ℕ) : ℝ) ≤
        (mtCM Tm cw + 6 * cw + 10) * ((T n : ℝ) * totMp n) := by
  filter_upwards [eventually_big] with n h w hw1 hw
  rw [mt_prod_t h]
  have h1 := mt_cmul_le Tm h hw1 hw
  have hm1 := mt_one_le_mp h
  have hpm := mt_p_le_mp h
  have hT1 := mt_one_le_T n
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hw
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwm : (w : ℝ) ≤ cw * totMp n := hw'.trans (mul_le_mul_of_nonneg_left hpm hcw)
  have hTm := mt_Tmp_nonneg n
  push_cast
  have e : (T n : ℝ) * ((cmulCost Tm w : ℝ) + 6 * w + 2) + 8 ≤
      (T n : ℝ) * (mtCM Tm cw * totMp n + 6 * (cw * totMp n) + 2 * totMp n) +
        8 * ((T n : ℝ) * totMp n) := by
    have : (cmulCost Tm w : ℝ) + 6 * w + 2 ≤
        mtCM Tm cw * totMp n + 6 * (cw * totMp n) + 2 * totMp n := by linarith
    have h8 : (8 : ℝ) ≤ 8 * ((T n : ℝ) * totMp n) := by nlinarith
    nlinarith
  nlinarith

/-- **Chirp products** (`cst_chirpMulKeep_runs` at the pipeline box, also the twists):
`O(T M(p))`. -/
theorem mt_ch_chirpMul_le (Tm cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, 1 ≤ w → w ≤ cw * p n →
      (((∏ i, t n i) * (cmulCost Tm w + 21 * w + 8) + 20 : ℕ) : ℝ) ≤
        (mtCM Tm cw + 21 * cw + 28) * ((T n : ℝ) * totMp n) := by
  filter_upwards [eventually_big] with n h w hw1 hw
  rw [mt_prod_t h]
  have h1 := mt_cmul_le Tm h hw1 hw
  have hm1 := mt_one_le_mp h
  have hpm := mt_p_le_mp h
  have hT1 := mt_one_le_T n
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hw
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwm : (w : ℝ) ≤ cw * totMp n := hw'.trans (mul_le_mul_of_nonneg_left hpm hcw)
  have hTm := mt_Tmp_nonneg n
  push_cast
  have e : (T n : ℝ) * ((cmulCost Tm w : ℝ) + 21 * w + 8) + 20 ≤
      (T n : ℝ) * (mtCM Tm cw * totMp n + 21 * (cw * totMp n) + 8 * totMp n) +
        20 * ((T n : ℝ) * totMp n) := by
    have : (cmulCost Tm w : ℝ) + 21 * w + 8 ≤
        mtCM Tm cw * totMp n + 21 * (cw * totMp n) + 8 * totMp n := by linarith
    have h8 : (20 : ℝ) ≤ 20 * ((T n : ℝ) * totMp n) := by nlinarith
    nlinarith
  nlinarith

/-- A stream of `L ≤ T` records at `a w + c` steps each plus `e`: `O(T p)`. -/
theorem mt_ch_lin_le {n L w cw a c e : ℕ} (h : Big n) (hL : L ≤ T n) (hw : w ≤ cw * p n) :
    ((L * (a * w + c) + e : ℕ) : ℝ) ≤ (a * cw + c + e) * ((T n : ℝ) * p n) := by
  have hp1 := mt_one_le_p h
  have hT1 := mt_one_le_T n
  have hL' : (L : ℝ) ≤ T n := by exact_mod_cast hL
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hw
  have hTp1 : (1 : ℝ) ≤ (T n : ℝ) * p n := by nlinarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have h1 : (L : ℝ) * (a * w + c) ≤ (T n : ℝ) * (a * (cw * p n) + c * p n) := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have : (a : ℝ) * w + c ≤ a * (cw * p n) + c * p n := by nlinarith
    have hx : (0 : ℝ) ≤ a * w + c := by positivity
    calc (L : ℝ) * (a * w + c) ≤ (T n : ℝ) * (a * w + c) := mul_le_mul_of_nonneg_right hL' hx
      _ ≤ _ := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have he : (e : ℝ) ≤ e * ((T n : ℝ) * p n) := by
    have : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    nlinarith
  push_cast
  nlinarith

/-- **Conjugation** (`cst_conj_runs` on the box stream): `O(T p)`. -/
theorem mt_ch_conj_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, w ≤ cw * p n →
      (((∏ i, t n i) * (5 * w + 6) + 2 : ℕ) : ℝ) ≤ (5 * cw + 8) * ((T n : ℝ) * p n) := by
  filter_upwards [eventually_big] with n h w hw
  have := mt_ch_lin_le (L := ∏ i, t n i) (a := 5) (c := 6) (e := 2) h (mt_prod_t h).le hw
  push_cast at this ⊢
  linarith

/-- **Conjugation keeping the source** (`cst_conjKeep_runs` on the box stream): `O(T p)`. -/
theorem mt_ch_conjKeep_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, w ≤ cw * p n →
      (((∏ i, t n i) * (13 * w + 6) + 10 : ℕ) : ℝ) ≤ (13 * cw + 16) * ((T n : ℝ) * p n) := by
  filter_upwards [eventually_big] with n h w hw
  have := mt_ch_lin_le (L := ∏ i, t n i) (a := 13) (c := 6) (e := 10) h (mt_prod_t h).le hw
  push_cast at this ⊢
  linarith

/-- **The exact scale by `2^γ`** (`cst_scale_runs` on the box stream): `O(T p)`, as `γ ≤ b/4`. -/
theorem mt_ch_scale_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, w ≤ cw * p n →
      (((∏ i, t n i) * (6 * w + 4 * gamma n + 14) + 4 : ℕ) : ℝ) ≤
        (6 * cw + 19) * ((T n : ℝ) * p n) := by
  filter_upwards [eventually_big] with n h w hw
  have hγ : 4 * gamma n ≤ p n := by have := h.four_gamma_le_b; unfold p; omega
  have hw' : 6 * w + 4 * gamma n ≤ (6 * cw + 1) * p n := by nlinarith
  have := mt_ch_lin_le (L := ∏ i, t n i) (w := 6 * w + 4 * gamma n) (cw := 6 * cw + 1) (a := 1)
    (c := 14) (e := 4) h (mt_prod_t h).le hw'
  push_cast at this ⊢
  linarith

end IntegerMultBounds.MathlibTM2.Cost
