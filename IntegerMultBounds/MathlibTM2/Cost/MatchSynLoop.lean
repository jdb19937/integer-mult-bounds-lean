module

public import IntegerMultBounds.MathlibTM2.Cost.MatchSynPipe
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynTop
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynPcs

/-!
# Cost matching: the round loops of the synthetic transforms

The loops `synLoopFCost`, `synLoopOCost` (`Fast/SynFwd.lean`) of the computed synthetic
transforms at the pipeline parameters — axes `es = List.ofFn (cvAx (t n))` (`|es| = d - 1`,
`Σ es = log₂ T - ℓ`), `ℓ = l = ℓ n`, `K = K n`, directions `Cost.brDirs`, `A = nRounds ≤ ℓ`
rounds, coefficients of `w = dsW n ≤ 3p` symbols, parking cost `stk ≤ C_s (r + (b + 1)^k)` — cost at
most a constant times `totConv n` (`mr_loop_cost_le`). Per round `h` (`mr_round_le`):

* the layer of a chunk round (`mr_chunk_layer_le`) is `topCost` with the `q₀ ≤ 46 (1 + log_m d)`
  top kernels and the pieces of the base-`m` digits of `D' = D - q₀` on `R₂ < 2^(a'+1)` rows:
  the linear stages and kernels cost `C (q₀ + 1 + |pcs|) 2^N r w'` (`mrT_topCost_le`), the pieces
  `C d^{λ'} R₂ 2^(N - a') r w'` (`mrP_pieces_le`), together `C T p d^{λ'}` since `2^N r = T`,
  `w' ≤ (G + m + 6) p` (`mrO_synW2_le`, `d^6 ≤ b`) and `1 + log_m d ≤ C d^{λ'}`;
* the layer of a top or low round (`mr_prefix_layer_le`) has `D ≤ d` top kernels and no pieces:
  `C T p d`; there are at most `b + 1 ≤ K` such rounds (`mr_rounds_split`);
* the records, rest states, parking and twiddles (`mr_over_le`): `C T p + 2 stk + 2`
  (`mrO_step_le` with `Z^8 2^N ≤ 24^8 T` from `b^8 ≤ r`).

Summing over `A ≤ ℓ` rounds: `T p (ℓ d^{λ'} + d K) + ℓ (T p + stk) + ℓ² ≤ C totConv`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Machine
  IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.Main

/-! ### The pipeline instance -/

/-- `F + 1 ≤ m^5` for the fixed directions. -/
theorem mr_F_le : factorCount (program Cost.brDirs) + 1 ≤ m ^ 5 := by
  have := br_factorCount_le
  have h : m ^ 5 = 931322574615478515625 := by norm_num [m]
  omega

/-- The parameters of the pipeline instance at a large `n`. -/
theorem mr_inst {n : ℕ} (h : Big n) :
    LayHyp (List.ofFn (cvAx (t n))) (ℓ n) (K n) ∧
      (List.ofFn (cvAx (t n))).sum = logT n - ℓ n ∧
      (List.ofFn (cvAx (t n))).length = d n - 1 ∧
      (List.ofFn (cvAx (t n))).sum ≤ b n ∧
      2 ^ (List.ofFn (cvAx (t n))).sum * r n = T n ∧
      nRounds (cvAx (t n)) ≤ ℓ n ∧ 1 ≤ K n ∧ ℓ n ≤ b n ∧ K n ≤ b n ∧ d n ≤ b n ∧ 16 ≤ b n ∧
      16 ≤ d n ∧ dsW n ≤ 18 * b n := by
  have H := mn_layHyp h
  have hs := ds_sum_cvAx h.1
  obtain ⟨hT, -⟩ := mt_T_split h
  have hw := ds_dsW_le h.1
  refine ⟨H, hs, ds_length_cvAx n, ?_, by rw [hs]; exact hT.symm, nRounds_le H, H.K_pos,
    mt_ℓ_le_b h, mt_K_le_b n, mt_d_le_b n, h.sixteen_le_b, h.2, ?_⟩
  · rw [hs]; have := mt_logT_le_b h; omega
  · have := h.sixteen_le_b; omega

/-- The working width of every round is at most `(G + m + 6) p`. -/
theorem mr_w2_le {n : ℕ} (h : Big n) (hh : ℕ) :
    synW2 (List.ofFn (cvAx (t n))) (ℓ n) (K n) (gateCount (program Cost.brDirs))
      (factorCount (program Cost.brDirs)) (dsW n) hh ≤
      (gateCount (program Cost.brDirs) + m + 6) * p n := by
  obtain ⟨-, -, hlen, -, -, -, -, -, -, -, hb16, hd16, hw⟩ := mr_inst h
  have h1 := mrO_synW2_le (List.ofFn (cvAx (t n))) (ℓ n) (K n) (gateCount (program Cost.brDirs))
    (factorCount (program Cost.brDirs)) (dsW n) hh mr_F_le
  rw [hlen, show d n - 1 + 1 = d n by omega] at h1
  have h2 : d n ^ 6 ≤ b n := h.pow_le_b (by norm_num)
  have h3 : (gateCount (program Cost.brDirs) + m + 3) * d n ^ 6 ≤
      (gateCount (program Cost.brDirs) + m + 3) * b n := Nat.mul_le_mul_left _ h2
  unfold p
  generalize gateCount (program Cost.brDirs) = G at *
  generalize b n = B at *
  generalize d n ^ 6 = D6 at *
  generalize dsW n = w at *
  generalize synW2 _ _ _ _ _ _ _ = W at *
  nlinarith

/-- `24 b · 5 b ≤ p³`. -/
theorem mr_bb_le_p3 {n : ℕ} (hb : 16 ≤ b n) : 24 * b n * (5 * b n) ≤ p n ^ 3 := by
  unfold p
  generalize b n = B at hb ⊢
  have h1 : B * B ≤ B * B * B := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : 0 ≤ B * B * B := Nat.zero_le _
  nlinarith

/-- `T p ≤ totConv`, `T p · d K ≤ totConv`, `T p · ℓ d^{λ'} ≤ totConv`. -/
theorem mr_conv_ge {n : ℕ} (h : Big n) :
    (T n : ℝ) * p n ≤ totConv n ∧ (T n : ℝ) * p n * ((d n : ℝ) * K n) ≤ totConv n ∧
      (T n : ℝ) * p n * ((ℓ n : ℝ) * (d n : ℝ) ^ totLam') ≤ totConv n := by
  have hTp := mt_Tp_nonneg n
  have hr : (1 : ℝ) ≤ r n := mt_one_le_r n
  have hp : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hll := gr_one_le_logLog (one_le_mul_of_one_le_of_one_le hr hp)
  have h1 : (0 : ℝ) ≤ (d n : ℝ) * K n := by positivity
  have h2 : (0 : ℝ) ≤ (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) := by positivity
  have h3 : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ totLam' := by positivity
  unfold totConv
  generalize (d n : ℝ) * K n = x at h1 ⊢
  generalize (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) = y at h2 ⊢
  generalize (ℓ n : ℝ) * (d n : ℝ) ^ totLam' = z at h3 ⊢
  generalize grLogLog ((r n : ℝ) * p n) = g at hll ⊢
  generalize (T n : ℝ) * p n = v at hTp ⊢
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-! ### The overheads of a round -/

/-- The records, rest states, parking and twiddles of a round cost `C T p + 2 stk + 2`. -/
theorem mr_over_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ h < ℓ n, ∀ stk : ℕ,
    ((synLayerStepCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n) h stk +
        synTwCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) h : ℕ) : ℝ) ≤
      (synLayerCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (dsW n) h : ℝ) +
        C * ((T n : ℝ) * p n) + 2 * stk + 2 := by
  obtain ⟨CA, hCA⟩ := mrO_step_le Cost.brDirs mr_F_le
  set G := gateCount (program Cost.brDirs)
  refine ⟨CA * (24 ^ 8 + G + m + 6), by positivity, ?_⟩
  filter_upwards [eventually_big, mr_b_pow_le_r 8] with n hbig hbr h hh stk
  obtain ⟨H, -, hlen, hN, hT, -, -, hℓ, hK, hd, hb16, -, hw⟩ := mr_inst hbig
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  have h1 := hCA (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n) h stk H hh hw1
  have hw2 := mr_w2_le hbig h
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  generalize hWe : synW2 es (ℓ n) (K n) G (factorCount (program Cost.brDirs)) (dsW n) h = W at *
  -- `Z ≤ 24 b`
  have hZ : mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ≤ 24 * b n := by
    unfold mrZ; rw [hlen]; omega
  have hZ8 : mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ^ 8 ≤ 24 ^ 8 * r n := by
    calc mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ^ 8 ≤ (24 * b n) ^ 8 := Nat.pow_le_pow_left hZ 8
      _ = 24 ^ 8 * b n ^ 8 := by ring
      _ ≤ 24 ^ 8 * r n := Nat.mul_le_mul_left _ hbr
  have hA : mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum ≤ 24 ^ 8 * T n := by
    calc mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum ≤ 24 ^ 8 * r n * 2 ^ es.sum :=
          Nat.mul_le_mul_right _ hZ8
      _ = 24 ^ 8 * (2 ^ es.sum * r n) := by ring
      _ = 24 ^ 8 * T n := by rw [hT]
  have hB : 2 ^ es.sum * (2 ^ ℓ n * W) ≤ T n * ((G + m + 6) * p n) := by
    calc 2 ^ es.sum * (2 ^ ℓ n * W) = (2 ^ es.sum * r n) * W := by unfold r; ring
      _ = T n * W := by rw [hT]
      _ ≤ T n * ((G + m + 6) * p n) := Nat.mul_le_mul_left _ hw2
  have hp1 : 1 ≤ p n := by unfold p; omega
  have hTp : T n ≤ T n * p n := Nat.le_mul_of_pos_right _ hp1
  have h2 : CA * (mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum +
      2 ^ es.sum * (2 ^ ℓ n * W)) ≤ CA * (24 ^ 8 + G + m + 6) * (T n * p n) := by
    have : mrZ es (ℓ n) (K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum + 2 ^ es.sum * (2 ^ ℓ n * W) ≤
        (24 ^ 8 + G + m + 6) * (T n * p n) := by nlinarith
    calc _ ≤ CA * ((24 ^ 8 + G + m + 6) * (T n * p n)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have h3 : synLayerStepCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) h stk +
      synTwCost es (ℓ n) (dsW n) h ≤
      synLayerCost Cost.brDirs es (ℓ n) (K n) (ℓ n) (dsW n) h +
        CA * (24 ^ 8 + G + m + 6) * (T n * p n) + 2 * stk + 2 := by omega
  exact_mod_cast h3

/-! ### The layer of a round -/

/-- The layer of a chunk round costs `C T p d^{λ'}`. -/
theorem mr_chunk_layer_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ h, synChunk (ℓ n) (K n) h →
    (synLayerCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (dsW n) h : ℝ) ≤
      C * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam' := by
  obtain ⟨CB, hCB⟩ := mrT_topCost_le Cost.brDirs
  obtain ⟨CP, hCP0, hCP⟩ := mrP_pieces_le (nT SXReg) Cost.brDirs mrP_logb_branching
  obtain ⟨CL, hCL0, hCL⟩ := mrP_one_add_logb_le
  refine ⟨(48 * CB * CL + 2 * CP) * (gateCount (program Cost.brDirs) + m + 6), by positivity, ?_⟩
  filter_upwards [eventually_big, mr_b_pow_le_r 2, mr_p_pow_le_two_pow_K 3] with n hbig hbr hpK
    h hc
  obtain ⟨H, -, hlen, hN, hT, -, hK1, hℓ, hK, hd, hb16, hd16, hw⟩ := mr_inst hbig
  obtain ⟨hKh, hRh, hAR, hAc, hQ, hDp, hAT, hfit, hfit2, hR2, hR2g, hR2l, hpcs, hER⟩ :=
    mr_chunk_facts H hc
  have hw2 := mr_w2_le hbig h
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  have hwW : dsW n ≤ synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h := mrO_le_synW2 _ _ _ _ _ _ _
  have hsW : synS es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h ≤ synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h :=
    mrO_synS_le_synW2 _ _ _ _ _ _ _
  have hDW : es.length ≤ synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h := mrO_length_le_synW2 _ _ _ _ _ _ _
  have hW : synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h =
      dsW n + synS es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h + es.length := rfl
  generalize hWe : synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h = W at *
  have hW1 : 1 ≤ W := by
    have : 1 ≤ dsW n := by unfold dsW; omega
    omega
  have hD1 : 1 ≤ es.length := by rw [hlen]; omega
  have hsplit := synK_mul_split es (K n)
  have hD'le : synDpp es ≤ es.length := Nat.sub_le _ _
  have hr1 : 1 ≤ 2 ^ ℓ n := Nat.one_le_two_pow
  have hNrW : es.sum ≤ 2 ^ ℓ n * W := by
    have : b n ≤ b n ^ 2 := Nat.le_self_pow (by norm_num) _
    have : b n ≤ 2 ^ ℓ n := by unfold r at hbr; omega
    calc es.sum ≤ 2 ^ ℓ n := by omega
      _ ≤ 2 ^ ℓ n * W := Nat.le_mul_of_pos_right _ hW1
  -- the piece conditions
  have hna : es.sum - synAc es (ℓ n) (K n) + synAc es (ℓ n) (K n) = es.sum :=
    Nat.sub_add_cancel hAc
  have hOk : ∀ pc ∈ synPcsR es (ℓ n) (K n) h,
      pc.Ok Cost.brDirs (synKh (ℓ n) (K n) h) (es.sum - synAR es (ℓ n) (K n) h) W
        (synR2 es (ℓ n) (K n) h) := by
    rw [hpcs, hKh, hAR, synR2_chunk es (ℓ n) (K n) hc]
    unfold synJp
    apply synPcs_ok
    · omega
    · rw [hW, synS, hER]; omega
  -- the `topCost` bound
  have hB := hCB (dsW n) W (synS es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h) (es.sum - synAR es (ℓ n) (K n) h)
    (synAR es (ℓ n) (K n) h) (2 ^ ℓ n) (synKh (ℓ n) (K n) h) (synRh (ℓ n) (K n) h)
    (synQ es (ℓ n) (K n) h) (synAT es (ℓ n) (K n) h) (synOS es (ℓ n) (K n) h)
    (synDp es (ℓ n) h) (synR2 es (ℓ n) (K n) h) (synPcsR es (ℓ n) (K n) h) hr1 hW1 hwW hsW
    (by rw [hKh]; exact hK1) (by rw [hKh]; exact hRh) (by rw [hAR, hR2]; exact hR2g)
    (by rw [hAR, hR2]; exact hR2l.le)
    (by rw [hAR, hna, hAT, hKh, hQ]; omega)
    (by rw [hAR, hna, hKh, hDp]; omega) (by rw [hAR, hna]; omega)
    (by rw [hAR, hna, hKh]; have := Nat.le_mul_of_pos_right (K n) hD1; omega)
    (by rw [hAR, hna]; exact hNrW) hOk
  rw [hAR, hna] at hB
  -- the pieces
  have hC := hCP (K n) (synRh (ℓ n) (K n) h) (synX es (ℓ n) (K n)) (synDpp es)
    (synOS es (ℓ n) (K n) h) (es.sum - synAc es (ℓ n) (K n)) (2 ^ ℓ n) W (es.sum + 1) (d n)
    hK1 hRh hr1 hW1 (by have : synDpp es ≤ d n := by unfold synDpp; omega
                        exact_mod_cast this)
    (by exact_mod_cast (show 1 ≤ d n by omega)) (gr_K_le_d_rpow n) (by omega)
    (by rw [hW, synS, hER]; omega)
    (by
      rw [← synR2_chunk es (ℓ n) (K n) hc, hR2]
      calc synR2c es (ℓ n) (K n) ≤ 2 * 2 ^ synAc es (ℓ n) (K n) := hR2l.le
        _ = 2 ^ (synAc es (ℓ n) (K n) + 1) := by ring
        _ ≤ 2 ^ (es.sum + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    (by
      have : 2 * (es.sum - synAc es (ℓ n) (K n) + (es.sum + 1) + 2) ≤ 10 * b n := by omega
      have : 10 * b n ≤ b n ^ 2 := by
        have : b n ^ 2 = b n * b n := by ring
        rw [this]; exact Nat.mul_le_mul_right _ (by omega)
      calc _ ≤ 10 * b n := by assumption
        _ ≤ 2 ^ ℓ n := by unfold r at hbr; omega
        _ ≤ 2 ^ ℓ n * W := Nat.le_mul_of_pos_right _ hW1)
    (by
      have h1 : 24 * (es.sum - synAc es (ℓ n) (K n)) * (es.sum - synAc es (ℓ n) (K n) +
          (es.sum + 1) + 2) ≤ 24 * b n * (5 * b n) := by
        apply Nat.mul_le_mul <;> omega
      have h2 : 24 * b n * (5 * b n) ≤ p n ^ 3 := mr_bb_le_p3 hb16
      omega)
  -- assemble
  have hlenP : (synPcsR es (ℓ n) (K n) h).length ≤ synJ (synDpp es) (synDpp es) := by
    rw [hpcs]; exact mrP_length_synPcs_le _ _ _ _ _ _
  have hlenP' : (synPcsR es (ℓ n) (K n) h).length ≤ synJ es.length es.length :=
    hlenP.trans (synJ_self_mono hD'le)
  have hJ : (synJ es.length es.length : ℝ) ≤ 1 + Real.logb m (d n) :=
    mrP_synJ_le (by rw [hlen]; exact_mod_cast (show d n - 1 ≤ d n by omega))
      (by exact_mod_cast (show 1 ≤ d n by omega))
  have hq : synQ es (ℓ n) (K n) h ≤ 46 * synJ es.length es.length := by
    rw [hQ, synQK_eq_min]
    have h1 : synJt es ≤ synJ es.length es.length := by unfold synJt; omega
    have := min_le_left (synCW * synJt es) es.length
    unfold synCW at this ⊢
    omega
  have hlog := hCL (d n) (by exact_mod_cast (show 1 ≤ d n by omega))
  have hlog0 : 0 ≤ Real.logb m (d n) :=
    Real.logb_nonneg (by norm_num [m]) (by exact_mod_cast (show 1 ≤ d n by omega))
  have hcnt : ((synQ es (ℓ n) (K n) h + 1 + (synPcsR es (ℓ n) (K n) h).length : ℕ) : ℝ) ≤
      48 * (CL * (d n : ℝ) ^ totLam') := by
    have h1 : ((synQ es (ℓ n) (K n) h + 1 + (synPcsR es (ℓ n) (K n) h).length : ℕ) : ℝ) ≤
        47 * (synJ es.length es.length : ℝ) + 1 := by exact_mod_cast (by omega)
    generalize CL * (d n : ℝ) ^ totLam' = X at *
    generalize Real.logb m (d n) = L at *
    linarith
  -- the volume: `R₂ 2^(N - a') ≤ 2 · 2^N`, `2^N 2^ℓ = T`
  have hvol : ((rowsAt (2 ^ synX es (ℓ n) (K n)) (synJ (synDpp es) (synDpp es) - 1) *
      2 ^ (es.sum - synAc es (ℓ n) (K n)) * (2 ^ ℓ n * W) : ℕ) : ℝ) ≤
      2 * ((T n : ℝ) * ((gateCount (program Cost.brDirs) + m + 6) * p n)) := by
    have h1 : rowsAt (2 ^ synX es (ℓ n) (K n)) (synJ (synDpp es) (synDpp es) - 1) *
        2 ^ (es.sum - synAc es (ℓ n) (K n)) * (2 ^ ℓ n * W) ≤
        2 * (T n * ((gateCount (program Cost.brDirs) + m + 6) * p n)) := by
      rw [← synR2_chunk es (ℓ n) (K n) hc, hR2]
      calc synR2c es (ℓ n) (K n) * 2 ^ (es.sum - synAc es (ℓ n) (K n)) * (2 ^ ℓ n * W)
          ≤ (2 * 2 ^ synAc es (ℓ n) (K n)) * 2 ^ (es.sum - synAc es (ℓ n) (K n)) *
            (2 ^ ℓ n * W) := by gcongr
        _ = 2 * ((2 ^ es.sum * r n) * W) := by
            rw [mul_assoc 2, ← pow_add, Nat.add_sub_cancel' hAc]; unfold r; ring
        _ = 2 * (T n * W) := by rw [hT]
        _ ≤ 2 * (T n * ((gateCount (program Cost.brDirs) + m + 6) * p n)) := by gcongr
    exact_mod_cast h1
  have hvol2 : ((2 ^ es.sum * (2 ^ ℓ n * W) : ℕ) : ℝ) ≤ (T n : ℝ) * ((gateCount (program Cost.brDirs) + m + 6) * p n) := by
    have h1 : 2 ^ es.sum * (2 ^ ℓ n * W) ≤ T n * ((gateCount (program Cost.brDirs) + m + 6) * p n) := by
      calc 2 ^ es.sum * (2 ^ ℓ n * W) = (2 ^ es.sum * r n) * W := by unfold r; ring
        _ = T n * W := by rw [hT]
        _ ≤ _ := by gcongr
    exact_mod_cast h1
  have hBr : (synLayerCost Cost.brDirs es (ℓ n) (K n) (ℓ n) (dsW n) h : ℝ) ≤
      CB * (((synQ es (ℓ n) (K n) h + 1 + (synPcsR es (ℓ n) (K n) h).length : ℕ) : ℝ) *
        ((2 ^ es.sum * (2 ^ ℓ n * W) : ℕ) : ℝ)) +
      (((synPcsR es (ℓ n) (K n) h).map fun pc =>
        layerCost (nT SXReg) Cost.brDirs pc.u (synKh (ℓ n) (K n) h) (synRh (ℓ n) (K n) h) pc.R₀
          (es.sum - synAR es (ℓ n) (K n) h) (2 ^ ℓ n) W pc.j pc.a₀).sum : ℝ) := by
    unfold synLayerCost
    rw [hAR, hWe]
    exact_mod_cast hB
  rw [hpcs, hKh, hAR] at hBr
  have hdl : 0 ≤ (d n : ℝ) ^ totLam' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsum : ((((synPcs (K n) (synX es (ℓ n) (K n)) (synDpp es) (synOS es (ℓ n) (K n) h)
      (synJp es) (synDpp es)).map fun pc =>
        layerCost (nT SXReg) Cost.brDirs pc.u (K n) (synRh (ℓ n) (K n) h) pc.R₀
          (es.sum - synAc es (ℓ n) (K n)) (2 ^ ℓ n) W pc.j pc.a₀).sum : ℕ) : ℝ) ≤
      CP * (d n : ℝ) ^ totLam' * (2 * ((T n : ℝ) * ((gateCount (program Cost.brDirs) + m + 6) * p n))) := by
    unfold synJp
    refine hC.trans ?_
    exact mul_le_mul_of_nonneg_left hvol (mul_nonneg hCP0 hdl)
  have hTp := mt_Tp_nonneg n
  have hcb : (0 : ℝ) ≤ CB := Nat.cast_nonneg _
  have hGm : (0 : ℝ) ≤ (gateCount (program Cost.brDirs) : ℝ) + m + 6 :=
    add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)
  have hcount0 : (0 : ℝ) ≤
      ((synQ es (ℓ n) (K n) h + 1 + (synPcsR es (ℓ n) (K n) h).length : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ ((2 ^ es.sum * (2 ^ ℓ n * W) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul : ((synQ es (ℓ n) (K n) h + 1 + (synPcsR es (ℓ n) (K n) h).length : ℕ) : ℝ) *
      ((2 ^ es.sum * (2 ^ ℓ n * W) : ℕ) : ℝ) ≤
      48 * (CL * (d n : ℝ) ^ totLam') * ((T n : ℝ) * ((gateCount (program Cost.brDirs) + m + 6) * p n)) :=
    mul_le_mul hcnt hvol2 hv0 (mul_nonneg (by norm_num) (mul_nonneg hCL0 hdl))
  have hTpG : (T n : ℝ) * ((gateCount (program Cost.brDirs) + m + 6) * p n) = (gateCount (program Cost.brDirs) + m + 6) * ((T n : ℝ) * p n) := by ring
  rw [hTpG] at hmul hsum
  have hmul' := mul_le_mul_of_nonneg_left hmul hcb
  rw [hpcs] at hmul'
  generalize (d n : ℝ) ^ totLam' = dl at hdl hmul' hsum ⊢
  generalize (T n : ℝ) * p n = v at hTp hmul' hsum ⊢
  generalize ((synQ es (ℓ n) (K n) h + 1 + (synPcs (K n) (synX es (ℓ n) (K n)) (synDpp es)
      (synOS es (ℓ n) (K n) h) (synJp es) (synDpp es)).length : ℕ) : ℝ) *
      ((2 ^ es.sum * (2 ^ ℓ n * W) : ℕ) : ℝ) = cv at hmul' hBr
  generalize ((gateCount (program Cost.brDirs) : ℝ) + m + 6) = gm at hGm hmul' hsum ⊢
  linarith only [hBr, hmul', hsum]

/-- The layer of a top or low round costs `C T p d`. -/
theorem mr_prefix_layer_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ h, ¬ synChunk (ℓ n) (K n) h →
    (synLayerCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (dsW n) h : ℝ) ≤
      C * ((T n : ℝ) * p n) * d n := by
  obtain ⟨CB, hCB⟩ := mrT_topCost_le Cost.brDirs
  refine ⟨CB * (gateCount (program Cost.brDirs) + m + 6), by positivity, ?_⟩
  filter_upwards [eventually_big, mr_b_pow_le_r 2] with n hbig hbr h hc
  obtain ⟨H, -, hlen, hN, hT, -, hK1, hℓ, hK, hd, hb16, hd16, hw⟩ := mr_inst hbig
  obtain ⟨hKh, hRh, hAR, hA, hQ, hDp, hAT, hfit, hR2, hpcs, -⟩ := mr_prefix_facts H hc
  have hw2 := mr_w2_le hbig h
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  have hwW : dsW n ≤ synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h := mrO_le_synW2 _ _ _ _ _ _ _
  have hsW : synS es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h ≤ synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h :=
    mrO_synS_le_synW2 _ _ _ _ _ _ _
  generalize hWe : synW2 es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h = W at *
  have hW1 : 1 ≤ W := by
    have : 1 ≤ dsW n := by unfold dsW; omega
    omega
  have hr1 : 1 ≤ 2 ^ ℓ n := Nat.one_le_two_pow
  have hNrW : es.sum ≤ 2 ^ ℓ n * W := by
    have : b n ≤ b n ^ 2 := Nat.le_self_pow (by norm_num) _
    have : b n ≤ 2 ^ ℓ n := by unfold r at hbr; omega
    calc es.sum ≤ 2 ^ ℓ n := by omega
      _ ≤ 2 ^ ℓ n * W := Nat.le_mul_of_pos_right _ hW1
  have hna : es.sum - synA es (ℓ n) (K n) + synA es (ℓ n) (K n) = es.sum :=
    Nat.sub_add_cancel hA
  have hN1 : 1 ≤ es.sum := by
    have := mr_length_le_sum H; rw [hlen] at this; omega
  have hB := hCB (dsW n) W (synS es (ℓ n) (K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h) (es.sum - synAR es (ℓ n) (K n) h)
    (synAR es (ℓ n) (K n) h) (2 ^ ℓ n) (synKh (ℓ n) (K n) h) (synRh (ℓ n) (K n) h)
    (synQ es (ℓ n) (K n) h) (synAT es (ℓ n) (K n) h) (synOS es (ℓ n) (K n) h)
    (synDp es (ℓ n) h) (synR2 es (ℓ n) (K n) h) (synPcsR es (ℓ n) (K n) h) hr1 hW1 hwW hsW
    (by rw [hKh]) (by rw [hKh, hRh]; norm_num) (by rw [hAR, hR2]) (by rw [hAR, hR2]; omega)
    (by rw [hAR, hna, hAT, hKh, hQ]; omega) (by rw [hAR, hna, hKh]; omega)
    (by rw [hAR, hna]; omega) (by rw [hAR, hna, hKh]; omega) (by rw [hAR, hna]; exact hNrW)
    (by rw [hpcs]; simp)
  rw [hAR, hna, hpcs] at hB
  simp only [List.map_nil, List.sum_nil, List.length_nil, add_zero] at hB
  have hcnt : synQ es (ℓ n) (K n) h + 1 ≤ d n := by rw [hQ, hlen] at *; omega
  have hv : 2 ^ es.sum * (2 ^ ℓ n * W) ≤ T n * ((gateCount (program Cost.brDirs) + m + 6) * p n) := by
    calc 2 ^ es.sum * (2 ^ ℓ n * W) = (2 ^ es.sum * r n) * W := by unfold r; ring
      _ = T n * W := by rw [hT]
      _ ≤ _ := by gcongr
  have h1 : synLayerCost Cost.brDirs es (ℓ n) (K n) (ℓ n) (dsW n) h ≤
      CB * (gateCount (program Cost.brDirs) + m + 6) * (T n * p n) * d n := by
    unfold synLayerCost
    rw [hAR, hWe, hpcs]
    calc _ ≤ CB * ((synQ es (ℓ n) (K n) h + 1) * (2 ^ es.sum * (2 ^ ℓ n * W))) := hB
      _ ≤ CB * (d n * (T n * ((gateCount (program Cost.brDirs) + m + 6) * p n))) := by gcongr
      _ = CB * (gateCount (program Cost.brDirs) + m + 6) * (T n * p n) * d n := by ring
  exact_mod_cast h1

/-! ### One round, and the loops -/

/-- One round at position `h < ℓ`: `C₁ T p d^{λ'} + C₃ T p + 2 stk + 2`, plus `C₂ T p d` when
the round is a top or low round. -/
theorem mr_round_le : ∃ C₁ C₂ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
    ∀ᶠ n in atTop, ∀ h < ℓ n, ∀ stk : ℕ,
      (synRoundCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n) h stk : ℝ) ≤
        (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam' + C₃ * ((T n : ℝ) * p n) + 2 * stk + 2) +
          if synChunk (ℓ n) (K n) h then 0 else C₂ * ((T n : ℝ) * p n) * d n := by
  obtain ⟨C₁, hC₁, h1⟩ := mr_chunk_layer_le
  obtain ⟨C₂, hC₂, h2⟩ := mr_prefix_layer_le
  obtain ⟨C₃, hC₃, h3⟩ := mr_over_le
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  filter_upwards [eventually_big, h1, h2, h3] with n hbig h1 h2 h3 h hh stk
  have e : (synRoundCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n) h stk :
      ℝ) = ((synLayerStepCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n) h
        stk + synTwCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) h : ℕ) : ℝ) := by
    rw [synRoundCost]
  rw [e]
  have hov := h3 h hh stk
  have hTp := mt_Tp_nonneg n
  have hdl : 0 ≤ (d n : ℝ) ^ totLam' := by positivity
  have hd0 : (0 : ℝ) ≤ d n := Nat.cast_nonneg _
  by_cases hc : synChunk (ℓ n) (K n) h
  · rw [if_pos hc]
    have := h1 h hc
    linarith
  · rw [if_neg hc]
    have := h2 h hc
    have : 0 ≤ C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam' := by positivity
    linarith

/-- **The round loops of the synthetic transforms against `totConv`.** For any fixed `C_s`, `k`
and parking cost `stk ≤ C_s (r + (b + 1)^k)`, the forward and opposite loops of
`A = nRounds (cvAx (t n))` rounds at the pipeline parameters cost at most `C · totConv n`. -/
theorem mr_loop_cost_le : ∀ C_s k : ℕ, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ stk ≤ C_s * (r n + (b n + 1) ^ k),
    ((synLoopFCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
        (nRounds (cvAx (t n))) stk +
      synLoopOCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n)
        (nRounds (cvAx (t n))) stk : ℕ) : ℝ) ≤ C * IntegerMultBounds.MathlibTM2.Cost.totConv n := by
  intro Cs k
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hr⟩ := mr_round_le
  refine ⟨2 * (C₁ + C₂ + C₃ + 3), ?_⟩
  filter_upwards [eventually_big, hr, mr_small_le (2 * (Cs + 1)) (k + 1), mr_small_le 52 2,
    ml_poly_r_le_T (4 * Cs) 1 1] with n hbig hr hsm1 hsm2 hpr stk hstk
  obtain ⟨H, -, hlen, hN, hT, hA, hK1, hℓ, hK, hd, hb16, hd16, hw⟩ := mr_inst hbig
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  generalize hAe : nRounds (cvAx (t n)) = A at *
  obtain ⟨hF, hO⟩ := mr_loops_le Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) A stk
  -- the sum of the rounds
  have hsum : ((∑ h ∈ Finset.range A, synRoundCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) h
      stk : ℕ) : ℝ) ≤
      A * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam' + C₃ * ((T n : ℝ) * p n) +
        2 * stk + 2) + (layB (ℓ n) (K n) + 1) * (C₂ * ((T n : ℝ) * p n) * d n) := by
    push_cast
    refine mr_rounds_split hA _ (mul_nonneg (mul_nonneg hC₂ (mt_Tp_nonneg n)) (Nat.cast_nonneg _))
      fun h hh => hr h (by omega) stk
  obtain ⟨hc1, hc2, hc3⟩ := mr_conv_ge hbig
  have hTp := mt_Tp_nonneg n
  have hdl : 1 ≤ (d n : ℝ) ^ totLam' :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d n by omega)) (by norm_num [totLam'])
  have hAℓ : (A : ℝ) ≤ ℓ n := by exact_mod_cast hA
  have hbK : (layB (ℓ n) (K n) : ℝ) + 1 ≤ K n := by exact_mod_cast H.b_lt
  have hd0 : (1 : ℝ) ≤ d n := by exact_mod_cast (show 1 ≤ d n by omega)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hℓ0 : (0 : ℝ) ≤ ℓ n := Nat.cast_nonneg _
  -- the parking and the loop bookkeeping are small
  have hpark : ((A * (2 * stk + 2) : ℕ) : ℝ) ≤ 2 * ((T n : ℝ) * p n) := by
    have h1 : A ≤ b n + 1 := by omega
    have h2 : 2 * stk + 2 ≤ 2 * Cs * r n + 2 * (Cs + 1) * (b n + 1) ^ k := by
      have : 1 ≤ (b n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have h3 : A * (2 * stk + 2) ≤ 4 * Cs * b n ^ 1 * r n ^ 1 + 2 * (Cs + 1) * (b n + 1) ^ (k + 1) := by
      calc A * (2 * stk + 2) ≤ (b n + 1) * (2 * Cs * r n + 2 * (Cs + 1) * (b n + 1) ^ k) :=
            Nat.mul_le_mul h1 h2
        _ = 2 * Cs * (b n + 1) * r n + 2 * (Cs + 1) * (b n + 1) ^ (k + 1) := by ring
        _ ≤ 4 * Cs * b n ^ 1 * r n ^ 1 + 2 * (Cs + 1) * (b n + 1) ^ (k + 1) := by
            have : 2 * Cs * (b n + 1) ≤ 4 * Cs * b n := by nlinarith
            have := Nat.mul_le_mul_right (r n) this
            simp only [pow_one]
            omega
    have h4 : ((4 * Cs * b n ^ 1 * r n ^ 1 : ℕ) : ℝ) ≤ (T n : ℝ) * p n := by
      have h5 : (4 * Cs * b n ^ 1 * r n ^ 1 : ℕ) ≤ T n := hpr
      have h6 : (T n : ℝ) ≤ T n * p n := by
        have := mt_one_le_p hbig
        have := mt_one_le_T n
        nlinarith
      have : ((4 * Cs * b n ^ 1 * r n ^ 1 : ℕ) : ℝ) ≤ T n := by exact_mod_cast h5
      linarith
    have h7 : ((2 * (Cs + 1) * (b n + 1) ^ (k + 1) : ℕ) : ℝ) ≤ (T n : ℝ) * p n := hsm1 _ le_rfl
    have h8 : ((A * (2 * stk + 2) : ℕ) : ℝ) ≤
        ((4 * Cs * b n ^ 1 * r n ^ 1 : ℕ) : ℝ) + ((2 * (Cs + 1) * (b n + 1) ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h3
    linarith
  have hbook : ((12 * A ^ 2 + 32 * A + 8 : ℕ) : ℝ) ≤ (T n : ℝ) * p n := by
    apply hsm2
    have h1 : A ≤ b n := by omega
    nlinarith
  -- the main terms
  have hmain1 : (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam') ≤ C₁ * totConv n := by
    calc (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam')
        ≤ (ℓ n : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam') :=
          mul_le_mul_of_nonneg_right hAℓ
            (mul_nonneg (mul_nonneg hC₁ hTp) (le_trans zero_le_one hdl))
      _ = C₁ * ((T n : ℝ) * p n * ((ℓ n : ℝ) * (d n : ℝ) ^ totLam')) := by ring
      _ ≤ C₁ * totConv n := by gcongr
  have hmain3 : (A : ℝ) * (C₃ * ((T n : ℝ) * p n)) ≤ C₃ * totConv n := by
    calc (A : ℝ) * (C₃ * ((T n : ℝ) * p n))
        ≤ (ℓ n : ℝ) * (C₃ * ((T n : ℝ) * p n)) := by gcongr
      _ ≤ (ℓ n : ℝ) * (C₃ * ((T n : ℝ) * p n)) * (d n : ℝ) ^ totLam' := by
          apply le_mul_of_one_le_right (by positivity) hdl
      _ = C₃ * ((T n : ℝ) * p n * ((ℓ n : ℝ) * (d n : ℝ) ^ totLam')) := by ring
      _ ≤ C₃ * totConv n := by gcongr
  have hmain2 : ((layB (ℓ n) (K n) : ℝ) + 1) * (C₂ * ((T n : ℝ) * p n) * d n) ≤
      C₂ * totConv n := by
    calc ((layB (ℓ n) (K n) : ℝ) + 1) * (C₂ * ((T n : ℝ) * p n) * d n)
        ≤ (K n : ℝ) * (C₂ * ((T n : ℝ) * p n) * d n) :=
          mul_le_mul_of_nonneg_right hbK (mul_nonneg (mul_nonneg hC₂ hTp) (Nat.cast_nonneg _))
      _ = C₂ * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) := by ring
      _ ≤ C₂ * totConv n := by gcongr
  have hpark' : (A : ℝ) * (2 * stk + 2) ≤ 2 * totConv n := by
    have : ((A * (2 * stk + 2) : ℕ) : ℝ) = (A : ℝ) * (2 * stk + 2) := by push_cast; ring
    linarith
  have hbook' : 12 * (A : ℝ) ^ 2 + 32 * A + 8 ≤ totConv n := by
    have : ((12 * A ^ 2 + 32 * A + 8 : ℕ) : ℝ) = 12 * (A : ℝ) ^ 2 + 32 * A + 8 := by push_cast; ring
    linarith
  have htot : ((synLoopFCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) A stk +
      synLoopOCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) A stk : ℕ) : ℝ) ≤
      2 * ((∑ h ∈ Finset.range A, synRoundCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) h
        stk : ℕ) : ℝ) + (12 * (A : ℝ) ^ 2 + 32 * A + 8) := by
    have : synLoopFCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) A stk +
        synLoopOCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) A stk ≤
        2 * (∑ h ∈ Finset.range A, synRoundCost Cost.brDirs es (ℓ n) (K n) (dsW n) (ℓ n) h stk) +
          (12 * A ^ 2 + 32 * A + 8) := by omega
    exact_mod_cast this
  have hA2 : (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam' +
      C₃ * ((T n : ℝ) * p n) + 2 * stk + 2) =
      (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ totLam') +
        (A : ℝ) * (C₃ * ((T n : ℝ) * p n)) + (A : ℝ) * (2 * stk + 2) := by ring
  rw [hA2] at hsum
  have hconv0 := tot_conv_nonneg hbig
  linarith

end IntegerMultBounds.MathlibTM2.Cost
