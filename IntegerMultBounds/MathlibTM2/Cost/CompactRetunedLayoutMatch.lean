module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLoopMatch
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransforms
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedDirectCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopCost

/-! Actual retuned round costs: compact bulk and explicit direct boundary rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node Filter Mult.SynthErr
noncomputable section

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
private theorem compactRetuned_one_le_K : ∀ᶠ n in atTop, 1≤Mult.CompactSizes.K n := by
  filter_upwards [eventually_big] with n h
  exact (compactRetuned_inst h).2.2.2.2.2.2.1
private theorem compactRetuned_K_le_b {n : ℕ} (h : Big n) : Mult.CompactSizes.K n≤b n := by
  obtain ⟨_,_,_,_,_,_,_,_,hK,_⟩ := compactRetuned_inst h
  exact hK
private theorem compactRetuned_lay_le_conv {n : ℕ} (h : Big n) :
    (T n:ℝ)*p n*((d n:ℝ)*Mult.CompactSizes.K n+(p n:ℝ)*(Mult.CompactSizes.K n:ℝ)^(Parameters.tau-1))≤CompactTotal.conv n := by
  have hg := gr_one_le_logLog (one_le_mul_of_one_le_of_one_le (mt_one_le_r n) (mt_one_le_p h))
  unfold CompactTotal.conv
  have hp : 0≤(ℓ n:ℝ)*(d n:ℝ)^CompactInterim.lam' := by positivity
  nlinarith [mt_Tp_nonneg n]

theorem compactRetuned_ml_counts {n : ℕ} {es : List ℕ} (H : LayHyp es (ℓ n) (Mult.CompactSizes.K n)) (hK1 : 1 ≤ Mult.CompactSizes.K n) (B : ℕ) :
    (layBits es (ℓ n) (Mult.CompactSizes.K n)).length ≤ es.length * (layB (ℓ n) (Mult.CompactSizes.K n) + 1) ∧
      (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).length ≤ es.length * layQ (ℓ n) (Mult.CompactSizes.K n) ∧
      layB (ℓ n) (Mult.CompactSizes.K n) + 1 ≤ Mult.CompactSizes.K n ∧ layQ (ℓ n) (Mult.CompactSizes.K n) * Mult.CompactSizes.K n ≤ ℓ n ∧ layQ (ℓ n) (Mult.CompactSizes.K n) ≤ ℓ n := by
  have hbK : layB (ℓ n) (Mult.CompactSizes.K n) + 1 ≤ Mult.CompactSizes.K n := H.b_lt
  have hq : layQ (ℓ n) (Mult.CompactSizes.K n) * Mult.CompactSizes.K n ≤ ℓ n := by
    unfold layQ
    exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have hqℓ : layQ (ℓ n) (Mult.CompactSizes.K n) ≤ ℓ n := by
    have : layQ (ℓ n) (Mult.CompactSizes.K n) ≤ layQ (ℓ n) (Mult.CompactSizes.K n) * Mult.CompactSizes.K n := Nat.le_mul_of_pos_right _ hK1
    omega
  obtain ⟨c1, c2⟩ := layMoves_counts (es := es) (ℓ := ℓ n) (K := Mult.CompactSizes.K n)
  rw [layPreMoves, layPreMovesK, List.length_map, List.length_range] at c1
  refine ⟨?_, ?_, hbK, hq, hqℓ⟩
  · rw [length_layBits]; exact c1
  · rw [length_layXcs]; omega


theorem compactRetuned_ml_writer_le (cw cW : ℕ) :
    ∀ᶠ n in atTop, ∀ (es : List ℕ) (B W : ℕ), LayHyp es (ℓ n) (Mult.CompactSizes.K n) → es.length ≤ d n →
      es.sum ≤ logT n → B ≤ cw * (b n ^ 2 * r n) → W ≤ cW * (b n ^ 2 * r n) →
      (ldgWriterCost W es.sum (ℓ n) (Mult.CompactSizes.K n) es.length B (layB (ℓ n) (Mult.CompactSizes.K n))
        (layBits es (ℓ n) (Mult.CompactSizes.K n)).length (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).length
        (ldxAtoms es.sum es.length (layQ (ℓ n) (Mult.CompactSizes.K n))) : ℝ) ≤ (T n : ℝ) * p n := by
  obtain ⟨cZ, hcZ⟩ : ∃ cZ, cZ = cW + cw + 2 := ⟨_, rfl⟩
  filter_upwards [eventually_big, compactRetuned_one_le_K, ml_small_le (555210 * cZ ^ 6) 12 6] with n h hK1
    hsmall
  intro es B W H hD hN hB hW
  have hb16 := h.sixteen_le_b
  have hNb : es.sum ≤ b n := hN.trans (mt_logT_le_b h)
  have hdb : d n ≤ b n := mt_d_le_b n
  have hℓb : ℓ n ≤ b n := mt_ℓ_le_b h
  have hKb : Mult.CompactSizes.K n ≤ b n := compactRetuned_K_le_b h
  obtain ⟨hlen1, hlenX, hbK, hq, hqℓ⟩ := compactRetuned_ml_counts H hK1 B
  apply hsmall
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = b n ^ 2 * r n := ⟨_, rfl⟩
  rw [← hQ] at hB hW
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = cZ * Q := ⟨_, rfl⟩
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hb2 : b n ≤ b n ^ 2 := Nat.le_self_pow two_ne_zero _
  have hbQ : b n ≤ Q := by rw [hQ]; exact hb2.trans (Nat.le_mul_of_pos_right _ hr1)
  have hbbQ : b n * b n ≤ Q := by rw [hQ, ← sq]; exact Nat.le_mul_of_pos_right _ hr1
  have hZe : Z = cW * Q + cw * Q + 2 * Q := by rw [hZ, hcZ]; ring
  have hQZ : Q ≤ Z := by rw [hZe]; omega
  have hbZ : b n ≤ Z := hbQ.trans hQZ
  have hbbZ : b n * b n ≤ Z := hbbQ.trans hQZ
  have hBZ : B ≤ Z := by rw [hZe]; omega
  have hWZ : W ≤ Z := by rw [hZe]; omega
  have hD' : es.length ≤ b n := hD.trans hdb
  have h1Z : (layBits es (ℓ n) (Mult.CompactSizes.K n)).length ≤ Z := by
    refine hlen1.trans (le_trans ?_ hbbZ)
    exact Nat.mul_le_mul hD' (hbK.trans hKb)
  have hXZ : (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).length ≤ Z := by
    refine hlenX.trans (le_trans ?_ hbbZ)
    exact Nat.mul_le_mul hD' (hqℓ.trans hℓb)
  have hZ1 : 1 ≤ Z := by omega
  have hm := mt_lay_writer_mono (W' := Z) (N' := Z) (ℓ' := Z) (K' := Z) (D' := Z) (B' := Z)
    (b' := Z) (len1' := Z) (lenX' := Z) (KX' := ldxAtoms Z Z Z) hWZ (hNb.trans hbZ)
    (hℓb.trans hbZ) (hKb.trans hbZ) (hD'.trans hbZ) hBZ
    (show layB (ℓ n) (Mult.CompactSizes.K n) ≤ Z by omega) h1Z hXZ
    (mt_lay_ldxAtoms_mono (hNb.trans hbZ) (hD'.trans hbZ) ((hqℓ.trans hℓb).trans hbZ))
  have hp := mt_lay_writer_poly hZ1
  have e : 555210 * Z ^ 6 = 555210 * cZ ^ 6 * b n ^ 12 * r n ^ 6 := by rw [hZ, hQ]; ring
  calc _ ≤ 555210 * Z ^ 6 := hm.trans hp
    _ = _ := e


theorem compactRetuned_ml_stage_le (Tm t₀ Ka cv : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (es : List ℕ) (B : ℕ) (rg : LayReg t₀ → Fin Tm)
      (xs : List LayXcD) (Wf : ℕ → Fin Tm → List (Fin (prime + Ka + 4))),
      LayHyp es (ℓ n) (Mult.CompactSizes.K n) → es.length ≤ d n → es.sum ≤ logT n → 1 ≤ B →
      2 ^ es.sum * B ≤ cv * (T n * p n) →
      (∀ x ∈ xs, x.OK es.sum (Mult.CompactSizes.K n) B) → xs.length ≤ es.length * layQ (ℓ n) (Mult.CompactSizes.K n) →
      (∀ j < xs.length, ∑ i, (Wf (j + 1) (rg (.sw i))).length ≤
        swapT t₀ * (3 * (2 ^ es.sum * B) + 1)) →
      ((layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es (ℓ n) (Mult.CompactSizes.K n)).length +
        layXcLoopCost Tm t₀ es.sum (Mult.CompactSizes.K n) B rg Wf (fun _ => 60 * (es.sum + B + 2) + 75) xs :
          ℕ) : ℝ) ≤
        C * ((T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n + (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1))) := by
  obtain ⟨C2, hC2def⟩ : ∃ C2, C2 = mlC2 Tm t₀ cv := ⟨_, rfl⟩
  have hC2 : 0 ≤ C2 := hC2def ▸ ml_C2_nonneg Tm t₀ cv
  refine ⟨18 * cv + 130 + C2, by positivity, ?_⟩
  filter_upwards [eventually_big, compactRetuned_one_le_K] with n h hK1
  intro es B rg xs Wf H hD hN hB1 hV hOK hxl hbank
  -- sizes
  have hb16 := h.sixteen_le_b
  have hpb : p n = 6 * b n := rfl
  have hT2 : 2 ^ es.sum ≤ T n := by
    show 2 ^ es.sum ≤ 2 ^ logT n
    exact Nat.pow_le_pow_right (by norm_num) hN
  have hTpos : 1 ≤ T n := Nat.one_le_two_pow
  have hNb : es.sum ≤ b n := hN.trans (mt_logT_le_b h)
  obtain ⟨hlen1, -, hbK, hq, -⟩ := compactRetuned_ml_counts H hK1 B
  have h3dℓ : 3 * d n * ℓ n ≤ p n := h.ℓ_bounds.2
  -- one exchange
  obtain ⟨V, hVdef⟩ : ∃ V, V = 2 ^ es.sum * B := ⟨_, rfl⟩
  obtain ⟨Xr, hXr⟩ : ∃ x : ℝ, x = 3 * swapConst * ((Tm + 12 * swapT t₀ + 5 : ℕ) : ℝ) * (V : ℝ) *
      (Mult.CompactSizes.K n : ℝ) ^ Parameters.tau +
      ((6 * (swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hXs : ∀ j < xs.length,
      layXcStep Tm t₀ es.sum (Mult.CompactSizes.K n) B rg (Wf (j + 1)) (xs.getD j default) ≤ ⌈Xr⌉₊ := by
    intro j hj
    have hok : (xs.getD j default).OK es.sum (Mult.CompactSizes.K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact hOK _ (List.getElem_mem hj)
    have hs := layXcStep_le Tm t₀ es.sum (Mult.CompactSizes.K n) B rg (Wf (j + 1)) hok (by omega)
    have hbk := hbank j hj
    have hmax : max 1 (Mult.CompactSizes.K n) = Mult.CompactSizes.K n := max_eq_right hK1
    rw [hmax, ← hVdef] at hs
    rw [← hVdef] at hbk
    generalize (∑ i, (Wf (j + 1) (rg (.sw i))).length) = bk at hs hbk
    have hnat : 6 * bk + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 ≤
        6 * (swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 := by omega
    have hnat' : ((6 * bk + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) ≤
        ((6 * (swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hle : (layXcStep Tm t₀ es.sum (Mult.CompactSizes.K n) B rg (Wf (j + 1)) (xs.getD j default) : ℝ) ≤ Xr := by
      rw [hXr]
      linarith
    exact Nat.cast_le.1 (hle.trans (Nat.le_ceil Xr))
  have hst := ml_xcLoop_le Tm t₀ es.sum (Mult.CompactSizes.K n) B rg Wf (60 * (es.sum + B + 2) + 75) ⌈Xr⌉₊ xs hXs
  have hbt := ml_bitLoop_le es.sum B (14 * es.sum + 12) (layBits es (ℓ n) (Mult.CompactSizes.K n)).length
  -- the natural-number bound
  have hNp : es.sum ≤ p n := by rw [hpb]; omega
  have hA1 : (layBits es (ℓ n) (Mult.CompactSizes.K n)).length ≤ d n * Mult.CompactSizes.K n := hlen1.trans (Nat.mul_le_mul hD hbK)
  have hA2 : 14 * es.sum + 12 + layMvCost es.sum B + 5 ≤ (18 * cv + 121) * (T n * p n) := by
    unfold layMvCost
    have hp1 : 1 ≤ p n := by omega
    have h2N : 1 ≤ 2 ^ es.sum := Nat.one_le_two_pow
    have e1 : 2 ^ es.sum * (18 * B + 20 * es.sum + 36) =
        18 * (2 ^ es.sum * B) + 20 * (2 ^ es.sum * es.sum) + 36 * 2 ^ es.sum := by ring
    have e2 : 2 ^ es.sum * es.sum ≤ T n * p n := Nat.mul_le_mul hT2 hNp
    have e3 : 2 ^ es.sum ≤ T n * p n := hT2.trans (Nat.le_mul_of_pos_right _ hp1)
    have e4 : es.sum ≤ T n * p n := hNp.trans (Nat.le_mul_of_pos_left _ hTpos)
    have e5 : (18 * cv + 121) * (T n * p n) = 18 * (cv * (T n * p n)) + 121 * (T n * p n) := by
      ring
    rw [e1, e5]
    omega
  have hA := Nat.mul_le_mul hA1 hA2
  have hxs' : xs.length * (60 * (es.sum + B + 2) + 75 + ⌈Xr⌉₊ + 5) ≤
      es.length * layQ (ℓ n) (Mult.CompactSizes.K n) * (60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊) := by
    have : 60 * (es.sum + B + 2) + 75 + ⌈Xr⌉₊ + 5 = 60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊ := by
      ring
    rw [this]; exact Nat.mul_le_mul_right _ hxl
  have hN1 : layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es (ℓ n) (Mult.CompactSizes.K n)).length +
      layXcLoopCost Tm t₀ es.sum (Mult.CompactSizes.K n) B rg Wf (fun _ => 60 * (es.sum + B + 2) + 75) xs ≤
      d n * Mult.CompactSizes.K n * ((18 * cv + 121) * (T n * p n)) +
        es.length * layQ (ℓ n) (Mult.CompactSizes.K n) * (60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊) + 8 := by
    omega
  have hR1 := (Nat.cast_le (α := ℝ)).2 hN1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hR1
  -- real facts
  have hTr1 : (1 : ℝ) ≤ T n := mt_one_le_T n
  have hPr1 : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hKr1 : (1 : ℝ) ≤ Mult.CompactSizes.K n := by exact_mod_cast hK1
  have hDr1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hKr0 : (0 : ℝ) < Mult.CompactSizes.K n := by linarith only [hKr1]
  have hKτ : (1 : ℝ) ≤ (Mult.CompactSizes.K n : ℝ) ^ Parameters.tau := Real.one_le_rpow hKr1 tot_tau_nonneg
  have hKτ1 : (0 : ℝ) ≤ (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) := Real.rpow_nonneg hKr0.le _
  have hKτe : (Mult.CompactSizes.K n : ℝ) ^ Parameters.tau = (Mult.CompactSizes.K n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) := by
    rw [Real.rpow_sub_one hKr0.ne']
    field_simp
  have hqK : (layQ (ℓ n) (Mult.CompactSizes.K n) : ℝ) * Mult.CompactSizes.K n ≤ ℓ n := by exact_mod_cast hq
  have hDℓ : (es.length : ℝ) * ℓ n ≤ p n := by
    have h1 : es.length * ℓ n ≤ p n := by
      have h2 : es.length * ℓ n ≤ d n * ℓ n := Nat.mul_le_mul_right _ hD
      have h3 : 3 * d n * ℓ n = 3 * (d n * ℓ n) := by ring
      omega
    exact_mod_cast h1
  have hVr : (V : ℝ) ≤ cv * ((T n : ℝ) * p n) := by rw [hVdef]; exact_mod_cast hV
  have hBV : (B : ℝ) ≤ V := by
    rw [hVdef]
    exact_mod_cast Nat.le_mul_of_pos_left B Nat.one_le_two_pow
  have hNr : (es.sum : ℝ) ≤ p n := by exact_mod_cast hNp
  have hXr0 : 0 ≤ Xr := by
    rw [hXr]
    have := mt_swapConst_nonneg
    have : (0 : ℝ) ≤ (Mult.CompactSizes.K n : ℝ) ^ Parameters.tau := by linarith only [hKτ]
    positivity
  have hceil : (⌈Xr⌉₊ : ℝ) ≤ Xr + 1 := (Nat.ceil_lt_add_one hXr0).le
  have hXrb : 60 * ((es.sum : ℝ) + B + 2) + 80 + (⌈Xr⌉₊ : ℝ) ≤
      C2 * ((T n : ℝ) * p n * (Mult.CompactSizes.K n : ℝ) ^ Parameters.tau) := by
    rw [hC2def, mlC2]
    refine ml_xr_le hTr1 hPr1 hKτ hNr hBV hVr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) mt_swapConst_nonneg ?_
    calc (⌈Xr⌉₊ : ℝ) ≤ Xr + 1 := hceil
      _ = _ := by rw [hXr]; push_cast; ring
  have hTP0 : (0 : ℝ) ≤ (T n : ℝ) * p n := by positivity
  have hexch : (es.length : ℝ) * layQ (ℓ n) (Mult.CompactSizes.K n) * (60 * ((es.sum : ℝ) + B + 2) + 80 + ⌈Xr⌉₊) ≤
      C2 * ((T n : ℝ) * p n) * ((p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1)) := by
    refine mt_lay_exch_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqK hDℓ hKτe hKτ1 ?_
      (mul_nonneg hC2 hTP0)
    rw [mul_assoc]
    exact hXrb
  -- assembly
  have hDK : (1 : ℝ) ≤ (d n : ℝ) * Mult.CompactSizes.K n := by nlinarith only [hDr1, hKr1]
  have hX1 : (T n : ℝ) * p n ≤ (T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n) := by
    nlinarith only [hDK, hTP0]
  have hX2 : (0 : ℝ) ≤ (T n : ℝ) * p n * ((p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1)) :=
    mul_nonneg hTP0 (mul_nonneg (by linarith only [hPr1]) hKτ1)
  have hX10 : (0 : ℝ) ≤ (T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n) := by linarith only [hX1, hTP0]
  have hTP1 : (1 : ℝ) ≤ (T n : ℝ) * p n := by nlinarith only [hTr1, hPr1]
  have hcvY : (0 : ℝ) ≤ (cv : ℝ) *
      ((T n : ℝ) * p n * ((p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1))) :=
    mul_nonneg (Nat.cast_nonneg _) hX2
  have hC2X : (0 : ℝ) ≤ C2 * ((T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n)) := mul_nonneg hC2 hX10
  have h8 : (8 : ℝ) ≤ 8 * ((T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n)) := by
    linarith only [hX1, hTP1]
  rw [Nat.cast_add]
  linarith [hR1, hexch, hX1, h8, hC2X, hcvY, hX2]


theorem compactRetuned_ml_lay_cost_le_gen :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (E : ℕ) (v₀ : SynW → List (Fin (prime + mnKa + 4))),
      ((slyFwdCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n)
          (slyW (List.ofFn (cvAx (t n))).sum (2 ^ ℓ n * dsW n) (ℓ n) (d n - 1)) E v₀ +
        slyOppCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n)
          (slyW (List.ofFn (cvAx (t n))).sum (2 ^ ℓ n * dsW n) (ℓ n) (d n - 1)) E v₀ : ℕ) : ℝ) ≤
        C * CompactTotal.conv n := by
  obtain ⟨Cs, hCs0, hst⟩ := compactRetuned_ml_stage_le (nT SXReg) 6 mnKa 12
  refine ⟨2 * Cs + 16, ?_⟩
  filter_upwards [eventually_big, hst, compactRetuned_ml_writer_le 72 80, ml_aux_le, compactRetuned_one_le_K] with n h hst
    hwr haux hK1
  intro E v₀
  simp only [slyFwdCost, slyOppCost, slyStageCost, slyUnstageCost]
  generalize hes : List.ofFn (cvAx (t n)) = es
  generalize hB : 2 ^ ℓ n * dsW n = B
  have H : LayHyp es (ℓ n) (Mult.CompactSizes.K n) := hes ▸ compactDs_layHyp h
  have hsum : es.sum = logT n - ℓ n := hes ▸ ds_sum_cvAx h.1
  have hlen : es.length ≤ d n := by rw [← hes, List.length_ofFn]; omega
  have hℓ : ℓ n ≤ logT n := mt_ℓ_le_logT h
  have hN : es.sum ≤ logT n := by omega
  have hb16 := h.sixteen_le_b
  have hb1 : 1 ≤ b n := by omega
  have hNb : es.sum ≤ b n := hN.trans (mt_logT_le_b h)
  have hdb : d n ≤ b n := mt_d_le_b n
  have hℓb : ℓ n ≤ b n := mt_ℓ_le_b h
  have hKb : Mult.CompactSizes.K n ≤ b n := compactRetuned_K_le_b h
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hw3 : dsW n ≤ 12 * p n := by
    have := ds_dsW_le h.1; unfold p; omega
  have hw18 : dsW n ≤ 72 * b n := by unfold p at hw3; omega
  have hwpos : 1 ≤ dsW n := by have := ds_w_A n; omega
  have hB1 : 1 ≤ B := by
    rw [← hB]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  have hT2 : 2 ^ es.sum ≤ T n := by
    show 2 ^ es.sum ≤ 2 ^ logT n
    exact Nat.pow_le_pow_right (by norm_num) hN
  have hV : 2 ^ es.sum * B ≤ 12 * (T n * p n) := by
    rw [← hB, ← mul_assoc, ← pow_add, hsum, Nat.sub_add_cancel hℓ]
    show 2 ^ logT n * dsW n ≤ 12 * (2 ^ logT n * p n)
    calc 2 ^ logT n * dsW n ≤ 2 ^ logT n * (12 * p n) := Nat.mul_le_mul_left _ hw3
      _ = 12 * (2 ^ logT n * p n) := by ring
  have hBb : B ≤ 72 * (b n * r n) := by
    rw [← hB]
    show r n * dsW n ≤ _
    calc r n * dsW n ≤ r n * (72 * b n) := Nat.mul_le_mul_left _ hw18
      _ = 72 * (b n * r n) := by ring
  have hbr : b n * r n ≤ b n ^ 2 * r n := by
    rw [sq]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hb1)
  have hBb2 : B ≤ 72 * (b n ^ 2 * r n) := hBb.trans (Nat.mul_le_mul_left _ hbr)
  have hWb : slyW es.sum B (ℓ n) (d n - 1) ≤ 80 * (b n ^ 2 * r n) := by
    unfold slyW
    have h1 : es.sum * es.sum ≤ b n * b n := Nat.mul_le_mul hNb hNb
    have h2 : b n * b n ≤ b n ^ 2 * r n := by rw [sq]; exact Nat.le_mul_of_pos_right _ hr1
    have h3 : b n ≤ b n ^ 2 * r n := (Nat.le_mul_of_pos_left _ hb1).trans h2
    have h4 : b n * r n ≤ b n ^ 2 * r n := hbr
    omega
  obtain ⟨hlen1, hlenX, hbK, hq, hqℓ⟩ := compactRetuned_ml_counts H hK1 B
  have hxM : (layBits es (ℓ n) (Mult.CompactSizes.K n)).length ≤ b n ^ 2 := by
    rw [sq]
    exact hlen1.trans ((Nat.mul_le_mul hlen hbK).trans (Nat.mul_le_mul hdb hKb))
  have hxX : (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).length ≤ b n ^ 2 := by
    rw [sq]
    exact hlenX.trans ((Nat.mul_le_mul hlen hqℓ).trans (Nat.mul_le_mul hdb hℓb))
  -- the files
  obtain ⟨R, hR⟩ : ∃ R, R = slyR₂ mnKa (slyW es.sum B (ℓ n) (d n - 1)) E es.sum B v₀ :=
    ⟨_, rfl⟩
  rw [← hR]
  have hRsw : ∀ i, R (slyRg (.sw i)) = [] := fun i => by rw [hR]; exact ml_slyR₂_sw _ _ _ _ _ _
  have hA : 0 < B := hB1
  -- forward: the bank of exchange `j`
  have hbankF : ∀ j < (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).length,
      ∑ i, ((fun j => ldlW slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2)
        (ldgPost slyRg slyLr R es (ℓ n) (Mult.CompactSizes.K n) B (layXcs es (ℓ n) (Mult.CompactSizes.K n) B)) (layBits es (ℓ n) (Mult.CompactSizes.K n))
        (layXcs es (ℓ n) (Mult.CompactSizes.K n) B) ((layBits es (ℓ n) (Mult.CompactSizes.K n)).length + j)) (j + 1)
        (slyRg (.sw i))).length ≤ swapT 6 * (3 * (2 ^ es.sum * B) + 1) := by
    intro j hj
    have hok : ((layXcs es (ℓ n) (Mult.CompactSizes.K n) B).getD j default).OK es.sum (Mult.CompactSizes.K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact layXcs_OK B H _ (List.getElem_mem hj)
    have hbk := mt_lay_bank_le sly_regs.l sxHd_inj
      (ldgPost slyRg slyLr R es (ℓ n) (Mult.CompactSizes.K n) B (layXcs es (ℓ n) (Mult.CompactSizes.K n) B)) es.sum (es.sum + B + 2)
      (layBits es (ℓ n) (Mult.CompactSizes.K n)) (layXcs es (ℓ n) (Mult.CompactSizes.K n) B) j (3 * (2 ^ es.sum * B))
      (fun k => mt_lay_hs_le hok hA k)
    have hR0 : ∑ i, (ldgPost slyRg slyLr R es (ℓ n) (Mult.CompactSizes.K n) B (layXcs es (ℓ n) (Mult.CompactSizes.K n) B)
        (slyRg (.sw i))).length = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mt_lay_post_rg sly_regs.l R es (ℓ n) (Mult.CompactSizes.K n) B _ (by simp) (by simp), hRsw]
      rfl
    rw [hR0, zero_add] at hbk
    exact hbk
  have hF := hst es B slyRg (layXcs es (ℓ n) (Mult.CompactSizes.K n) B)
    (fun j => ldlW slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2)
      (ldgPost slyRg slyLr R es (ℓ n) (Mult.CompactSizes.K n) B (layXcs es (ℓ n) (Mult.CompactSizes.K n) B)) (layBits es (ℓ n) (Mult.CompactSizes.K n))
      (layXcs es (ℓ n) (Mult.CompactSizes.K n) B) ((layBits es (ℓ n) (Mult.CompactSizes.K n)).length + j))
    H hlen hN hB1 hV (layXcs_OK B H) hlenX hbankF
  -- opposite: the bank of exchange `j` of the reversed list
  have hbankO : ∀ j < (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).reverse.length,
      ∑ i, (ldlWU slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2)
        (slyRw' R es (ℓ n) (Mult.CompactSizes.K n) B) (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).reverse
        ((layBits es (ℓ n) (Mult.CompactSizes.K n)).map Prod.swap).reverse (j + 1)
        (slyRg (.sw i))).length ≤ swapT 6 * (3 * (2 ^ es.sum * B) + 1) := by
    intro j hj
    have hok : ((layXcs es (ℓ n) (Mult.CompactSizes.K n) B).reverse.getD j default).OK es.sum (Mult.CompactSizes.K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact layXcs_OK B H _ (List.mem_reverse.1 (List.getElem_mem hj))
    rw [ldlWU_X sxHd (prime + mnKa) es.sum (es.sum + B + 2) _ _ _ (by omega)]
    have hbk := ml_bankX_le sly_regs.l sxHd_inj (slyRw' R es (ℓ n) (Mult.CompactSizes.K n) B) (es.sum + B + 2)
      (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).reverse j (3 * (2 ^ es.sum * B)) (fun k => mt_lay_hs_le hok hA k)
    have hR0 : ∑ i, (slyRw' R es (ℓ n) (Mult.CompactSizes.K n) B (slyRg (.sw i))).length = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ml_slyRw'_sw, hRsw]
      rfl
    rw [hR0, zero_add] at hbk
    exact hbk
  have hO := hst es B slyRg (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).reverse
    (ldlWU slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2) (slyRw' R es (ℓ n) (Mult.CompactSizes.K n) B)
      (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).reverse ((layBits es (ℓ n) (Mult.CompactSizes.K n)).map Prod.swap).reverse)
    H hlen hN hB1 hV
    (fun x hx => layXcs_OK B H x (List.mem_reverse.1 hx))
    (by rw [List.length_reverse]; exact hlenX) hbankO
  -- the writer and the auxiliary passes
  have hWr := hwr es B _ H hlen hN hBb2 hWb
  have hAux := haux es.sum B _ (dsW n) (layBits es (ℓ n) (Mult.CompactSizes.K n)).length
    (layXcs es (ℓ n) (Mult.CompactSizes.K n) B).length hNb hT2 hBb hWb hw18 hxM hxX
  -- against `CompactTotal.conv`
  have hconv := compactRetuned_lay_le_conv h
  have hTr1 : (1 : ℝ) ≤ T n := mt_one_le_T n
  have hPr1 : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hKr1 : (1 : ℝ) ≤ Mult.CompactSizes.K n := by exact_mod_cast hK1
  have hDr1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hKτ1 : (0 : ℝ) ≤ (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) :=
    Real.rpow_nonneg (by linarith only [hKr1]) _
  have hTP0 : (0 : ℝ) ≤ (T n : ℝ) * p n := by positivity
  have hDK : (1 : ℝ) ≤ (d n : ℝ) * Mult.CompactSizes.K n := by nlinarith only [hDr1, hKr1]
  have hpK : (0 : ℝ) ≤ (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) := by positivity
  have hTpX : (T n : ℝ) * p n ≤ (T n : ℝ) * p n *
      ((d n : ℝ) * Mult.CompactSizes.K n + (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1)) := by
    nlinarith only [hDK, hpK, hTP0]
  have hCsX := mul_le_mul_of_nonneg_left hconv hCs0
  have hTpc : (T n : ℝ) * p n ≤ CompactTotal.conv n := hTpX.trans hconv
  push_cast at hF hO hAux ⊢
  linarith [hF, hO, hWr, hAux, hCsX, hTpc, hTP0]


end
end IntegerMultBounds.MathlibTM2.Cost
