module

import IntegerMultBounds.MathlibTM2.Cost.MatchSynLoop
import IntegerMultBounds.MathlibTM2.Fast.CompactDistWires
public import IntegerMultBounds.MathlibTM2.Cost.CompactStageGrowth
import IntegerMultBounds.MathlibTM2.Cost.MatchSynTop
import IntegerMultBounds.MathlibTM2.Cost.MatchSynPipe
import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
public import IntegerMultBounds.MathlibTM2.Fast.DistWidth
public import IntegerMultBounds.MathlibTM2.Fast.SynRound
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.MathlibTM2.Cost.Branching

/-! Direct rounds and unchanged synthetic overhead at the actual larger chunk. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Machine
  IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.Main
noncomputable section
theorem compactRetuned_inst {n : ℕ} (h : Big n) :
    LayHyp (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) ∧
      (List.ofFn (cvAx (t n))).sum = logT n - ℓ n ∧
      (List.ofFn (cvAx (t n))).length = d n - 1 ∧
      (List.ofFn (cvAx (t n))).sum ≤ b n ∧
      2 ^ (List.ofFn (cvAx (t n))).sum * r n = T n ∧
      nRounds (cvAx (t n)) ≤ ℓ n ∧ 1 ≤ Mult.CompactSizes.K n ∧ ℓ n ≤ b n ∧ Mult.CompactSizes.K n ≤ b n ∧ d n ≤ b n ∧ 16 ≤ b n ∧
      16 ≤ d n ∧ dsW n ≤ 72 * b n := by
  have H := compactDs_layHyp h
  have hs := ds_sum_cvAx h.1
  obtain ⟨hT, -⟩ := mt_T_split h
  have hw := ds_dsW_le h.1
  refine ⟨H, hs, ds_length_cvAx n, ?_, by rw [hs]; exact hT.symm, nRounds_le H, H.K_pos,
    mt_ℓ_le_b h, ((Mult.CompactSizes.K_le_d n).trans (mt_d_le_b n)), mt_d_le_b n,
    h.sixteen_le_b, (by have := h.2; omega), ?_⟩
  · rw [hs]; have := mt_logT_le_b h; omega
  · have := h.sixteen_le_b; omega

/-- The working width of a direct round is at most `(G + m + 15) p`: direct rounds carry no
piece exponents, so the shift is at most `3 D/2 + 1`. -/
theorem compactRetuned_direct_w2_le {n : ℕ} (h : Big n) {hh : ℕ}
    (hc : ¬ synChunk (ℓ n) (Mult.CompactSizes.K n) hh) :
    synW2 (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs))
      (factorCount (program Cost.brDirs)) (dsW n) hh ≤
      (gateCount (program Cost.brDirs) + m + 15) * p n := by
  obtain ⟨-, -, hlen, -, -, -, -, -, -, hdb, hb16, -, hw⟩ := compactRetuned_inst h
  have hLg := mrO_synLg_le (List.ofFn (cvAx (t n))) (ℓ n)
  have hS : synS (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs))
      (factorCount (program Cost.brDirs)) hh ≤ 3 * (List.ofFn (cvAx (t n))).length + 1 := by
    have hDp : synDp (List.ofFn (cvAx (t n))) (ℓ n) hh ≤ (List.ofFn (cvAx (t n))).length := by
      unfold synDp; split_ifs <;> omega
    simp only [synS, synQ, synER, hc, ite_false]
    omega
  unfold synW2 p
  generalize gateCount (program Cost.brDirs) = G at *
  rw [hlen] at hS ⊢
  have h15 : 15 * (6 * b n) ≤ (G + m + 15) * (6 * b n) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem compactRetuned_conv_ge {n : ℕ} (h : Big n) :
    (T n : ℝ) * p n ≤ CompactTotal.conv n ∧ (T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n) ≤ CompactTotal.conv n ∧
      (T n : ℝ) * p n * ((ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam') ≤ CompactTotal.conv n := by
  have hTp := mt_Tp_nonneg n
  have hr : (1 : ℝ) ≤ r n := mt_one_le_r n
  have hp : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hll := gr_one_le_logLog (one_le_mul_of_one_le_of_one_le hr hp)
  have h1 : (0 : ℝ) ≤ (d n : ℝ) * Mult.CompactSizes.K n := by positivity
  have h2 : (0 : ℝ) ≤ (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) := by positivity
  have h3 : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam' := by positivity
  unfold CompactTotal.conv
  generalize (d n : ℝ) * Mult.CompactSizes.K n = x at h1 ⊢
  generalize (p n : ℝ) * (Mult.CompactSizes.K n : ℝ) ^ (Parameters.tau - 1) = y at h2 ⊢
  generalize (ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam' = z at h3 ⊢
  generalize grLogLog ((r n : ℝ) * p n) = g at hll ⊢
  generalize (T n : ℝ) * p n = v at hTp ⊢
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith


theorem compactRetuned_direct_over_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ h < ℓ n,
    ¬ synChunk (ℓ n) (Mult.CompactSizes.K n) h → ∀ stk : ℕ,
    ((synLayerStepCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) h stk +
        synTwCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) h : ℕ) : ℝ) ≤
      (synLayerCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n) h : ℝ) +
        C * ((T n : ℝ) * p n) + 2 * stk + 2 := by
  obtain ⟨CA, hCA⟩ := mrO_step_le Cost.brDirs mr_F_le
  set G := gateCount (program Cost.brDirs)
  refine ⟨CA * (80 ^ 8 + G + m + 15), by positivity, ?_⟩
  filter_upwards [eventually_big, mr_b_pow_le_r 8] with n hbig hbr h hh hc stk
  obtain ⟨H, -, hlen, hN, hT, -, -, hℓ, hK, hd, hb16, -, hw⟩ := compactRetuned_inst hbig
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  have h1 := hCA (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) h stk H hh hw1
  have hw2 := compactRetuned_direct_w2_le hbig hc
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  generalize hWe : synW2 es (ℓ n) (Mult.CompactSizes.K n) G (factorCount (program Cost.brDirs)) (dsW n) h = W at *
  -- `Z ≤ 24 b`
  have hZ : mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ≤ 80 * b n := by
    unfold mrZ; rw [hlen]; omega
  have hZ8 : mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 ≤ 80 ^ 8 * r n := by
    calc mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 ≤ (80 * b n) ^ 8 := Nat.pow_le_pow_left hZ 8
      _ = 80 ^ 8 * b n ^ 8 := by ring
      _ ≤ 80 ^ 8 * r n := Nat.mul_le_mul_left _ hbr
  have hA : mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum ≤ 80 ^ 8 * T n := by
    calc mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum ≤ 80 ^ 8 * r n * 2 ^ es.sum :=
          Nat.mul_le_mul_right _ hZ8
      _ = 80 ^ 8 * (2 ^ es.sum * r n) := by ring
      _ = 80 ^ 8 * T n := by rw [hT]
  have hB : 2 ^ es.sum * (2 ^ ℓ n * W) ≤ T n * ((G + m + 15) * p n) := by
    calc 2 ^ es.sum * (2 ^ ℓ n * W) = (2 ^ es.sum * r n) * W := by unfold r; ring
      _ = T n * W := by rw [hT]
      _ ≤ T n * ((G + m + 15) * p n) := Nat.mul_le_mul_left _ hw2
  have hp1 : 1 ≤ p n := by unfold p; omega
  have hTp : T n ≤ T n * p n := Nat.le_mul_of_pos_right _ hp1
  have h2 : CA * (mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum +
      2 ^ es.sum * (2 ^ ℓ n * W)) ≤ CA * (80 ^ 8 + G + m + 15) * (T n * p n) := by
    have : mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum + 2 ^ es.sum * (2 ^ ℓ n * W) ≤
        (80 ^ 8 + G + m + 15) * (T n * p n) := by nlinarith
    calc _ ≤ CA * ((80 ^ 8 + G + m + 15) * (T n * p n)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have h3 : synLayerStepCost Cost.brDirs es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) h stk +
      synTwCost es (ℓ n) (dsW n) h ≤
      synLayerCost Cost.brDirs es (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n) h +
        CA * (80 ^ 8 + G + m + 15) * (T n * p n) + 2 * stk + 2 := by omega
  exact_mod_cast h3


theorem compactRetuned_direct_layer_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ h, ¬ synChunk (ℓ n) (Mult.CompactSizes.K n) h →
    (synLayerCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n) h : ℝ) ≤
      C * ((T n : ℝ) * p n) * d n := by
  obtain ⟨CB, hCB⟩ := mrT_topCost_le Cost.brDirs
  refine ⟨CB * (gateCount (program Cost.brDirs) + m + 15), by positivity, ?_⟩
  filter_upwards [eventually_big, mr_b_pow_le_r 2] with n hbig hbr h hc
  obtain ⟨H, -, hlen, hN, hT, -, hK1, hℓ, hK, hd, hb16, hd16, hw⟩ := compactRetuned_inst hbig
  obtain ⟨hKh, hRh, hAR, hA, hQ, hDp, hAT, hfit, hR2, hpcs, -⟩ := mr_prefix_facts H hc
  have hw2 := compactRetuned_direct_w2_le hbig hc
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  have hwW : dsW n ≤ synW2 es (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h := mrO_le_synW2 _ _ _ _ _ _ _
  have hsW : synS es (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h ≤ synW2 es (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h :=
    mrO_synS_le_synW2 _ _ _ _ _ _ _
  generalize hWe : synW2 es (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (dsW n) h = W at *
  have hW1 : 1 ≤ W := by
    have : 1 ≤ dsW n := by unfold dsW; omega
    omega
  have hr1 : 1 ≤ 2 ^ ℓ n := Nat.one_le_two_pow
  have hNrW : es.sum ≤ 2 ^ ℓ n * W := by
    have : b n ≤ b n ^ 2 := Nat.le_self_pow (by norm_num) _
    have : b n ≤ 2 ^ ℓ n := by unfold r at hbr; omega
    calc es.sum ≤ 2 ^ ℓ n := by omega
      _ ≤ 2 ^ ℓ n * W := Nat.le_mul_of_pos_right _ hW1
  have hna : es.sum - synA es (ℓ n) (Mult.CompactSizes.K n) + synA es (ℓ n) (Mult.CompactSizes.K n) = es.sum :=
    Nat.sub_add_cancel hA
  have hN1 : 1 ≤ es.sum := by
    have := mr_length_le_sum H; rw [hlen] at this; omega
  have hB := hCB (dsW n) W (synS es (ℓ n) (Mult.CompactSizes.K n) (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h) (es.sum - synAR es (ℓ n) (Mult.CompactSizes.K n) h)
    (synAR es (ℓ n) (Mult.CompactSizes.K n) h) (2 ^ ℓ n) (synKh (ℓ n) (Mult.CompactSizes.K n) h) (synRh (ℓ n) (Mult.CompactSizes.K n) h)
    (synQ es (ℓ n) (Mult.CompactSizes.K n) h) (synAT es (ℓ n) (Mult.CompactSizes.K n) h) (synOS es (ℓ n) (Mult.CompactSizes.K n) h)
    (synDp es (ℓ n) h) (synR2 es (ℓ n) (Mult.CompactSizes.K n) h) (synPcsR es (ℓ n) (Mult.CompactSizes.K n) h) hr1 hW1 hwW hsW
    (by rw [hKh]) (by rw [hKh, hRh]; norm_num) (by rw [hAR, hR2]) (by rw [hAR, hR2]; omega)
    (by rw [hAR, hna, hAT, hKh, hQ]; omega) (by rw [hAR, hna, hKh]; omega)
    (by rw [hAR, hna]; omega) (by rw [hAR, hna, hKh]; omega) (by rw [hAR, hna]; exact hNrW)
    (by rw [hpcs]; simp)
  rw [hAR, hna, hpcs] at hB
  simp only [List.map_nil, List.sum_nil, List.length_nil, add_zero] at hB
  have hcnt : synQ es (ℓ n) (Mult.CompactSizes.K n) h + 1 ≤ d n := by rw [hQ, hlen] at *; omega
  have hv : 2 ^ es.sum * (2 ^ ℓ n * W) ≤ T n * ((gateCount (program Cost.brDirs) + m + 15) * p n) := by
    calc 2 ^ es.sum * (2 ^ ℓ n * W) = (2 ^ es.sum * r n) * W := by unfold r; ring
      _ = T n * W := by rw [hT]
      _ ≤ _ := by gcongr
  have h1 : synLayerCost Cost.brDirs es (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n) h ≤
      CB * (gateCount (program Cost.brDirs) + m + 15) * (T n * p n) * d n := by
    unfold synLayerCost
    rw [hAR, hWe, hpcs]
    calc _ ≤ CB * ((synQ es (ℓ n) (Mult.CompactSizes.K n) h + 1) * (2 ^ es.sum * (2 ^ ℓ n * W))) := hB
      _ ≤ CB * (d n * (T n * ((gateCount (program Cost.brDirs) + m + 15) * p n))) := by gcongr
      _ = CB * (gateCount (program Cost.brDirs) + m + 15) * (T n * p n) * d n := by ring
  exact_mod_cast h1


/-- The twiddle pass of every round costs `O(T p)`. -/
theorem compactRetuned_tw_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ h < ℓ n,
    (synTwCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) h : ℝ) ≤ C * ((T n : ℝ) * p n) := by
  refine ⟨500 * 80 ^ 8 + 720, by positivity, ?_⟩
  filter_upwards [eventually_big, mr_b_pow_le_r 8] with n hbig hbr h hh
  obtain ⟨H, -, hlen, hN, hT, -, -, hℓ, hK, hd, hb16, -, hw⟩ := compactRetuned_inst hbig
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  have hZ : mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ≤ 80 * b n := by
    unfold mrZ; rw [hlen]; omega
  have htw := mrO_twCost_le es (Z := mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n))
    (l := ℓ n) (w := dsW n) (h := h) (by unfold mrZ; omega) hw1 (by unfold mrZ; omega) (by unfold mrZ; omega)
    (by unfold mrZ; omega) (by unfold mrZ; omega) (by unfold mrZ; omega)
  have hA : mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum ≤ 80 ^ 8 * T n := by
    calc mrZ es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) ^ 8 * 2 ^ es.sum
        ≤ (80 * b n) ^ 8 * 2 ^ es.sum := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hZ 8)
      _ = 80 ^ 8 * (b n ^ 8 * 2 ^ es.sum) := by ring
      _ ≤ 80 ^ 8 * (r n * 2 ^ es.sum) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hbr)
      _ = 80 ^ 8 * T n := by rw [← hT]; ring
  have hB : 2 ^ es.sum * (2 ^ ℓ n * dsW n) ≤ 12 * (T n * p n) := by
    calc 2 ^ es.sum * (2 ^ ℓ n * dsW n) = (2 ^ es.sum * r n) * dsW n := by unfold r; ring
      _ = T n * dsW n := by rw [hT]
      _ ≤ T n * (12 * p n) := Nat.mul_le_mul_left _ (by unfold p; omega)
      _ = 12 * (T n * p n) := by ring
  have hp1 : 1 ≤ p n := by unfold p; omega
  have hTp : T n ≤ T n * p n := Nat.le_mul_of_pos_right _ hp1
  have h3 : synTwCost es (ℓ n) (dsW n) h ≤ (500 * 80 ^ 8 + 720) * (T n * p n) := by nlinarith
  exact_mod_cast h3

end
end IntegerMultBounds.MathlibTM2.Cost
