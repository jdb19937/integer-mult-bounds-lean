module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedRoundMatch
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

theorem compactRetuned_loops_le {Ka : ℕ} (ds : ComplexFramedExecution.Directions) (M : ℕ) (es : List ℕ)
    (ℓ K w l A stk : ℕ) :
    compactSynUniformLoopFCost (Ka:=Ka) ds M K es ℓ w l A stk ≤
        (∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk) + 6 * A ^ 2 + 16 * A + 4 ∧
      compactSynUniformLoopOCost (Ka:=Ka) ds M K es ℓ w l A stk ≤
        (∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk) + 6 * A ^ 2 + 16 * A + 4 := by
  have hS : ∀ f : ℕ → ℕ, (∀ j < A, f j ≤ 6 * A + 14) →
      ∑ j ∈ Finset.range A, f j ≤ 6 * A ^ 2 + 14 * A := by
    intro f hf
    calc ∑ j ∈ Finset.range A, f j ≤ ∑ j ∈ Finset.range A, (6 * A + 14) :=
          Finset.sum_le_sum fun j hj => hf j (Finset.mem_range.1 hj)
      _ = 6 * A ^ 2 + 14 * A := by simp; ring
  constructor
  · unfold compactSynUniformLoopFCost
    have e : ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + 1 +
        compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk + (2 * (A - 1 - j) + 2) + 3) =
        (∑ j ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk) +
          ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + 1 + (2 * (A - 1 - j) + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hr : ∑ j ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk =
        ∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk :=
      Finset.sum_range_reflect (fun h => compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l h stk) A
    have := hS (fun j => (4 * (A - 1 - j) + 4) + 1 + (2 * (A - 1 - j) + 2) + 3)
      (fun j hj => by omega)
    omega
  · unfold compactSynUniformLoopOCost
    have e : ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 +
        compactSynUniformRoundOCost (Ka:=Ka) ds M K es ℓ w l j stk + (2 * j + 2) + 3) =
        (∑ j ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) ds M K es ℓ w l j stk) +
          ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold compactSynUniformRoundFCost compactSynUniformRoundOCost; ring
    rw [e]
    have := hS (fun j => (4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) (fun j hj => by omega)
    omega

theorem compactRetuned_loop_cost_le {Ka : ℕ} : ∀ C_s k : ℕ, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ stk ≤ C_s * (r n + (b n + 1) ^ k),
    ((compactSynUniformLoopFCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n)
        (nRounds (cvAx (t n))) stk +
      compactSynUniformLoopOCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n)
        (nRounds (cvAx (t n))) stk : ℕ) : ℝ) ≤ C * CompactTotal.conv n := by
  intro Cs k
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hr⟩ := compactRetuned_round_le (Ka:=Ka)
  refine ⟨2 * (C₁ + C₂ + C₃ + 3), ?_⟩
  filter_upwards [eventually_big, hr, mr_small_le (2 * (Cs + 1)) (k + 1), mr_small_le 52 2,
    ml_poly_r_le_T (4 * Cs) 1 1] with n hbig hr hsm1 hsm2 hpr stk hstk
  obtain ⟨H, -, hlen, hN, hT, hA, hK1, hℓ, hK, hd, hb16, hd16, hw⟩ := compactRetuned_inst hbig
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  generalize hAe : nRounds (cvAx (t n)) = A at *
  obtain ⟨hF, hO⟩ := compactRetuned_loops_le (Ka:=Ka) Cost.brDirs n es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) A stk
  -- the sum of the rounds
  have hsum : ((∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) h
      stk : ℕ) : ℝ) ≤
      A * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam' + C₃ * ((T n : ℝ) * p n) +
        2 * stk + 2) + (layB (ℓ n) (Mult.CompactSizes.K n) + 1) * (C₂ * ((T n : ℝ) * p n) * d n) := by
    push_cast
    refine mr_rounds_split hA _ (mul_nonneg (mul_nonneg hC₂ (mt_Tp_nonneg n)) (Nat.cast_nonneg _))
      fun h hh => hr h (by omega) stk
  obtain ⟨hc1, hc2, hc3⟩ := compactRetuned_conv_ge hbig
  have hTp := mt_Tp_nonneg n
  have hdl : 1 ≤ (d n : ℝ) ^ CompactInterim.lam' :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d n by omega)) (by norm_num [CompactInterim.lam'])
  have hAℓ : (A : ℝ) ≤ ℓ n := by exact_mod_cast hA
  have hbK : (layB (ℓ n) (Mult.CompactSizes.K n) : ℝ) + 1 ≤ Mult.CompactSizes.K n := by exact_mod_cast H.b_lt
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
  have hmain1 : (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam') ≤ C₁ * CompactTotal.conv n := by
    calc (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam')
        ≤ (ℓ n : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam') :=
          mul_le_mul_of_nonneg_right hAℓ
            (mul_nonneg (mul_nonneg hC₁ hTp) (le_trans zero_le_one hdl))
      _ = C₁ * ((T n : ℝ) * p n * ((ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam')) := by ring
      _ ≤ C₁ * CompactTotal.conv n := by gcongr
  have hmain3 : (A : ℝ) * (C₃ * ((T n : ℝ) * p n)) ≤ C₃ * CompactTotal.conv n := by
    calc (A : ℝ) * (C₃ * ((T n : ℝ) * p n))
        ≤ (ℓ n : ℝ) * (C₃ * ((T n : ℝ) * p n)) := by gcongr
      _ ≤ (ℓ n : ℝ) * (C₃ * ((T n : ℝ) * p n)) * (d n : ℝ) ^ CompactInterim.lam' := by
          apply le_mul_of_one_le_right (by positivity) hdl
      _ = C₃ * ((T n : ℝ) * p n * ((ℓ n : ℝ) * (d n : ℝ) ^ CompactInterim.lam')) := by ring
      _ ≤ C₃ * CompactTotal.conv n := by gcongr
  have hmain2 : ((layB (ℓ n) (Mult.CompactSizes.K n) : ℝ) + 1) * (C₂ * ((T n : ℝ) * p n) * d n) ≤
      C₂ * CompactTotal.conv n := by
    calc ((layB (ℓ n) (Mult.CompactSizes.K n) : ℝ) + 1) * (C₂ * ((T n : ℝ) * p n) * d n)
        ≤ (Mult.CompactSizes.K n : ℝ) * (C₂ * ((T n : ℝ) * p n) * d n) :=
          mul_le_mul_of_nonneg_right hbK (mul_nonneg (mul_nonneg hC₂ hTp) (Nat.cast_nonneg _))
      _ = C₂ * ((T n : ℝ) * p n * ((d n : ℝ) * Mult.CompactSizes.K n)) := by ring
      _ ≤ C₂ * CompactTotal.conv n := by gcongr
  have hpark' : (A : ℝ) * (2 * stk + 2) ≤ 2 * CompactTotal.conv n := by
    have : ((A * (2 * stk + 2) : ℕ) : ℝ) = (A : ℝ) * (2 * stk + 2) := by push_cast; ring
    linarith
  have hbook' : 12 * (A : ℝ) ^ 2 + 32 * A + 8 ≤ CompactTotal.conv n := by
    have : ((12 * A ^ 2 + 32 * A + 8 : ℕ) : ℝ) = 12 * (A : ℝ) ^ 2 + 32 * A + 8 := by push_cast; ring
    linarith
  have htot : ((compactSynUniformLoopFCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk +
      compactSynUniformLoopOCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk : ℕ) : ℝ) ≤
      2 * ((∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) h
        stk : ℕ) : ℝ) + (12 * (A : ℝ) ^ 2 + 32 * A + 8) := by
    have : compactSynUniformLoopFCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk +
        compactSynUniformLoopOCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk ≤
        2 * (∑ h ∈ Finset.range A, compactSynUniformRoundFCost (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) h stk) +
          (12 * A ^ 2 + 32 * A + 8) := by omega
    exact_mod_cast this
  have hA2 : (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam' +
      C₃ * ((T n : ℝ) * p n) + 2 * stk + 2) =
      (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam') +
        (A : ℝ) * (C₃ * ((T n : ℝ) * p n)) + (A : ℝ) * (2 * stk + 2) := by ring
  rw [hA2] at hsum
  have hconv0 := CompactTotal.conv_nonneg hbig
  linarith

end
end IntegerMultBounds.MathlibTM2.Cost
