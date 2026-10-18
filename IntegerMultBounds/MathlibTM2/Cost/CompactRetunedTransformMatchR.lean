module

import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLayerMatchR
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLayoutMatch
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedStashMatch
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedDirectCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransformsR
public import IntegerMultBounds.MathlibTM2.Cost.CompactStageGrowth
import IntegerMultBounds.MathlibTM2.Cost.MatchSynPipe
import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
import IntegerMultBounds.MathlibTM2.Cost.MatchSynLay
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The cost of the rounded transforms at the retuned sizes: rounded compact chunk rounds, the
exact direct boundary rounds and the loop bookkeeping, against the convolution envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node Filter Mult.SynthErr
noncomputable section

private theorem dispatchBoundR (ell K h : ℕ) (hh : h≤ell) :
    compactSynDispatchCost ell K h≤20*ell+26 := by
  have hb : layB ell K≤ell := (Nat.mod_le _ _).trans (Nat.sub_le _ _)
  unfold compactSynDispatchCost compactSynCompareCost
  simp only [Bool.false_eq_true,ite_true,ite_false,Nat.sub_zero]
  split_ifs <;> omega

private theorem layer_le_stepR (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ell K w l h s : ℕ) : synLayerCost ds es ell K l w h≤synLayerStepCost ds es ell K w l h s := by
  unfold synLayerStepCost
  dsimp only
  omega

/-- Rounded compact rounds use the stronger layer exponent; the at-most-K boundary
rounds keep their linear-in-d direct contribution explicit. -/
theorem compactRetunedR_round_le {Ka : ℕ} :
    ∃ C₁ C₂ C₃ : ℝ, 0≤C₁ ∧ 0≤C₂ ∧ 0≤C₃ ∧
    ∀ᶠ n in atTop, ∀ h<ℓ n, ∀ stash : ℕ,
      (compactSynRoundFCostR (Ka:=Ka) brDirs n (Mult.CompactSizes.K n)
        (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) h stash:ℝ)≤
        (C₁*((T n:ℝ)*p n)*(d n:ℝ)^CompactInterim.lam'+C₃*((T n:ℝ)*p n)+2*stash+2)+
          if synChunk (ℓ n) (Mult.CompactSizes.K n) h then 0 else C₂*((T n:ℝ)*p n)*d n := by
  obtain ⟨C₂,hC₂,hprefix⟩ := compactRetuned_direct_layer_le
  obtain ⟨C₃,hC₃,hover⟩ := compactRetuned_direct_over_le
  obtain ⟨C₄,hC₄,htwist⟩ := compactRetuned_tw_le
  have hCC : 0≤compactRetunedRoundCoeffR brDirs := by
    have ht : 0≤compactRetunedTopCoeff 1 brDirs := (compactLayerDyadic_pos _).le
    change 0≤16*(32768+2*compactRetunedTopCoeff 1 brDirs)
    linarith
  refine ⟨12*compactRetunedRoundCoeffR brDirs,C₂,C₃+C₄+4,by positivity,hC₂,by positivity,?_⟩
  filter_upwards [eventually_big,hprefix,hover,htwist,mr_small_le 46 1,
    compactRetunedR_layer_chunk_eventually (Ka:=Ka) brDirs 4 compactLayer_br_logb]
    with n hbig hprefix hover htwist hsmall hchunkCost
  intro h hh stash
  obtain ⟨H,-,hlen,hN,hT,-,-,hell,-,-,-,-,hw⟩ := compactRetuned_inst hbig
  have hbP : b n≤p n := Nat.le_mul_of_pos_left _ (by decide : 0<6)
  have hWp : p n≤dsW n := (Nat.le_add_right (p n) 2).trans (ds_w_B n)
  have hWP : dsW n≤2^4*(p n+1) := by unfold p; omega
  have hv : 2^(List.ofFn (cvAx (t n))).sum*(2^(ℓ n)*dsW n)≤12*(T n*p n) := by
    calc
      _ = (2^(List.ofFn (cvAx (t n))).sum*r n)*dsW n := by unfold r; ring
      _ = T n*dsW n := by rw [hT]
      _ ≤ T n*(12*p n) := Nat.mul_le_mul_left _ (by unfold p; omega)
      _ = _ := by ring
  have hdsp : (compactSynDispatchCost (ℓ n) (Mult.CompactSizes.K n) h:ℝ)≤(T n:ℝ)*p n := by
    apply hsmall
    have hb := dispatchBoundR (ℓ n) (Mult.CompactSizes.K n) h (by omega)
    simp only [pow_one]
    omega
  have hTp1 : (1:ℝ)≤(T n:ℝ)*p n := one_le_mul_of_one_le_of_one_le (mt_one_le_T n) (mt_one_le_p hbig)
  have hC₃Tp : 0≤C₃*((T n:ℝ)*p n) := mul_nonneg hC₃ (by linarith)
  have hC₄Tp : 0≤C₄*((T n:ℝ)*p n) := mul_nonneg hC₄ (by linarith)
  have hTw : (synTwCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) h:ℝ)≤(C₃+C₄)*((T n:ℝ)*p n)+2 := by
    have := htwist h hh
    nlinarith
  by_cases hc : synChunk (ℓ n) (Mult.CompactSizes.K n) h
  · have hl := hchunkCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) h stash
      H hlen (hN.trans hbP) (hell.trans hbP) (le_refl _) (hell.trans hbP) hWp hWP (by omega) hc
    have hvolR : ((2^(List.ofFn (cvAx (t n))).sum*(2^(ℓ n)*dsW n):ℕ):ℝ)≤12*((T n:ℝ)*p n) := by exact_mod_cast hv
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvolR hCC) (Real.rpow_nonneg (Nat.cast_nonneg (d n)) CompactInterim.lam')
    simp only [compactSynRoundFCostR,Nat.cast_add,Nat.cast_one,hc,ite_true,add_zero]
    nlinarith only [hl,hscaled,hTw,hdsp,hTp1]
  · have hl := hprefix h hc
    have ho := hover h hh hc stash
    have hbase : 0≤12*compactRetunedRoundCoeffR brDirs*((T n:ℝ)*p n)*(d n:ℝ)^CompactInterim.lam' := by positivity
    simp only [compactSynRoundFCostR,compactSynLayerCostR,hc,ite_false,Nat.cast_add,Nat.cast_one]
    push_cast at ho
    nlinarith only [hl,ho,hdsp,hTp1,hbase,hC₄Tp]


theorem compactRetunedR_loops_le {Ka : ℕ} (ds : ComplexFramedExecution.Directions) (M : ℕ) (es : List ℕ)
    (ℓ K w l A stk : ℕ) :
    compactSynLoopFCostR (Ka:=Ka) ds M K es ℓ w l A stk ≤
        (∑ h ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l h stk) + 6 * A ^ 2 + 16 * A + 4 ∧
      compactSynLoopOCostR (Ka:=Ka) ds M K es ℓ w l A stk ≤
        (∑ h ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l h stk) + 6 * A ^ 2 + 16 * A + 4 := by
  have hS : ∀ f : ℕ → ℕ, (∀ j < A, f j ≤ 6 * A + 14) →
      ∑ j ∈ Finset.range A, f j ≤ 6 * A ^ 2 + 14 * A := by
    intro f hf
    calc ∑ j ∈ Finset.range A, f j ≤ ∑ j ∈ Finset.range A, (6 * A + 14) :=
          Finset.sum_le_sum fun j hj => hf j (Finset.mem_range.1 hj)
      _ = 6 * A ^ 2 + 14 * A := by simp; ring
  constructor
  · unfold compactSynLoopFCostR
    have e : ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + 1 +
        compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk + (2 * (A - 1 - j) + 2) + 3) =
        (∑ j ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk) +
          ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + 1 + (2 * (A - 1 - j) + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hr : ∑ j ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l (A - 1 - j) stk =
        ∑ h ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l h stk :=
      Finset.sum_range_reflect (fun h => compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l h stk) A
    have := hS (fun j => (4 * (A - 1 - j) + 4) + 1 + (2 * (A - 1 - j) + 2) + 3)
      (fun j hj => by omega)
    omega
  · unfold compactSynLoopOCostR
    have e : ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 +
        compactSynRoundOCostR (Ka:=Ka) ds M K es ℓ w l j stk + (2 * j + 2) + 3) =
        (∑ j ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) ds M K es ℓ w l j stk) +
          ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold compactSynRoundFCostR compactSynRoundOCostR; ring
    rw [e]
    have := hS (fun j => (4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) (fun j hj => by omega)
    omega

theorem compactRetunedR_loop_cost_le {Ka : ℕ} : ∀ C_s k : ℕ, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ stk ≤ C_s * (r n + (b n + 1) ^ k),
    ((compactSynLoopFCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n)
        (nRounds (cvAx (t n))) stk +
      compactSynLoopOCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n)
        (nRounds (cvAx (t n))) stk : ℕ) : ℝ) ≤ C * CompactTotal.conv n := by
  intro Cs k
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hr⟩ := compactRetunedR_round_le (Ka:=Ka)
  refine ⟨2 * (C₁ + C₂ + C₃ + 3), ?_⟩
  filter_upwards [eventually_big, hr, mr_small_le (2 * (Cs + 1)) (k + 1), mr_small_le 52 2,
    ml_poly_r_le_T (4 * Cs) 1 1] with n hbig hr hsm1 hsm2 hpr stk hstk
  obtain ⟨H, -, hlen, hN, hT, hA, hK1, hℓ, hK, hd, hb16, hd16, hw⟩ := compactRetuned_inst hbig
  generalize hes : List.ofFn (cvAx (t n)) = es at *
  generalize hAe : nRounds (cvAx (t n)) = A at *
  obtain ⟨hF, hO⟩ := compactRetunedR_loops_le (Ka:=Ka) Cost.brDirs n es (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) A stk
  -- the sum of the rounds
  have hsum : ((∑ h ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) h
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
        = C₂ * ((T n : ℝ) * p n * ((d n : ℝ) * ((layB (ℓ n) (Mult.CompactSizes.K n) : ℝ) + 1))) := by
          ring
      _ ≤ C₂ * CompactTotal.conv n := mul_le_mul_of_nonneg_left hc2 hC₂
  have hpark' : (A : ℝ) * (2 * stk + 2) ≤ 2 * CompactTotal.conv n := by
    have : ((A * (2 * stk + 2) : ℕ) : ℝ) = (A : ℝ) * (2 * stk + 2) := by push_cast; ring
    linarith
  have hbook' : 12 * (A : ℝ) ^ 2 + 32 * A + 8 ≤ CompactTotal.conv n := by
    have : ((12 * A ^ 2 + 32 * A + 8 : ℕ) : ℝ) = 12 * (A : ℝ) ^ 2 + 32 * A + 8 := by push_cast; ring
    linarith
  have htot : ((compactSynLoopFCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk +
      compactSynLoopOCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk : ℕ) : ℝ) ≤
      2 * ((∑ h ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) h
        stk : ℕ) : ℝ) + (12 * (A : ℝ) ^ 2 + 32 * A + 8) := by
    have : compactSynLoopFCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk +
        compactSynLoopOCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) A stk ≤
        2 * (∑ h ∈ Finset.range A, compactSynRoundFCostR (Ka:=Ka) Cost.brDirs n (Mult.CompactSizes.K n) es (ℓ n) (dsW n) (ℓ n) h stk) +
          (12 * A ^ 2 + 32 * A + 8) := by omega
    exact_mod_cast this
  have hA2 : (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam' +
      C₃ * ((T n : ℝ) * p n) + 2 * stk + 2) =
      (A : ℝ) * (C₁ * ((T n : ℝ) * p n) * (d n : ℝ) ^ CompactInterim.lam') +
        (A : ℝ) * (C₃ * ((T n : ℝ) * p n)) + (A : ℝ) * (2 * stk + 2) := by ring
  rw [hA2] at hsum
  have hconv0 := CompactTotal.conv_nonneg hbig
  linarith


open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
private theorem bootstrapPolyR (p d : ℕ) (hd : d≤p) :
    compactMnOriginalBootstrapCost p d+((2*d+2)+(2*(4*Nat.clog 2 p+6)+2))+1≤1000*(p+1)^2 := by
  have hc := mrO_cnt_le 2 (p-1) (p-1)
  have hl : Nat.clog 2 p≤p := (Nat.clog_le_iff_le_pow (by decide : 1<2)).2 (Nat.lt_two_pow_self (n:=p)).le
  have hs : p-1≤p := Nat.sub_le _ _
  have hm := Nat.mul_le_mul hs (show 8*(p-1)+14≤8*p+14 by omega)
  have hdsub : d-1≤d := Nat.sub_le _ _
  unfold compactMnOriginalBootstrapCost compactMnBootstrapCost compactGlobalBootstrapCost compactGlobalGuardCost
  nlinarith

theorem compactRetunedR_transform_cost_le :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      ((compactSynRetunedFwdCostR n (compactBlCL n)+compactSynRetunedOppCostR n (compactBlCL' n):ℕ):ℝ)≤C*CompactTotal.conv n := by
  obtain ⟨CL,hL⟩ := compactRetuned_ml_lay_cost_le_gen
  obtain ⟨CR,hR⟩ := compactRetunedR_loop_cost_le (Ka:=mnKa) 806 2
  refine ⟨CL+CR+2,?_⟩
  filter_upwards [hL,hR,compactRetuned_finStash,eventually_big,mr_small_le 36000 2] with n hL hR hs hbig hsmall
  have hl := hL (blE n) (compactDsyV₀ n)
  change ((compactBlCL n+compactBlCL' n:ℕ):ℝ)≤CL*CompactTotal.conv n at hl
  have hr := hR _ hs
  have hbase : ((compactMnOriginalBootstrapCost (p n) (d n)+((2*d n+2)+(2*(4*Nat.clog 2 (p n)+6)+2))+1:ℕ):ℝ)≤CompactTotal.conv n := by
    apply le_trans (hsmall _ ?_) (compactRetuned_conv_ge hbig).1
    have hd : d n≤p n := (mt_d_le_b n).trans (Nat.le_mul_of_pos_left _ (by decide : 0<6))
    have hb := bootstrapPolyR (p n) (d n) hd
    have hp : p n+1≤6*(b n+1) := by unfold p; omega
    have hp2 := Nat.pow_le_pow_left hp 2
    exact hb.trans ((Nat.mul_le_mul_left 1000 hp2).trans (le_of_eq (by ring)))
  unfold compactSynRetunedFwdCostR compactSynRetunedOppCostR
  generalize compactBlCL n = cL at hl ⊢
  generalize compactBlCL' n = cL' at hl ⊢
  generalize compactSynLoopFCostR (Ka:=mnKa) brDirs n (Mult.CompactSizes.K n)
    (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) (nRounds (cvAx (t n)))
    (synStashCostW (A:=prime+mnKa) (compactDsyV₀ n) synXS+6*nRounds (cvAx (t n))+6) = F at hr ⊢
  generalize compactSynLoopOCostR (Ka:=mnKa) brDirs n (Mult.CompactSizes.K n)
    (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) (nRounds (cvAx (t n)))
    (synStashCostW (A:=prime+mnKa) (compactDsyV₀ n) synXS+6*nRounds (cvAx (t n))+6) = O at hr ⊢
  push_cast at hl hr hbase ⊢
  linarith

end
end IntegerMultBounds.MathlibTM2.Cost
