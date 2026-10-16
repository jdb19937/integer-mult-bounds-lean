module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLayerMatch
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
open IntegerMultBounds.MathlibTM2.Node Filter
noncomputable section

private theorem dispatchBound (ell K h : ℕ) (hh : h≤ell) :
    compactSynDispatchCost ell K h≤20*ell+26 := by
  have hb : layB ell K≤ell := (Nat.mod_le _ _).trans (Nat.sub_le _ _)
  unfold compactSynDispatchCost compactSynCompareCost
  simp only [Bool.false_eq_true,ite_true,ite_false,Nat.sub_zero]
  split_ifs <;> omega

private theorem layer_le_step (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ell K w l h s : ℕ) : synLayerCost ds es ell K l w h≤synLayerStepCost ds es ell K w l h s := by
  unfold synLayerStepCost
  dsimp only
  omega

/-- Compact rounds use the stronger layer exponent; the at-most-K boundary
rounds keep their linear-in-d direct contribution explicit. -/
theorem compactRetuned_round_le {Ka : ℕ} :
    ∃ C₁ C₂ C₃ : ℝ, 0≤C₁ ∧ 0≤C₂ ∧ 0≤C₃ ∧
    ∀ᶠ n in atTop, ∀ h<ℓ n, ∀ stash : ℕ,
      (compactSynUniformRoundFCost (Ka:=Ka) brDirs n (Mult.CompactSizes.K n)
        (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) h stash:ℝ)≤
        (C₁*((T n:ℝ)*p n)*(d n:ℝ)^CompactInterim.lam'+C₃*((T n:ℝ)*p n)+2*stash+2)+
          if synChunk (ℓ n) (Mult.CompactSizes.K n) h then 0 else C₂*((T n:ℝ)*p n)*d n := by
  obtain ⟨C₂,hC₂,hprefix⟩ := compactRetuned_direct_layer_le
  obtain ⟨C₃,hC₃,hover⟩ := compactRetuned_direct_over_le
  have hCC : 0≤compactRetunedRoundCoeff brDirs := by
    have ht := (compactLayerDyadic_pos
      (16384*compactTopCountConst Parameters.lam+
       512*compactRetunedReservationCoeff CompactInterim.lam'+
       compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) 1 brDirs Parameters.lam) m Parameters.lam*
         compactCallerGuardPowerCoeff (CompactInterim.lam'-Parameters.lam))).le
    change 0≤4*(32768+compactRetunedTopCoeff 1 brDirs)
    change 0≤compactRetunedTopCoeff 1 brDirs at ht
    linarith
  refine ⟨12*compactRetunedRoundCoeff brDirs,C₂,C₃+4,by positivity,hC₂,by positivity,?_⟩
  filter_upwards [eventually_big,hprefix,hover,mr_small_le 46 1,
    compactRetuned_layer_chunk_eventually (Ka:=Ka) brDirs 4 mr_F_le compactLayer_br_logb]
    with n hbig hprefix hover hsmall hchunkCost
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
    have hb := dispatchBound (ℓ n) (Mult.CompactSizes.K n) h (by omega)
    simp only [pow_one]
    omega
  have hTp1 : (1:ℝ)≤(T n:ℝ)*p n := one_le_mul_of_one_le_of_one_le (mt_one_le_T n) (mt_one_le_p hbig)
  have hTw : (synTwCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) h:ℝ)≤C₃*((T n:ℝ)*p n)+2 := by
    have ho := hover h hh 0
    have hl : (synLayerCost brDirs (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (ℓ n) (dsW n) h:ℝ)≤
        synLayerStepCost brDirs (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) h 0 := by
      exact_mod_cast layer_le_step brDirs (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n) (dsW n) (ℓ n) h 0
    push_cast at ho
    linarith
  by_cases hc : synChunk (ℓ n) (Mult.CompactSizes.K n) h
  · have hl := hchunkCost (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) h stash
      H hlen (hN.trans hbP) (hell.trans hbP) (le_refl _) hWp hWP (by omega) hc
    have hvolR : ((2^(List.ofFn (cvAx (t n))).sum*(2^(ℓ n)*dsW n):ℕ):ℝ)≤12*((T n:ℝ)*p n) := by exact_mod_cast hv
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvolR hCC) (Real.rpow_nonneg (Nat.cast_nonneg (d n)) CompactInterim.lam')
    simp only [compactSynUniformRoundFCost,Nat.cast_add,Nat.cast_one,hc,ite_true,add_zero]
    nlinarith only [hl,hscaled,hTw,hdsp,hTp1]
  · have hl := hprefix h hc
    have ho := hover h hh stash
    have hbase : 0≤12*compactRetunedRoundCoeff brDirs*((T n:ℝ)*p n)*(d n:ℝ)^CompactInterim.lam' := by positivity
    simp only [compactSynUniformRoundFCost,compactSynUniformLayerCost,hc,ite_false,Nat.cast_add,Nat.cast_one]
    push_cast at ho
    nlinarith only [hl,ho,hdsp,hTp1,hbase]

end
end IntegerMultBounds.MathlibTM2.Cost
