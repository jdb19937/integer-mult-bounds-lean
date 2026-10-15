module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLayoutMatch
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedStashMatch
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
private theorem bootstrapPoly (p d : ℕ) (hd : d≤p) :
    compactMnOriginalBootstrapCost p d+((2*d+2)+(2*(4*Nat.clog 2 p+6)+2))+1≤1000*(p+1)^2 := by
  have hc := mrO_cnt_le 2 (p-1) (p-1)
  have hl : Nat.clog 2 p≤p := (Nat.clog_le_iff_le_pow (by decide : 1<2)).2 (Nat.lt_two_pow_self (n:=p)).le
  have hs : p-1≤p := Nat.sub_le _ _
  have hm := Nat.mul_le_mul hs (show 8*(p-1)+14≤8*p+14 by omega)
  have hdsub : d-1≤d := Nat.sub_le _ _
  unfold compactMnOriginalBootstrapCost compactMnBootstrapCost compactGlobalBootstrapCost compactGlobalGuardCost
  nlinarith

theorem compactRetuned_transform_cost_le :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      ((compactSynRetunedFwdCost n (compactBlCL n)+compactSynRetunedOppCost n (compactBlCL' n):ℕ):ℝ)≤C*CompactTotal.conv n := by
  obtain ⟨CL,hL⟩ := compactRetuned_ml_lay_cost_le_gen
  obtain ⟨CR,hR⟩ := compactRetuned_loop_cost_le (Ka:=mnKa) 806 2
  refine ⟨CL+CR+2,?_⟩
  filter_upwards [hL,hR,compactRetuned_finStash,eventually_big,mr_small_le 36000 2] with n hL hR hs hbig hsmall
  have hl := hL (blE n) (compactDsyV₀ n)
  change ((compactBlCL n+compactBlCL' n:ℕ):ℝ)≤CL*CompactTotal.conv n at hl
  have hr := hR _ hs
  have hbase : ((compactMnOriginalBootstrapCost (p n) (d n)+((2*d n+2)+(2*(4*Nat.clog 2 (p n)+6)+2))+1:ℕ):ℝ)≤CompactTotal.conv n := by
    apply le_trans (hsmall _ ?_) (compactRetuned_conv_ge hbig).1
    have hd : d n≤p n := (mt_d_le_b n).trans (Nat.le_mul_of_pos_left _ (by decide : 0<6))
    have hb := bootstrapPoly (p n) (d n) hd
    have hp : p n+1≤6*(b n+1) := by unfold p; omega
    have hp2 := Nat.pow_le_pow_left hp 2
    exact hb.trans ((Nat.mul_le_mul_left 1000 hp2).trans (le_of_eq (by ring)))
  unfold compactSynRetunedFwdCost compactSynRetunedOppCost
  generalize compactBlCL n = cL at hl ⊢
  generalize compactBlCL' n = cL' at hl ⊢
  generalize compactSynUniformLoopFCost (Ka:=mnKa) brDirs n (Mult.CompactSizes.K n)
    (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) (nRounds (cvAx (t n)))
    (synStashCostW (A:=prime+mnKa) (compactDsyV₀ n) synXS+6*nRounds (cvAx (t n))+6) = F at hr ⊢
  generalize compactSynUniformLoopOCost (Ka:=mnKa) brDirs n (Mult.CompactSizes.K n)
    (List.ofFn (cvAx (t n))) (ℓ n) (dsW n) (ℓ n) (nRounds (cvAx (t n)))
    (synStashCostW (A:=prime+mnKa) (compactDsyV₀ n) synXS+6*nRounds (cvAx (t n))+6) = O at hr ⊢
  push_cast at hl hr hbase ⊢
  linarith

end
end IntegerMultBounds.MathlibTM2.Cost
