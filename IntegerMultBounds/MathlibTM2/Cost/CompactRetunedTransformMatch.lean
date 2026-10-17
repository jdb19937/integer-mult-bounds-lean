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

end
end IntegerMultBounds.MathlibTM2.Cost
