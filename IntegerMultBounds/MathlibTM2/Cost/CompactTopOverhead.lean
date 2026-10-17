module

import IntegerMultBounds.MathlibTM2.Cost.CompactTopBlockBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlBound
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Complete actual nonrecursive top-transform overhead. No scan, padding,
record, header, shift or cleanup cost is omitted. Recursive calls and kernel
execution are separated by compactTopCost_split. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

/-- Complete top control work is linear in padded stream volume, plus the
explicit number of piece records times their header/row metadata. -/
theorem compactTopControlCost_le {ds : ComplexFramedExecution.Directions}
    (w w' s n a R r K ρ q aT o D R₂ : ℕ) (pcs : List TopPc)
    (hR : 1≤R) (hr : 1≤r) (hw' : 1≤w') (hK : 1≤K)
    (hsw : s+w≤w') (hN : n+a≤r*w') (hρo : ρ+o≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a)
    (hcap : 2^a*R≤R₂) (hpcs : ∀ pc∈pcs,pc.Ok ds K n w' R₂) :
    let cfg := topCfg w s a R R₂ q aT K o D
    let V := R₂*(2^n*r*w')
    compactTopControlCost w w' s n a R r K ρ q aT o D R₂ pcs ≤
      2048*V+32*topGetCost cfg+
        pcs.length*(topGetCost cfg+32*n+2*R₂+32)+4 := by
  let cfg := topCfg w s a R R₂ q aT K o D
  let V := R₂*(2^n*r*w')
  have hL : 1≤2^n*r*w' :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow n 2 (by decide)) hr) hw'
  have hR₂ : 1≤R₂ := (Nat.mul_le_mul (Nat.one_le_pow a 2 (by decide)) hR).trans hcap
  have hV : 1≤V := Nat.mul_le_mul hR₂ hL
  have hsource : R*2^(n+a)*(r*w')≤V := by
    have hm := Nat.mul_le_mul_right (2^n*(r*w')) hcap
    dsimp only [V]
    rw [pow_add]
    nlinarith only [hm]
  have hcoeff : w'≤V := by
    have hs : 1≤R₂*2^n*r := Nat.mul_le_mul (Nat.mul_le_mul hR₂ (Nat.one_le_pow n 2 (by decide))) hr
    have hh := Nat.le_mul_of_pos_left w' hs
    dsimp only [V]
    nlinarith only [hh]
  have hRW : r*w'≤V := by
    have hs : 1≤R₂*2^n := Nat.mul_le_mul hR₂ (Nat.one_le_pow n 2 (by decide))
    have hh := Nat.le_mul_of_pos_left (r*w') hs
    dsimp only [V]
    nlinarith only [hh]
  have hRbase : R≤2^a*R := Nat.le_mul_of_pos_left R (Nat.one_le_pow a 2 (by decide))
  have hRV : R≤V := hRbase.trans (hcap.trans (Nat.le_mul_of_pos_right R₂ hL))
  have hD : D≤n+a := (Nat.le_mul_of_pos_right D hK).trans hDK
  have hq : q≤n+a := (Nat.le_mul_of_pos_left q hK).trans (by omega)
  have hNV : n+a≤V := hN.trans hRW
  have hww : w≤w' := by omega
  have hwiden := compactTopWidenSCost_linear cfg R (n+a) r w w' hw' hww
  have hphase := compactTopPhaseSCost_linear cfg (n+a) R r w' K ρ o D hR
    (Nat.mul_le_mul hr hw') hN hρo hDK hD
  have hunit := compactTopUnitSCost_linear cfg R (n+a) r w' D hw'
  have hshift := compactTopShiftSCost_linear cfg R (n+a) r w' s w hw' hsw
  have hblock := compactTopBlockCost_control cfg K n a r w' R R₂ pcs hK hr hw' hR hcap hpcs
  have hkernel : compactTopKerSCost cfg K R q aT 0 ≤ 4*topGetCost cfg+24*V := by
    unfold compactTopKerSCost
    nlinarith only [hq,hker,hNV,hRV,hV]
  dsimp only
  unfold compactTopControlCost compactTopCost
  change _ ≤2048*V+32*topGetCost cfg+pcs.length*(topGetCost cfg+32*n+2*R₂+32)+4
  change compactTopBlockCost cfg K n a r w' R R₂ (fun _ => 0) pcs ≤ _ at hblock
  change _ ≤512*V+8*topGetCost cfg+pcs.length*(topGetCost cfg+32*n+2*R₂+32)+4 at hblock
  nlinarith only [hwiden,hphase,hunit,hshift,hblock,hkernel,hsource,hcoeff,hV,hD,hNV,
    Nat.zero_le (topGetCost cfg)]

end IntegerMultBounds.MathlibTM2.Cost
