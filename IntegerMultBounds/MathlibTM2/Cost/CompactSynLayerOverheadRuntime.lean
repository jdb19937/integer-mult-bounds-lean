module
import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadBound
import IntegerMultBounds.MathlibTM2.Cost.CompactRuntimePolynomial
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-! Eventual absorption of actual complete compact-round overhead. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

private theorem compactCoefficient_le_volume (rows n r working : ℕ)
    (hrows : 0<rows) (hw : 0<working) : r≤rows*2^n*(r*working) :=
  (Nat.le_mul_of_pos_right r hw).trans
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos hrows (pow_pos (by decide : 0<2) n)))

/-- Fixed polynomial scalar budgets make the actual whole-round overhead
linear in padded working volume, with its two stash passes still explicit. -/
theorem compactSynLayerRoundOverhead_eventually (ds : ComplexFramedExecution.Directions)
    (G F c e : ℕ) : ∀ᶠ M : ℕ in atTop,
    ∀ N d g K D o W r h b ρ stash B : ℕ,
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := D-qrow-f-back
    let E := back+synE G F active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(back+active)
    let shift := (D+1)/2+q+E
    let working := W+shift+D
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W shift a 1 R₂ q aT K o D
    let V := R₂*2^n*(r*working)
    ∀ (_hB : 1≤B) (_hF : F+1≤m^5) (_hdpos : 0<d)
      (_hKpos : 0<K) (_hr : 0<r) (_hWpos : 0<W)
      (_hN : N≤B) (_hd : d≤B) (_hg : g≤B) (_hK : K≤B) (_hD : D≤B)
      (_ho : o≤B) (_hW : W≤B) (_hdg : d*g≤B) (_hh : h≤B) (_hb : b≤B) (_hρ : ρ<K)
      (_hqrow : qrow≤B) (_hf : f≤B) (_hback : back≤B) (_hoffset : o+K*back≤B)
      (_hE : E≤B) (_hq : q≤B) (_haT : aT≤B) (_hKq : K*q≤B)
      (_hdivisor : NW^CompactGlobalRowPadding.depth m d≤B)
      (_ha : qrow*K≤a) (_hn : qrow*K+3≤n) (_hnN : n≤N)
      (_hpoly : B≤2^c*(Mult.Sizes.p M+1)^e) (_hrun : Mult.Sizes.r M≤r)
      (_hpcs : ∀ pc∈pcs,pc.Ok ds K n working R₂),
    compactSynLayerRoundOverhead G F N d g K D o W r h b ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      32768*V+2*stash := by
  filter_upwards [compactRuntime_eventually_setup_volume (262144*(G+m+1)) c e 7 14,
    compactRuntime_eventually_polynomial c e] with M habs hscalar
  intro N d g K D o W r h b ρ stash B
  dsimp only
  intro hB hF hdpos hKpos hr hWpos hN hd hg hK hD ho hW hdg hh hb hρ
    hqrow hf hback hoffset hE hq haT hKq hdivisor ha hn hnN hpoly hrun hpcs
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let back := backChunks d g K
  let active := D-qrow-f-back
  let E := back+synE G F active active
  let n := o+K*(D-qrow)
  let a := N-n
  let q := qrow+f
  let aT := o+K*(back+active)
  let shift := (D+1)/2+q+E
  let working := W+shift+D
  let R₂ := compactTopRows d 1 a
  let pcs := compactTopPcs d g K D o R₂
  let cfg := topCfg W shift a 1 R₂ q aT K o D
  let V := R₂*2^n*(r*working)
  change qrow*K≤a at ha
  have hw : 0<working := hWpos.trans_le
    ((Nat.le_add_right W shift).trans (Nat.le_add_right (W+shift) D))
  have hrows : 0<R₂ := compactTopRows_positive hKpos (by decide : 0<1) ha
  have hrV : r≤V := compactCoefficient_le_volume R₂ n r working hrows hw
  have hBV : B≤V := hpoly.trans (hscalar.trans (hrun.trans hrV))
  have hbound := compactSynLayerRoundOverhead_complete ds G F N d g K D o W r h b ρ stash B
    hB hF hdpos hKpos hr hWpos hN hd hg hK hD ho hW hdg hh hb hρ
    hqrow hf hback hoffset hE hq haT hKq hdivisor ha hn hnN hBV hpcs
  have hpay := habs B V hpoly (hrun.trans hrV)
  change (262144*(G+m+1))*B^7+16384*V≤32768*V at hpay
  have hpay' : 262144*((G+m+1)*B^7)+16384*V≤32768*V := by
    simpa only [Nat.mul_assoc] using hpay
  exact hbound.trans (Nat.add_le_add_right hpay' (2*stash))

end
end IntegerMultBounds.MathlibTM2.Cost
