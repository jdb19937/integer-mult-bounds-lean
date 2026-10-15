module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformTransforms
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedGeometry
public import IntegerMultBounds.MathlibTM2.Fast.CompactBundleMnLay

/-! Concrete forward and opposite transforms with original layout programs and complete frame restoration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

def compactSynRetunedFwdCost (M cL : ℕ) : ℕ :=
  (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynUniformLoopFCost (Ka := mnKa) Cost.brDirs M (Mult.CompactSizes.K M) (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (nRounds (cvAx (t M)))
        (synStashCostW (A := prime+mnKa) (compactDsyV₀ M) synXS+6*nRounds (cvAx (t M))+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2))))


theorem compactSynRetunedFwd_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynFwdSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactSynRetunedFwdCost M (compactBlCL M)) := by
  have hA : 21≤prime+mnKa := by have := mnKa_alpha; omega
  filter_upwards [compactSynUniformFwd_eventually hA (embKa_hA9 mnKa_le) (embKa_hNW mnKa_le),
    compactSynRetunedGeometry_eventually,compactBlLay.wires,compactBlLay.layF]
    with M hspec hg hv hLay
  intro mainP
  obtain ⟨hv₀,hvh,hvt,hvc,hcb⟩ := hv
  have hAl : nRounds (cvAx (t M))≤Mult.Sizes.ℓ M+1 :=
    (nRounds_le hg.layout).trans (Nat.le_succ _)
  dsimp only [compactBlLay] at hv₀ hvh hvt hvc hcb hLay
  exact hspec Cost.brDirs Cost.br_directions_realizes (embKa_gate mnKa_le)
    (mnBody mnLb mainP) (mn_body_lay mainP) (Mult.CompactSizes.K M) _
    (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) (cvAx (t M)) hg hAl
    (compactDsyV₀ M) hv₀ hvh hvt hvc hcb (slyPk (blW dsW M) (blE M))
    (slyFwd mnQ_layer) (compactBlCL M) hLay

def compactSynRetunedOppCost (M cL : ℕ) : ℕ :=
  (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynUniformLoopOCost (Ka := mnKa) Cost.brDirs M (Mult.CompactSizes.K M) (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (nRounds (cvAx (t M)))
        (synStashCostW (A := prime+mnKa) (compactDsyV₀ M) synXS+6*nRounds (cvAx (t M))+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2))))


theorem compactSynRetunedOpp_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    SynOppSpec (compactMainBody (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactSynRetunedOppCost M (compactBlCL' M)) := by
  have hA : 21≤prime+mnKa := by have := mnKa_alpha; omega
  filter_upwards [compactSynUniformOpp_eventually hA (embKa_hA9 mnKa_le) (embKa_hNW mnKa_le),
    compactSynRetunedGeometry_eventually,compactBlLay.wires,compactBlLay.layO]
    with M hspec hg hv hLay
  intro mainP
  obtain ⟨hv₀,hvh,hvt,hvc,hcb⟩ := hv
  have hAl : nRounds (cvAx (t M))≤Mult.Sizes.ℓ M+1 :=
    (nRounds_le hg.layout).trans (Nat.le_succ _)
  dsimp only [compactBlLay] at hv₀ hvh hvt hvc hcb hLay
  exact hspec Cost.brDirs Cost.br_directions_realizes (embKa_gate mnKa_le)
    (mnBody mnLb mainP) (mn_body_lay mainP) (Mult.CompactSizes.K M) _
    (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) (cvAx (t M)) hg hAl
    (compactDsyV₀ M) hv₀ hvh hvt hvc hcb (slyPk (blW dsW M) (blE M))
    (slyOpp mnQ_layer) (compactBlCL' M) hLay

end
end IntegerMultBounds.MathlibTM2.Fast.Main
