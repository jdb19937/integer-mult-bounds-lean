module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedMainEntry
public import IntegerMultBounds.MathlibTM2.Fast.CompactBundleWires

/-! Actual compact distribution execution supplies the main transform entry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.TableVM Filter
noncomputable section

/-- All entry hypotheses follow from the distribution output and preserved main invariant. -/
theorem compactSynRetunedMainPre_of_distribution (M x y : ℕ)
    (S₁ : Stacks mnT (prime+mnKa)) (S : Stacks compactMnT (prime+mnKa))
    (hL₁ : ∀ i,S₁.L i=[]) (hι : ∀ j,S₁.R (mnι j)=[])
    (hout : MnDistOut S₁.R M (dsW M) (bdE M) (mnσ (blP₀ dsW M) (compactDsyV₀ M)))
    (hmid : MnMid S₁ x y M) (hL : ∀ i,S.L i=[])
    (hb : ∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) :
    compactSynRetunedMainPre M (compactMainFinalStacks S₁ S) :=
  compactSynRetunedMainPre_placed M x y S₁ S ⟨hL₁,hι,hout.lay⟩ hmid hL hb

/-- Run the actual retuned distribution, preserve `MnMid`, and derive the
expanded main entry without an external wire-file or precision-source premise. -/
theorem compactBdDist_entry_eventually
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    ∀ᶠ M : ℕ in atTop, ∀ (mainP : MnPr bdA) (x y : ℕ)
      (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA),
      (∀ i,S.L i=[]) → (∀ j,S.R (mnι j)=[]) → MnPostParam S.R M → MnMid S x y M →
      ∃ (v' : HS mnT mnQ bdA Unit) (S' : Stacks mnT bdA) (steps : ℕ),
        steps≤(compactBdDist hP).cost M ∧
        Exec (mnBody mnLb mainP) (compactBdDist hP).distP (mk v S) steps (mk v' S') ∧
        S'.inp=S.inp ∧ S'.out=S.out ∧ S'.L=S.L ∧
        MnDistOut S'.R M (dsW M) (bdE M) (mnσ (blP₀ dsW M) (compactDsyV₀ M)) ∧
        MnMid S' x y M ∧
        ∀ (B : Stacks compactMnT bdA), (∀ i,B.L i=[]) →
          (∀ z : CompactBReg,B.R (compactMnLay (.bc (.inl z)))=[]) →
          compactSynRetunedMainPre M (compactMainFinalStacks S' B) := by
  filter_upwards [(compactBdDist hP).spec] with M hspec
  intro mainP x y v S hL hι hpost hmid
  obtain ⟨v',S',steps,hc,he,hin,hout,hleft,hscratch,hfields,hkeep⟩ :=
    hspec mainP v S hL hι hpost
  have hmid' := mn_mid_keep hmid hkeep
  refine ⟨v',S',steps,hc,he,hin,hout,hleft,hfields,hmid',?_⟩
  intro B hB hblank
  exact compactSynRetunedMainPre_of_distribution M x y S' B
    (fun i => by rw [hleft]; exact hL i) hscratch hfields hmid' hB hblank

end
end IntegerMultBounds.MathlibTM2.Fast.Main
