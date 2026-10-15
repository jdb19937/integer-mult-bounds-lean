module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopsContract
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialContract

/-! The actual distributed transform parameters execute both hybrid scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter
noncomputable section

theorem compactSynInitialLoops_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (mainP : MnPr (prime+mnKa)) (fwd : Bool),
    CompactSynLoopContract (mnBody mnLb mainP) Cost.brDirs M (dsyEs M)
      (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) fwd := by
  filter_upwards [compactSynInitialContract_eventually,compactSynInitialGeometry_eventually]
    with M hLayer hgeometry
  intro mainP fwd
  exact compactSynLoopsContract_of_layer (mnBody mnLb mainP) Cost.brDirs (mn_body_lay mainP)
    (by have := mnKa_alpha; omega) (hLayer mainP) hgeometry.numerator fwd

end
end IntegerMultBounds.MathlibTM2.Fast.Main
