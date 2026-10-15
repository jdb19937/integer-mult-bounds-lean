module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialGeometry

/-! The actual distributed transform meets the concrete hybrid layer contract
with the existing finite alphabet and canonical network directions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter
noncomputable section

theorem compactSynInitialContract_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ mainP : MnPr (prime+mnKa),
    CompactSynLayerContract (mnBody mnLb mainP) Cost.brDirs M (dsyEs M)
      (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) := by
  have hA : 21≤prime+mnKa := by have := mnKa_alpha; omega
  filter_upwards [compactSynLayerContract_eventually hA (embKa_hA9 mnKa_le)
    (embKa_hNW mnKa_le),compactSynInitialGeometry_eventually] with M hexec hgeometry
  intro mainP
  with_reducible exact (hexec Cost.brDirs Cost.br_directions_realizes (embKa_gate mnKa_le)
    (mnBody mnLb mainP) (mn_body_lay mainP) (dsyEs M) (Mult.Sizes.ℓ M) (dsW M)
    (Mult.Sizes.ℓ M) (Mult.Sizes.p M) hgeometry)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
