module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLayer
import IntegerMultBounds.MathlibTM2.Node.CompactLayerGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The actual compact basis estimate supplies the recursive layer budget.
Only geometric packing remains a caller premise, not an arbitrary cost oracle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationShape (Shape)
noncomputable section

theorem compactLayerReady_canonical {shape : Shape} {n o u ρ R₀ r w Ka D j a left right : ℕ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hG : 1≤shape.guard) (hGK : shape.guard+1≤shape.chunk)
    (hrecord : shape.bits+1≤shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (hpack : ∀ i≤j, ∀ a left right
      (layout : CompactRecursiveLayout shape n a (bits u i) ρ left right),
      CompactLayoutPacked layout (rowsAt R₀ i) D)
    (layout : CompactRecursiveLayout shape n a (bits u j) ρ left right) :
    CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord
      (compactLayerBasisBudget (nT CompactBReg) D shape u R₀ n) (j+1) a := by
  apply compactLayerReady_of_layout hu hR₀ hG hGK hrecord _ j _ a left right layout
  intro i hi a left right layout
  let hp := hpack i hi a left right layout
  refine ⟨hp,?_⟩
  intro vv x
  exact compactLayerBasisBudget_covers layout hG hGK hR₀ hrecord hpayload
    (nT CompactBReg) Ka D hp vv x

end
end IntegerMultBounds.MathlibTM2.Cost
