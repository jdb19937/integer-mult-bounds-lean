module

public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Derive recursive admissibility from local packing and basis bounds, using shared child geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- A uniform local geometric estimate suffices for the entire recursion. All descendant
layouts are constructed from the parent layout; no leaf layout is constructed or required. -/
theorem compactLayerReady_of_layout {shape : Shape} {n o u ρ R₀ r w Ka D : ℕ}
    (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀) (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (budget : CompactBasisBudget) :
    ∀ j,
    (∀ i ≤ j, ∀ a left right (layout : CompactRecursiveLayout shape n a (bits u i) ρ left right),
      ∃ hp : CompactLayoutPacked layout (rowsAt R₀ i) D,
      ∀ vv x, compactFactorBasisCost layout hG hGK (rowsAt_pos hR₀ i) hrecord D hp
        (nT CompactBReg) Ka o r w vv x ≤ budget i a vv x) →
    ∀ a left right, CompactRecursiveLayout shape n a (bits u j) ρ left right →
      CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget (j+1) a := by
  intro j
  induction j with
  | zero =>
      intro hlocal a left right layout
      obtain ⟨hp,hb⟩ := hlocal 0 (by omega) a left right layout
      exact ⟨left,right,layout,hp,hb,fun _ => trivial⟩
  | succ j ih =>
      intro hlocal a left right layout
      obtain ⟨hp,hb⟩ := hlocal (j+1) (by omega) a left right layout
      refine ⟨left,right,layout,hp,hb,?_⟩
      intro p
      exact ih (fun i hi => hlocal i (by omega)) _ _ _
        (layout.child p (bits u j) (bits_pos hu j) rfl)

end
end IntegerMultBounds.MathlibTM2.LayerMachine
