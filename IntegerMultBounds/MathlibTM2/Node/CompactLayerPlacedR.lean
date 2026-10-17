module

public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProcR

/-! Placement of the rounded recursive compact layer beside the retained legacy workspace:
`compactLayerPlaced` for `CallSpecF` and the rounded table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {Q A Ka : ℕ} {U P : Type}

/-- Lift a checked call with a general result through the register embedding. -/
theorem compactCallSpecF_placed
    {body : P → Pr P (nT CompactBReg) Q A U}
    {body' : P → Pr P (nT CompactHostBReg) Q A U}
    (hbody : ∀ f, body' f=embProg compactLayerReg id (body f))
    {cp : Pr P (nT CompactBReg) Q A U} {shape : Shape} {o R₀ j u K ρ a L n r w cc : ℕ}
    {Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n}
    (hc : CallSpecF body cp (compactBasisRest shape o r) R₀ j u K ρ a L n r w Fo cc) :
    CallSpecF body' (embProg compactLayerReg id cp) (compactHostBasisRest shape o r)
      R₀ j u K ρ a L n r w Fo cc := by
  intro Z v S hL hpar hrest hio
  obtain ⟨v₁,c,hu,hcost,hexec⟩ := hc Z (embDn compactLayerReg v) (embStk compactLayerReg S)
    (fun y => hL (compactLayerReg y)) (compactLayer_parState hpar) (compactLayer_rest hrest)
    (by simpa only [embStk,Function.comp_apply,compactLayerReg_io] using hio)
  obtain ⟨v₂,hu₂,he₂⟩ := compactExec_placed_frame compactLayerReg compactLayerReg_injective
    hbody hu hexec
  rw [compactLayerReg_io] at he₂
  exact ⟨v₂,c,hu₂,hcost,he₂⟩

/-- The embedded rounded recursive table on the shared host. -/
def compactPlacedLayerTableR (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) : LProc → Pr LProc (nT CompactHostBReg) Q (prime+Ka) U :=
  fun p => embProg compactLayerReg id (compactLayerTableR hQ ds p)

/-- **The placed rounded layer**: `compactLayerR_exec` on the union host. -/
theorem compactPlacedLayerR_callSpec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime+Ka)
    (hA9 : 9^4 ≤ prime+Ka+4) (hNW : NW ≤ prime+Ka+4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2*gateBound g+1)^(2*(gateWires g).length) ≤ prime+Ka+4)
    {shape : Shape} {u ρ R₀ n o r w D : ℕ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (budget : CompactBasisBudget) (j : ℕ) (hsw : ∀ i<j, scaleR u ds i < w) (a : ℕ)
    (hready : CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget j a)
    (hfit : ∀ i<bits u j, (o+a)+ρ+shape.chunk*i<o+n)
    (hfitL : (o+a)+shape.chunk*bits u j ≤ o+n) :
    CallSpecF (compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds) (.call .layer)
      (compactHostBasisRest shape o r) R₀ j u shape.chunk ρ (o+a) (shape.chunk*bits u j)
      (o+n) r w (layerRW w u ds R₀ j (actMap (o+a) ρ shape.chunk (bits u j) (o+n) hfit))
      (compactLayerCostR ds u shape.chunk ρ R₀ n o r w budget j a) :=
  compactCallSpecF_placed (fun _ => rfl)
    (compactLayerR_exec hQ ds hA hA9 hNW hgate hr hw hu hR₀ hG hGK hrecord hpayload
      budget j hsw a hready hfit hfitL)

end
end IntegerMultBounds.MathlibTM2.LayerMachine
