module

public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProc
public import IntegerMultBounds.MathlibTM2.Node.CompactRegisterEmbedding
public import IntegerMultBounds.MathlibTM2.Host.Embed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Placement of the complete recursive compact layer beside the retained legacy workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {Q A Ka : ℕ} {U P : Type}

/-- Only the compact half of the private bank has a rest requirement. The entire
legacy half may retain arbitrary data, which the embedded execution preserves. -/
def compactHostBasisRest (shape : Shape) (o r : ℕ) :
    CompactHostBReg → List (Fin (A+4)) → Prop
  | .inl x, l => compactBasisRest shape o r x l
  | .inr _, _ => True

lemma compactLayer_parState {j u K ρ a L rows n w rw : ℕ}
    {S : Stacks (nT CompactHostBReg) A}
    (h : ParState S.R j u K ρ a L rows n w rw) :
    ParState (embStk compactLayerReg S).R j u K ρ a L rows n w rw := by
  intro x
  have hx := h (compactMapRegName Sum.inl x)
  cases x <;> first
    | exact trivial
    | simpa only [parSpec,embStk,Function.comp_apply,compactLayerReg,
    compactMapReg_reg,compactMapRegName] using hx

lemma compactLayer_rest {shape : Shape} {o n r w : ℕ}
    {S : Stacks (nT CompactHostBReg) A}
    (h : Rest (compactHostBasisRest shape o r) n r w S.R) :
    Rest (compactBasisRest shape o r) n r w (embStk compactLayerReg S).R := by
  intro x
  have hx := h (compactMapRegName Sum.inl x)
  cases x <;> first
    | exact trivial
    | simpa only [restSpec,embStk,Function.comp_apply,compactLayerReg,
    compactMapReg_reg,compactMapRegName,compactHostBasisRest] using hx

/-- Generic frame transport, proved before specializing either register count. -/
theorem compactExec_placed_frame {T T' : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e)
    {body : P → Pr P T Q A U} {body' : P → Pr P T' Q A U}
    (hbody : ∀ f, body' f=embProg e id (body f))
    {cp : Pr P T Q A U} {v : HS T' Q A U} {S : Stacks T' A}
    {v₁ : HS T Q A U} {c : ℕ} {x : Fin T} {out : List (Fin (A+4))}
    (hu : v₁.user=(embDn e v).user)
    (hexec : Exec body cp (mk (embDn e v) (embStk e S)) c
      (mk v₁ {embStk e S with R := Function.update (embStk e S).R x out})) :
    ∃ v₂ : HS T' Q A U, v₂.user=v.user ∧
      Exec body' (embProg e id cp) (mk v S) c
        (mk v₂ {S with R := Function.update S.R (e x) out}) := by
  obtain ⟨v₂,_,hu₂,he₂⟩ := exec_emb_ovr (e := e) (ι := id) (body := body) (body' := body')
    he hbody hexec v rfl S rfl
  rw [embOvr_updR he,embOvr_stk] at he₂
  exact ⟨v₂,hu₂.trans hu,he₂⟩

/-- Lift a checked compact call through the register embedding. The target table may
contain additional procedures, provided the source table is placed at the same names. -/
theorem compactCallSpec_placed
    {body : P → Pr P (nT CompactBReg) Q A U}
    {body' : P → Pr P (nT CompactHostBReg) Q A U}
    (hbody : ∀ f, body' f=embProg compactLayerReg id (body f))
    {cp : Pr P (nT CompactBReg) Q A U} {shape : Shape} {o R₀ j u K ρ a L n r w cc : ℕ}
    {ds : ComplexFramedExecution.Directions}
    {hfit : ∀ i<bits u j, a+ρ+K*i<n}
    (hc : CallSpec body cp (compactBasisRest shape o r) ds R₀ j u K ρ a L n r w hfit cc) :
    CallSpec body' (embProg compactLayerReg id cp) (compactHostBasisRest shape o r)
      ds R₀ j u K ρ a L n r w hfit cc := by
  intro Z v S hL hpar hrest hio
  obtain ⟨v₁,c,hu,hcost,hexec⟩ := hc Z (embDn compactLayerReg v) (embStk compactLayerReg S)
    (fun y => hL (compactLayerReg y)) (compactLayer_parState hpar) (compactLayer_rest hrest)
    (by simpa only [embStk,Function.comp_apply,compactLayerReg_io] using hio)
  obtain ⟨v₂,hu₂,he₂⟩ := compactExec_placed_frame compactLayerReg compactLayerReg_injective
    hbody hu hexec
  rw [compactLayerReg_io] at he₂
  exact ⟨v₂,c,hu₂,hcost,he₂⟩

/-- The embedded recursive table on the shared host. -/
def compactPlacedLayerTable (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) : LProc → Pr LProc (nT CompactHostBReg) Q (prime+Ka) U :=
  fun p => embProg compactLayerReg id (compactLayerTable hQ ds p)

/-- Closed concrete layer call on the union host. Its cost is unchanged by placement,
and every stack except the output stream is preserved, including the legacy private bank. -/
theorem compactPlacedLayer_callSpec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime+Ka)
    (hA9 : 9^4 ≤ prime+Ka+4) (hNW : NW ≤ prime+Ka+4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2*gateBound g+1)^(2*(gateWires g).length) ≤ prime+Ka+4)
    {shape : Shape} {u ρ R₀ n o r w D : ℕ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (budget : CompactBasisBudget) (j : ℕ) (hTw : ∀ i<j, expZ u ds i ≤ w) (a : ℕ)
    (hready : CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget j a)
    (hfit : ∀ i<bits u j, (o+a)+ρ+shape.chunk*i<o+n)
    (hfitL : (o+a)+shape.chunk*bits u j ≤ o+n) :
    CallSpec (compactPlacedLayerTable (Ka := Ka) (U := U) hQ ds) (.call .layer)
      (compactHostBasisRest shape o r) ds R₀ j u shape.chunk ρ (o+a) (shape.chunk*bits u j)
      (o+n) r w hfit (compactLayerCost ds u shape.chunk ρ R₀ n o r w budget j a) :=
  compactCallSpec_placed (fun _ => rfl)
    (compactLayer_callSpec hQ ds hA hA9 hNW hgate hr hw hu hR₀ hG hGK hrecord hpayload
      budget j hTw a hready hfit hfitL)

end
end IntegerMultBounds.MathlibTM2.LayerMachine
