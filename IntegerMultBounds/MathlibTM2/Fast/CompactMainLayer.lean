module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransport
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepExecution

/-! Canonical compact layer procedures and whole-round placement on the expanded
main machine. The source-array tape is the same tape used by the old stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

private theorem placedLayRuns {T T' Q A : ℕ} {U P P' : Type}
    (e : Fin T → Fin T') (he : Function.Injective e) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f,body' (ι f)=embProg e ι (body f))
    {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (R : Fin T' → List (Fin (A+4))) (hR : R ∘ e=R₀) :
    LayRuns body' (embProg e ι p) R (embExt e R₁ R) c := by
  intro v S hL hS
  obtain ⟨w,k,hu,hc,hex⟩ := h (embDn e v) (embStk e S) (fun i => hL (e i))
    (by change S.R ∘ e=R₀; rw [hS]; exact hR)
  obtain ⟨v',hv,hu',hex'⟩ := exec_emb_ovr he hbody hex v rfl S rfl
  refine ⟨v',k,hu'.trans hu,hc,Exec.cast hex' rfl ?_⟩
  apply congrArg (mk v')
  simp only [embOvr,embStk,Stacks.get,embExt_comp,hS]

def compactMainNativeTable (ds : ComplexFramedExecution.Directions) :
    LProc → CompactMnPr CompactMainProc (prime+Ka) := fun f =>
  embProg compactMnLayerReg compactMainLayerProc
    (compactPlacedLayerTable (Ka := Ka) (U := Unit) compactMnQ_runtime ds f)

def compactMainBody (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) :
    CompactMainProc → CompactMnPr CompactMainProc (prime+Ka) :=
  compactMainTransportTable legacy (compactMainNativeTable ds)

def compactMainChunk (ds : ComplexFramedExecution.Directions) :
    CompactMnPr CompactMainProc (prime+Ka) :=
  embProg compactMnLayerReg compactMainLayerProc (compactSynLayerStep ds)

theorem compactMainBody_layer (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (f : LProc) :
    compactMainBody legacy ds (compactMainLayerProc f)=
      embProg compactMnLayerReg compactMainLayerProc
        (compactPlacedLayerTable (Ka := Ka) (U := Unit) compactMnQ_runtime ds f) := rfl

/-- The concrete combined procedure table preserves any proved compact layer
execution, including its exact time and its off-image main stack frame. -/
theorem compactMainLayer_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    {p : Pr LProc (nT CompactHostBReg) compactMnQ (prime+Ka) Unit}
    {R₀ R₁ : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4))} {c : ℕ}
    (h : LayRuns (compactPlacedLayerTable (Ka := Ka) (U := Unit) compactMnQ_runtime ds) p R₀ R₁ c)
    (R : Fin compactMnT → List (Fin (prime+Ka+4))) (hR : R ∘ compactMnLayerReg=R₀) :
    LayRuns (compactMainBody legacy ds) (embProg compactMnLayerReg compactMainLayerProc p)
      R (embExt compactMnLayerReg R₁ R) c := by
  with_reducible exact (placedLayRuns compactMnLayerReg compactMnLayerReg_injective
    compactMainLayerProc (compactMainBody_layer legacy ds) h R hR)

/-- Restoring every local register except the stream restores the full main
register file except its actual source-array tape. -/
theorem compactMainLayer_io_restore
    (R₀ : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (io : List (Fin (prime+Ka+4))) (hR : R ∘ compactMnLayerReg=R₀) :
    embExt compactMnLayerReg
      (Function.update R₀ (reg (BReg := CompactHostBReg) .io) io) R=
        Function.update R (compactMnRg (.src (.v .io))) io := by
  rw [←hR,←compactEmbExt_update_image compactMnLayerReg compactMnLayerReg_injective,
    embExt_comp,compactMnLayerReg_io]

theorem compactMainChunk_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (R₀ : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
    (R : Fin compactMnT → List (Fin (prime+Ka+4))) (io : List (Fin (prime+Ka+4)))
    (c : ℕ) (hR : R ∘ compactMnLayerReg=R₀)
    (h : LayRuns (compactPlacedLayerTable (Ka := Ka) (U := Unit) compactMnQ_runtime ds)
      (compactSynLayerStep ds) R₀ (Function.update R₀ (reg (BReg := CompactHostBReg) .io) io) c) :
    LayRuns (compactMainBody legacy ds) (compactMainChunk ds) R
      (Function.update R (compactMnRg (.src (.v .io))) io) c := by
  have he := compactMainLayer_runs legacy ds h R hR
  rw [compactMainLayer_io_restore R₀ R io hR] at he
  exact he

end
end IntegerMultBounds.MathlibTM2.Fast.Main
