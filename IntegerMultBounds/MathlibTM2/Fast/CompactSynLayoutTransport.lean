module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialLoops

/-! Layout programs retain their original stream contracts on the expanded host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

def compactSynLayout (p : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) :
    CompactMnPr CompactMainProc (prime+Ka) := compactMainStage (embProg mnLayE MnProc.lay p)

theorem compactSynLayout_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    {p : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit}
    {io out park : List (Fin (prime+Ka+4))} {v : SynW → List (Fin (prime+Ka+4))} {c : ℕ}
    (h : LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) p
      (synG (synIdle io park) v) (synG (synIdle out park) v) c)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle io park) v) :
    LayRuns (compactMainBody legacy ds) (compactSynLayout p) R
      (Function.update R (compactMnRg (.src (.v .io))) out) (1+c) := by
  have hout : synG (synIdle out park) v=Function.update (synG (synIdle io park) v) mnLio out := by
    rw [synG_update_out (lreg_out (by simp)),synIdle_update_io]
  rw [hout] at h
  have he := compactLegacyLayer_runs legacy (compactMainNativeTable ds)
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) hbody h R hR
  rw [compactLegacyLayer_io_restore _ R _ hR] at he
  exact he

def compactSynPreReady (M : ℕ) (Pk : List (Fin (prime+Ka+4)) → Prop)
    (v : SynW → List (Fin (prime+Ka+4))) (S : Stacks compactMnT (prime+Ka)) : Prop :=
  (∀ i,S.L i=[]) ∧ CompactSynReady S.R M ∧ ∃ park,Pk park ∧
    compactSynView S.R=synG (synIdle (S.R (compactMnRg (.src (.v .io)))) park) v

end
end IntegerMultBounds.MathlibTM2.Fast.Main
