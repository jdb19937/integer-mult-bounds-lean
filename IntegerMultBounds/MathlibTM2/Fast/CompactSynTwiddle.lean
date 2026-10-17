module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynDirect
import IntegerMultBounds.MathlibTM2.Fast.CompactMainLegacyRuns
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The original twiddle step on the actual expanded main machine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

def compactSynTwiddle (fwd : Bool) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactMainStage (embProg mnLayE MnProc.lay (synTwStep fwd))

theorem compactSynTwiddle_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
      (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (fwd : Bool) (hA : 5≤prime+Ka) {es : List ℕ} {ℓ K W l h : ℕ}
    (hW : 1≤W) (hhl : h≤l) (L : Equiv.Perm (Fin es.sum))
    (v : SynW → List (Fin (prime+Ka+4))) (hv : SynV v es ℓ K W l h L)
    (P₀ : List (Fin (prime+Ka+4))) (Y : ℕ → Fin (2^l) → GaussianInt)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v) :
    LayRuns (compactMainBody legacy ds) (compactSynTwiddle fwd) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (fun m => twShiftZ (twEx fwd es l h (twGat (twPosL L) es.sum m)) (Y m)))))
      (1+synTwCost es l W h) := by
  have he := sg_synTwStep (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) fwd hA hW hhl L
    (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v Y
    (by simp [synIdle,lreg]) hv.hpz hv.htw hv.hN hv.hw hv.hr hv.hlr hv.hh hv.hes hv.hD
    (hv.hs 2) (hv.hs 3) (hv.hs 23) (hv.hs 25) (hv.hs 26) (hv.hs 27) (hv.hs 28)
  rw [←synG_update_out (lreg_out (by simp))] at he
  have ei := compactLegacyLayer_runs legacy (compactMainNativeTable ds)
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) hbody he R hR
  rw [compactLegacyLayer_io_restore _ R _ hR] at ei
  exact ei

end
end IntegerMultBounds.MathlibTM2.Fast.Main
