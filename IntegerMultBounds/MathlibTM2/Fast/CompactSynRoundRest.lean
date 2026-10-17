module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced
public import IntegerMultBounds.MathlibTM2.Fast.SynRound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Call-free round staging on the union host, preserving its compact bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactSynRestUp : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim) (synRestUp (P := Empty))

theorem compactSynRestUp_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4)))
    (N r w' K ρ : ℕ) (pr : List (Fin (A + 4)))
    (hRo : ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], Ro (lreg x) = [])
    (hw2 : v (.p .w2) = List.replicate w' tick) (hN : (v (.p .N)).length = N)
    (hr : (v (.p .r)).length = r) (hkh : v (.p .kh) = List.replicate K tick)
    (hrh : v (.p .rh) = List.replicate ρ tick) (hpr : v (.p .pr) = pr)
    (h2 : v (.s 2) = []) (h3 : v (.s 3) = []) (h4 : v (.s 4) = []) :
    CompactPlacedRuns body compactSynRestUp (synG Ro v)
      (synG (synRestFile Ro N r w' K ρ pr) (Function.update (Function.update (Function.update
        (Function.update v (.p .kh) []) (.p .rh) []) (.p .pr) []) (.p .w2) []))
      (synRestUpCost N r w' K ρ pr.length) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (lr_synRestUp (fun f : Empty => f.elim) Ro v N r w' K ρ pr hRo hw2 hN hr hkh hrh hpr h2 h3 h4) vbig S hL hR

def compactSynRestDown : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim) (synRestDown (P := Empty))

theorem compactSynRestDown_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4)))
    (N r w' K ρ : ℕ) (pr : List (Fin (A + 4)))
    (hRo : ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], Ro (lreg x) = []) :
    CompactPlacedRuns body compactSynRestDown (synG (synRestFile Ro N r w' K ρ pr) v) (synG Ro v)
      (synRestDownCost N r w' K ρ pr.length) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (lr_synRestDown (fun f : Empty => f.elim) Ro v N r w' K ρ pr hRo) vbig S hL hR

end
end IntegerMultBounds.MathlibTM2.Fast
