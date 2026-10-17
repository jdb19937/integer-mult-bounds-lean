module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced
public import IntegerMultBounds.MathlibTM2.Fast.SynRound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Concrete parking, configuration pushing/popping and restoration stages on
the union host. The disjoint compact bank is preserved by call-free placement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactSynStash : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim)
    (synStash (lreg .park) blank (synXS.map sreg) : Pr Empty _ _ _ _)

theorem compactSynStash_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4))) :
    CompactPlacedRuns body compactSynStash (synG R v)
      (synG (Function.update R (lreg .park) (synStkW v blank synXS ++ blank :: R (lreg .park)))
        (synClrW v synXS)) (synStashCostW v synXS+1) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_synStash (fun f : Empty => f.elim) (R := R) (v := v) (lreg_out (by simp))
      blank synXS synXS_nodup) vbig S hL hR

def compactSynUnstash : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim)
    (synUnstash (lreg .park) blank (synXS.map sreg) : Pr Empty _ _ _ _)

theorem compactSynUnstash_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (P₀ : List (Fin (A+4))) (hblank : ∀ x∈synXS,blank∉v x) :
    CompactPlacedRuns body compactSynUnstash
      (synG (Function.update R (lreg .park) (synStkW v blank synXS ++ blank :: P₀)) (synClrW v synXS))
      (synG (Function.update R (lreg .park) P₀) v) (synStashCostW v synXS+1) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_synUnstash (fun f : Empty => f.elim) (R := R) (v := v) (lreg_out (by simp))
      blank synXS P₀ synXS_nodup hblank) vbig S hL hR

def compactSynPushCfg : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim)
    (moveR (sreg (.p .cf)) (lreg .park) id : Pr Empty _ _ _ _)

theorem compactSynPushCfg_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (cfg : List ℕ) (hcf : v (.p .cf)=(topRec cfg).reverse) :
    CompactPlacedRuns body compactSynPushCfg (synG R v)
      (synG (Function.update R (lreg .park) (topRec cfg ++ R (lreg .park)))
        (Function.update v (.p .cf) [])) (2*(topRec cfg : List (Fin (A+4))).length+2) := by
  intro vbig S hL hR
  have hh := so_moveWO (Q := Q) (U := U) (fun f : Empty => f.elim) (R := R) (v := v)
    (a := .p .cf) (o := lreg .park) (lreg_out (by simp))
  rw [hcf,List.reverse_reverse,List.length_reverse] at hh
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body hh vbig S hL hR

def compactSynDropCfgCore : Pr P (nT SXReg) Q A U :=
  .seq (topSkips (lreg .park) (sreg (.s 30)) (sreg (.s 31)) 10) (uclear (sreg (.s 30)))

theorem sg_compactSynDropCfg (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (cfg : List ℕ) (P₀ : List (Fin (A+4))) (hlen : cfg.length=10)
    (hpark : R (lreg .park)=topRec cfg++P₀) (h30 : v (.s 30)=[]) :
    LayRuns body compactSynDropCfgCore (synG R v)
      (synG (Function.update R (lreg .park) P₀) v)
      ((2*(topRec cfg : List (Fin (A+4))).length+11)+(2*(topRec cfg : List (Fin (A+4))).length+2)) := by
  have ht : cfg.take 10=cfg := List.take_of_length_le hlen.le
  have hd : cfg.drop 10=[] := List.drop_eq_nil_iff.mpr hlen.le
  have e₁ := so_topSkips body (R := R) (v := v) (o := lreg .park) (b := .s 30) (c := .s 31)
    (lreg_out (by simp)) (by decide) 10 cfg P₀ hlen.ge hpark
  simp only [ht,hd,topRec_nil,List.nil_append,h30,List.append_nil] at e₁
  have e₂ := sg_uclear body (R := Function.update R (lreg .park) P₀)
    (v := Function.update v (.s 30) (topRec cfg).reverse) (a := .s 30)
  refine lr_weaken body (e₁.seq e₂) ?_ ?_
  · rw [Function.update_idem,←h30,Function.update_eq_self]
  · simp

def compactSynDropCfg : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim) (compactSynDropCfgCore (P := Empty))

theorem compactSynDropCfg_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (cfg : List ℕ) (P₀ : List (Fin (A+4))) (hlen : cfg.length=10)
    (hpark : R (lreg .park)=topRec cfg++P₀) (h30 : v (.s 30)=[]) :
    CompactPlacedRuns body compactSynDropCfg (synG R v)
      (synG (Function.update R (lreg .park) P₀) v)
      ((2*(topRec cfg : List (Fin (A+4))).length+11)+(2*(topRec cfg : List (Fin (A+4))).length+2)) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_compactSynDropCfg (fun f : Empty => f.elim) R v cfg P₀ hlen hpark h30) vbig S hL hR

end
end IntegerMultBounds.MathlibTM2.Fast
