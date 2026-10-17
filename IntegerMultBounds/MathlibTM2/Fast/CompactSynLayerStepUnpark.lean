module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepTopRegs
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepWires
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundPark
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundRest
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundCompose
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Concrete configuration removal and restoration after the compact top call. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactSynLayerUnpark : Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynDropCfg (.seq compactSynUnstash compactSynRestDown)

theorem compactSynLayerUnpark_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum))
    (hv : SynV v es ℓ K W l h L) (ρ working : ℕ) (pfs cfg : List ℕ)
    (hlen : cfg.length=10) (io P₀ : List (Fin (A+4))) :
    LayRuns body compactSynLayerUnpark
      (compactSynParkedFile R io (synStkW v blank synXS ++ blank :: P₀) es.sum (2^l) working K ρ cfg pfs)
      (embExt compactLegacyReg (synG (synIdle io P₀) v)
        (compactSynParkedFile R io (synStkW v blank synXS ++ blank :: P₀) es.sum (2^l) working K ρ cfg pfs))
      (((2*(topRec cfg : List (Fin (A+4))).length+11)+(2*(topRec cfg : List (Fin (A+4))).length+2))+
        ((synStashCostW v synXS+1)+synRestDownCost es.sum (2^l) working K ρ (topRec pfs : List (Fin (A+4))).length)) := by
  let park := synStkW v blank synXS ++ blank :: P₀
  let RF := synRestFile (synIdle io P₀) es.sum (2^l) working K ρ (topRec pfs)
  have hup (X : List (Fin (A+4))) : Function.update RF (lreg .park) X=
      synRestFile (synIdle io X) es.sum (2^l) working K ρ (topRec pfs) := by
    dsimp only [RF]
    rw [synRestFile_update (by simp),synIdle_update_park]
  have hclr : synClrW v synXS=(fun _ => []) := by
    funext x
    by_cases hx : x∈synXS
    · simp [synClrW,hx]
    · by_cases hcf : x=.p .cf
      · subst x; simp [synClrW,synXS,hv.hcf]
      · have hh := compactSynParkedW_empty v es ℓ K W l h L hv [] x
        simpa [synClrW,hx,Function.update_of_ne,hcf] using hh
  have e₁ := compactSynDropCfg_runs body
    (synRestFile (synIdle io (topRec cfg ++ park)) es.sum (2^l) working K ρ (topRec pfs))
    (fun _ => []) cfg park hlen (by simp [synRestFile,synIdle,lreg]) rfl
  have e₂ := compactSynUnstash_runs body RF v P₀ hv.hblank
  have e₃ := compactSynRestDown_runs body (synIdle io P₀) v es.sum (2^l) working K ρ (topRec pfs)
    (synIdle_rest io P₀)
  rw [hclr,hup,hup] at e₂
  have hreset : Function.update
      (synRestFile (synIdle io (topRec cfg ++ park)) es.sum (2^l) working K ρ (topRec pfs))
      (lreg .park) park=synRestFile (synIdle io park) es.sum (2^l) working K ρ (topRec pfs) := by
    rw [synRestFile_update (by simp),synIdle_update_park]
  rw [hreset] at e₁
  exact (e₁.seq (e₂.seq e₃)).layRuns _ (embExt_comp_e compactLegacyReg_injective _ _)

end
end IntegerMultBounds.MathlibTM2.Fast
