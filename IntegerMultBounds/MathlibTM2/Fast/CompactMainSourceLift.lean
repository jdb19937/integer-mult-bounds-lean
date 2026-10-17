module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainStableFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcMachine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Source-stage execution on the full main register file, with precision read from that file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

lemma compactMainSourceRuns {M c : ℕ} {E E' : SrcF 6 (prime+mnKa)}
    {body : CompactMainProc → CompactMnPr CompactMainProc (prime+mnKa)}
    {prog : CompactMnPr CompactMainProc (prime+mnKa)}
    (g : MnR → List (Fin (prime+mnKa+4))) (hp : (g (.io .dpn)).length=Mult.Sizes.p M)
    (h : SrcRuns body compactSrcM.rg compactSrcM.ι
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) prog E.get E'.get c) :
    SrcRuns body compactMnRg compactSrcM.ι (compactMainStablePre M) prog
      (mnGlob E g) (mnGlob E' g) c := by
  have hrg : compactSrcM.rg=(fun x => compactMnRg (.src x)) := by
    funext x
    exact compactSrcM_rg x
  rw [hrg] at h
  have hl := SrcRuns.lift compactMnRg_injective mn_src_inj h (mnGlob E g) (fun _ => rfl)
  rw [mn_extend_src] at hl
  intro v S hc hpre hS
  have hp' : (S.R (compactMnRg (.io .dpn))).length=Mult.Sizes.p M := by
    rw [hS]
    exact hp
  exact hl v S hc (compactMainStablePre_entry M S hpre hp') hS

end
end IntegerMultBounds.MathlibTM2.Fast.Main
