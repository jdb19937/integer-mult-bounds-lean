module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineFrame
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisCleanup
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Original globals and charged cleanup at a transform boundary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactMnBootstrapDst_guard : compactMnBootstrapDst 0=compactMnLay (.bc (.inl (.work 14))) := by
  rw [compactMnBootstrapDst_eq,compactGlobalBootstrapDst_guard]
  simp only [compactMnLayerReg,reg_inj,reduceCtorEq,ite_false]
  rw [show reg (BReg:=CompactHostBReg) (.bc (.inl (.work 14)))=
    regEquiv CompactHostBReg (.bc (.inl (.work 14))) from rfl,Equiv.symm_apply_apply]

lemma compactMnBootstrap_globals (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :
    CompactMainGlobals (compactMnBootstrapFinal R p d) p d := by
  rw [compactMnBootstrapFinal_base]
  have h := compactSetupUpdate7_get compactMnBootstrapDst compactMnBootstrapDst_injective
    R (compactGlobalBootstrapValues p d)
  exact ⟨by simpa only [compactMnBootstrapDst_depth,compactGlobalBootstrapValues,
    Matrix.cons_val_one,Matrix.cons_val_zero] using h 1,
    by simpa only [compactMnBootstrapDst_guard,compactGlobalBootstrapValues,
      Matrix.cons_val_zero] using h 0⟩

/-- At a transform boundary, clear the bootstrap destinations for the next transform. -/
def compactMnBootstrapCleanup : Pr P compactMnT Q A U := compactClear7 compactMnBootstrapDst

theorem compactMnBootstrapCleanup_runs (body : P → Pr P compactMnT Q A U)
    (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ)
    (hz : ∀ i,R (compactMnBootstrapDst i)=[]) :
    LayRuns body compactMnBootstrapCleanup (compactMnBootstrapFinal R p d) R
      (compactClear7Cost (compactGlobalBootstrapValues p d)) := by
  rw [compactMnBootstrapFinal_base]
  exact compactClear7_runs body compactMnBootstrapDst compactMnBootstrapDst_injective R
    (compactGlobalBootstrapValues p d) hz

end
end IntegerMultBounds.MathlibTM2.Fast.Main
