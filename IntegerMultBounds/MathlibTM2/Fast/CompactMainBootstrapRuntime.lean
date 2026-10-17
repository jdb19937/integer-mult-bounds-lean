module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineFrame
public import IntegerMultBounds.Machine.CompactReservationGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The concrete main bootstrap supplies exactly the original dimension and
guard words required by the actual compact runtime round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Cost
noncomputable section
variable {A : ℕ}

lemma compactMnLayerReg_private (b : CompactBReg) :
    compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl b)))=
      compactMnLay (.bc (.inl b)) := by
  simp only [compactMnLayerReg,reg_inj,reduceCtorEq,ite_false]
  rw [show reg (BReg := CompactHostBReg) (.bc (.inl b))=
    regEquiv CompactHostBReg (.bc (.inl b)) from rfl,Equiv.symm_apply_apply]

theorem compactMainGlobals_runtime_words (N : ℕ) (hN : 2≤N)
    (R : Fin compactMnT → List (Fin (A+4)))
    (h : CompactMainGlobals R (Mult.Sizes.p N) (Mult.Sizes.d N)) :
    R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))))=
        List.replicate (Mult.Sizes.d N) tick ∧
      R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))))=
        List.replicate (CompactReservationGrowth.guard N) tick := by
  rw [compactMnLayerReg_private,compactMnLayerReg_private]
  have hg : CompactReservationGrowth.guard N=4*Nat.clog 2 (Mult.Sizes.p N)+6 := by
    unfold CompactReservationGrowth.guard
    rw [compactCaller_runtime_guardLog hN]
  rw [hg]
  exact h

theorem compactMainGlobals_runtime_lengths (N : ℕ) (hN : 2≤N)
    (R : Fin compactMnT → List (Fin (A+4)))
    (h : CompactMainGlobals R (Mult.Sizes.p N) (Mult.Sizes.d N)) :
    ((R ∘ compactMnLayerReg) (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=
        Mult.Sizes.d N ∧
      ((R ∘ compactMnLayerReg) (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=
        CompactReservationGrowth.guard N := by
  obtain ⟨hd,hg⟩ := compactMainGlobals_runtime_words N hN R h
  constructor <;> simp only [Function.comp_apply,hd,hg,List.length_replicate]

theorem compactMain_io_private (R : Fin compactMnT → List (Fin (A+4)))
    (io : List (Fin (A+4))) (b : CompactBReg) :
    (Function.update R (compactMnRg (.src (.v .io))) io)
      (compactMnLay (.bc (.inl b)))=R (compactMnLay (.bc (.inl b))) :=
  Function.update_of_ne (compactMnRg_ne_lay _ _).symm _ _

/-- Actual compact and direct round outputs retain the initialized original
parameters, so subsequent rounds can reuse the same globals. -/
theorem compactMainGlobals_io_update (R : Fin compactMnT → List (Fin (A+4)))
    (p d : ℕ) (io : List (Fin (A+4))) (h : CompactMainGlobals R p d) :
    CompactMainGlobals (Function.update R (compactMnRg (.src (.v .io))) io) p d := by
  unfold CompactMainGlobals
  rw [compactMain_io_private,compactMain_io_private]
  exact h

end
end IntegerMultBounds.MathlibTM2.Fast.Main
