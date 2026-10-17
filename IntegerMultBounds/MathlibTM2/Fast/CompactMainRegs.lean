module

public import IntegerMultBounds.MathlibTM2.Fast.MainRegs
public import IntegerMultBounds.MathlibTM2.Node.CompactRegisterEmbedding
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! A fixed expanded main host for the compact transform. Existing main-stage
registers embed injectively; the transform shares the actual source-array tape.
This module supplies placement, not the new multiplier execution theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node
noncomputable section

abbrev CompactMnAll := MnR ⊕ Fin 64 ⊕ LReg CompactHostBReg

def compactMnT : ℕ := Fintype.card CompactMnAll

def compactMnEq : CompactMnAll ≃ Fin compactMnT := Fintype.equivFin CompactMnAll

def compactMnRg (x : MnR) : Fin compactMnT := compactMnEq (.inl x)

def compactMnLay (x : LReg CompactHostBReg) : Fin compactMnT := compactMnEq (.inr (.inr x))

lemma compactMnRg_injective : Function.Injective compactMnRg :=
  fun _ _ h => Sum.inl_injective (compactMnEq.injective h)

lemma compactMnLay_injective : Function.Injective compactMnLay :=
  fun _ _ h => Sum.inr_injective (Sum.inr_injective (compactMnEq.injective h))

lemma compactMnRg_ne_lay (x : MnR) (y : LReg CompactHostBReg) :
    compactMnRg x ≠ compactMnLay y := by
  intro h
  have := compactMnEq.injective h
  cases this

/-- Every original stage and multiplier register keeps its named role. -/
def compactMnLegacyName : MnAll → CompactMnAll :=
  Sum.map id (Sum.map id (compactMapRegName Sum.inr))

lemma compactMnLegacyName_injective : Function.Injective compactMnLegacyName := by
  apply Sum.map_injective.mpr
  refine ⟨Function.injective_id, ?_⟩
  exact Sum.map_injective.mpr ⟨Function.injective_id,compactMapRegName_injective Sum.inr_injective⟩

def compactMnLegacyReg (i : Fin mnT) : Fin compactMnT :=
  compactMnEq (compactMnLegacyName (mnEq.symm i))

lemma compactMnLegacyReg_injective : Function.Injective compactMnLegacyReg :=
  compactMnEq.injective.comp (compactMnLegacyName_injective.comp mnEq.symm.injective)

@[simp] lemma compactMnLegacyReg_rg (x : MnR) :
    compactMnLegacyReg (mnRg x) = compactMnRg x := by
  simp only [compactMnLegacyReg,mnRg,Equiv.symm_apply_apply,compactMnLegacyName,compactMnRg]
  rfl

@[simp] lemma compactMnLegacyReg_lay (x : LReg SXReg) :
    compactMnLegacyReg (mnLay x) = compactMnLay (compactMapRegName Sum.inr x) := by
  simp only [compactMnLegacyReg,mnLay,Equiv.symm_apply_apply,compactMnLegacyName,compactMnLay]
  rfl

/-- The compact host acts on the same source-array tape as the original main. -/
def compactMnLayerReg (i : Fin (nT CompactHostBReg)) : Fin compactMnT :=
  if i = reg (BReg := CompactHostBReg) .io then compactMnRg (.src (.v .io))
  else compactMnLay ((regEquiv CompactHostBReg).symm i)

@[simp] lemma compactMnLayerReg_io :
    compactMnLayerReg (reg (BReg := CompactHostBReg) .io) = compactMnRg (.src (.v .io)) := by simp only [compactMnLayerReg,ite_true]

lemma compactMnLayerReg_injective : Function.Injective compactMnLayerReg := by
  intro i j h
  by_cases hi : i = reg (BReg := CompactHostBReg) .io
  · by_cases hj : j = reg (BReg := CompactHostBReg) .io
    · exact hi.trans hj.symm
    · have hh : compactMnRg (.src (.v .io)) = compactMnLay ((regEquiv CompactHostBReg).symm j) := by
        simpa only [compactMnLayerReg,hi,ite_true,ite_false,hj] using h
      exact False.elim (compactMnRg_ne_lay _ _ hh)
  · by_cases hj : j = reg (BReg := CompactHostBReg) .io
    · have hh : compactMnLay ((regEquiv CompactHostBReg).symm i) = compactMnRg (.src (.v .io)) := by
        simpa only [compactMnLayerReg,hj,ite_true,ite_false,hi] using h
      exact False.elim (compactMnRg_ne_lay _ _ hh.symm)
    · have hh : compactMnLay ((regEquiv CompactHostBReg).symm i) =
          compactMnLay ((regEquiv CompactHostBReg).symm j) := by
        simpa only [compactMnLayerReg,hi,hj,ite_false] using h
      exact (regEquiv CompactHostBReg).symm.injective (compactMnLay_injective hh)

/-- Old and new transform placements share exactly the running source stream. -/
lemma compactMn_stream_shared :
    compactMnLegacyReg (mnLayE mnLio) =
      compactMnLayerReg (reg (BReg := CompactHostBReg) .io) := by
  rw [mnLayE_io,compactMnLegacyReg_rg,compactMnLayerReg_io]

/-- Existing main stages cannot touch the newly reserved compact private bank. -/
lemma compactMnLegacyReg_ne_private (i : Fin mnT) (b : CompactBReg) :
    compactMnLegacyReg i ≠ compactMnLay (.bc (.inl b)) := by
  intro h
  have hh := compactMnEq.injective h
  change compactMnLegacyName (mnEq.symm i) = .inr (.inr (.bc (.inl b))) at hh
  generalize mnEq.symm i = x at hh
  rcases x with x | x
  · cases hh
  · rcases x with j | x
    · cases hh
    · have hm : compactMapRegName Sum.inr x = .bc (.inl b) :=
        Sum.inr_injective (Sum.inr_injective hh)
      cases x <;> simp only [compactMapRegName] at hm <;> cases hm

/-- Original precision can be copied from the actual unary input-stage register. -/
lemma compactMn_precision_source :
    compactMnLegacyReg (mnRg (.io .dpn)) = compactMnRg (.io .dpn) := compactMnLegacyReg_rg _

end
end IntegerMultBounds.MathlibTM2.Fast.Main
