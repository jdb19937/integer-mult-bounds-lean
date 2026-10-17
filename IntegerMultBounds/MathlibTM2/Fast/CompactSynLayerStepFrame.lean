module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundGlobal
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Full-host execution and temporary source restoration for compact rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- A placed stage is a full-host run with an explicit unchanged background. -/
theorem CompactPlacedRuns.layRuns
    {body : P → Pr P (nT CompactHostBReg) Q A U}
    {p : Pr P (nT CompactHostBReg) Q A U}
    {R₀ R₁ : Fin (nT SXReg) → List (Fin (A+4))} {c : ℕ}
    (h : CompactPlacedRuns body p R₀ R₁ c)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (hR : R ∘ compactLegacyReg=R₀) :
    LayRuns body p R (embExt compactLegacyReg R₁ R) c := by
  intro v S hL hS
  obtain ⟨v',k,hu,hc,he⟩ := h v S (fun i => hL (compactLegacyReg i)) (by rw [hS]; exact hR)
  refine ⟨v',k,hu,hc,Exec.cast he rfl ?_⟩
  apply congrArg (mk v')
  simp only [embOvr,embStk,Stacks.get,embExt_comp,hS]

/-- One outside row is independent of the coefficient multiplicity in `p.r`. -/
def compactSynOutsideRow : Fin (nT CompactHostBReg) :=
  reg (BReg := CompactHostBReg) (.wire (synWire (.ly 0)))

def compactSynOutsideRowPush : Pr P (nT CompactHostBReg) Q A U :=
  synPush compactSynOutsideRow tick

theorem compactSynOutsideRowPush_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (h : R compactSynOutsideRow=[]) :
    LayRuns body compactSynOutsideRowPush R
      (Function.update R compactSynOutsideRow [tick]) 1 := by
  simpa only [compactSynOutsideRowPush,h] using lr_push body (R := R) compactSynOutsideRow tick

/-- Clear the three constructor copies and the temporary outside-row source. -/
def compactSynSourceClear : Pr P (nT CompactHostBReg) Q A U :=
  .seq (.seq (.seq (uclear (compactSynScratch 0)) (uclear (compactSynScratch 1)))
    (uclear (compactSynScratch 7))) (uclear compactSynOutsideRow)

def compactSynSourceClearOut (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) :=
  Function.update (Function.update (Function.update (Function.update R
    (compactSynScratch 0) []) (compactSynScratch 1) []) (compactSynScratch 7) []) compactSynOutsideRow []

theorem compactSynSourceClear_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (d g o : ℕ)
    (hd : (R (compactSynScratch 0)).length=d)
    (hg : (R (compactSynScratch 1)).length=g)
    (ho : (R (compactSynScratch 7)).length=o)
    (hrow : (R compactSynOutsideRow).length=1) :
    LayRuns body compactSynSourceClear R (compactSynSourceClearOut R)
      (((2*d+2)+(2*g+2))+(2*o+2)+4) := by
  have h10 := compactSynScratch_ne (by decide : (1:Fin 32)≠0)
  have h70 := compactSynScratch_ne (by decide : (7:Fin 32)≠0)
  have h71 := compactSynScratch_ne (by decide : (7:Fin 32)≠1)
  have hr (i : Fin 32) : compactSynOutsideRow≠compactSynScratch i := reg_ne (by simp)
  have e := (((lr_uclear body (R := R) (compactSynScratch 0)).seq
    (lr_uclear body (compactSynScratch 1))).seq (lr_uclear body (compactSynScratch 7))).seq
      (lr_uclear body compactSynOutsideRow)
  simpa only [Function.update_of_ne h10,Function.update_of_ne h70,Function.update_of_ne h71,
    Function.update_of_ne (hr 0),Function.update_of_ne (hr 1),Function.update_of_ne (hr 7),
    hd,hg,ho,hrow,compactSynSourceClear,compactSynSourceClearOut,
    Nat.mul_one,Nat.reduceAdd] using e

end
end IntegerMultBounds.MathlibTM2.Fast
