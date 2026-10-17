module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransport
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Recover original depth from its initial transform predecessor, preserving the main frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

private lemma bootstrapEraseCopies {T : ℕ} (R : Fin T → List (Fin (A+4)))
    (e : Fin 7 → Fin T) (values : Fin 7 → ℕ) (p d : ℕ) :
    compactSetupUpdate7 (Function.update (Function.update R (e 2) (List.replicate p tick))
      (e 3) (List.replicate d tick)) e values=compactSetupUpdate7 R e values := by
  funext z
  by_cases h2 : z=e 2 <;> by_cases h3 : z=e 3 <;>
    simp [compactSetupUpdate7,Function.update_apply,h2,h3]

lemma compactMnBootstrapFinal_base (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :
    compactMnBootstrapFinal R p d=compactSetupUpdate7 R compactMnBootstrapDst (compactGlobalBootstrapValues p d) := by
  unfold compactMnBootstrapFinal compactMnBootstrapCopied
  rw [←compactMnBootstrapDst_p,←compactMnBootstrapDst_d]
  exact bootstrapEraseCopies R compactMnBootstrapDst (compactGlobalBootstrapValues p d) p d

lemma compactMnBootstrapDst_depth : compactMnBootstrapDst 1=compactMnLay (.bc (.inl (.work 13))) := by
  rw [compactMnBootstrapDst_eq,compactGlobalBootstrapDst_depth]
  simp only [compactMnLayerReg,reg_inj,reduceCtorEq,ite_false]
  rw [show reg (BReg:=CompactHostBReg) (.bc (.inl (.work 13)))=
    regEquiv CompactHostBReg (.bc (.inl (.work 13))) from rfl,Equiv.symm_apply_apply]

private lemma bootstrapPushDepth {T : ℕ} (R : Fin T → List (Fin (A+4)))
    (e : Fin 7 → Fin T) (he : Function.Injective e) (g d : ℕ) (hd : 0<d) :
    Function.update (compactSetupUpdate7 R e ![g,d-1,0,0,0,0,0]) (e 1)
      (tick::compactSetupUpdate7 R e ![g,d-1,0,0,0,0,0] (e 1))=
      compactSetupUpdate7 R e ![g,d,0,0,0,0,0] := by
  have h1 : compactSetupUpdate7 R e ![g,d-1,0,0,0,0,0] (e 1)=List.replicate (d-1) tick :=
    compactSetupUpdate7_get e he R _ 1
  have hw : tick::List.replicate (d-1) (tick : Fin (A+4))=List.replicate d tick := by
    rw [←List.replicate_succ]
    congr 1
    omega
  rw [h1,hw]
  funext z
  by_cases hz : z=e 1
  · subst z; simp [compactSetupUpdate7,he.eq_iff]
  · simp [compactSetupUpdate7,Function.update_apply,hz]

/-- One tick on the retained copied predecessor gives exactly the original-d bootstrap file. -/
lemma compactMnBootstrap_original_depth_file
    (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) (hd : 0<d) :
    Function.update (compactMnBootstrapFinal R p (d-1)) (compactMnLay (.bc (.inl (.work 13))))
      (tick::compactMnBootstrapFinal R p (d-1) (compactMnLay (.bc (.inl (.work 13)))))=
      compactMnBootstrapFinal R p d := by
  rw [←compactMnBootstrapDst_depth,compactMnBootstrapFinal_base,compactMnBootstrapFinal_base]
  exact bootstrapPushDepth R compactMnBootstrapDst compactMnBootstrapDst_injective (4*Nat.clog 2 p+6) d hd

/-- Initialized original inputs remain present across any transported legacy stage. -/
def CompactMainGlobals (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) : Prop :=
  R (compactMnLay (.bc (.inl (.work 13))))=List.replicate d tick ∧
  R (compactMnLay (.bc (.inl (.work 14))))=List.replicate (4*Nat.clog 2 p+6) tick

lemma compactMainGlobals_legacy (S₁ : Stacks mnT A) (S : Stacks compactMnT A) (p d : ℕ)
    (h : CompactMainGlobals S.R p d) : CompactMainGlobals (compactMainFinalStacks S₁ S).R p d := by
  exact ⟨(compactMainFinalStacks_private S₁ S (.work 13)).2.trans h.1,
    (compactMainFinalStacks_private S₁ S (.work 14)).2.trans h.2⟩

end
end IntegerMultBounds.MathlibTM2.Fast.Main
