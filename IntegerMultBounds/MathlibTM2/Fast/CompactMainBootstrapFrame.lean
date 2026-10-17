module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrap
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Original-source preservation and consumed-copy guarantees for the main bootstrap. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

lemma compactMnBootstrapReg_source (x : SynW) (hx : ∀ i : Fin 7,x≠compactBasisOutputWire i) :
    compactMnBootstrapReg (sreg x)=compactMnSyn x := by
  rw [compactMnBootstrapReg,Function.comp_apply,compactBasisSetupReg_source x hx]
  simpa only [sreg_eq,compactLegacyReg,compactMapReg_reg,compactMapRegName] using compactMnSyn_legacy x


lemma compactMnBootstrapDst_injective : Function.Injective compactMnBootstrapDst := by
  intro i j h
  change compactMnLayerReg (compactGlobalBootstrapDst i)=compactMnLayerReg (compactGlobalBootstrapDst j) at h
  exact compactGlobalBootstrapDst_injective (compactMnLayerReg_injective h)

lemma compactMnBootstrapDst_eq (i : Fin 7) :
    compactMnBootstrapDst i=compactMnLayerReg (compactGlobalBootstrapDst i) := rfl

lemma compactMnBootstrapDst_p : compactMnBootstrapDst 2=compactMnSyn (.s 0) := by
  rw [compactMnBootstrapDst_eq,compactGlobalBootstrapDst_p]
  simpa only [sreg_eq,compactLegacyReg,compactMapReg_reg,compactMapRegName] using compactMnSyn_legacy (.s 0)

lemma compactMnBootstrapDst_d : compactMnBootstrapDst 3=compactMnSyn (.s 1) := by
  rw [compactMnBootstrapDst_eq,compactGlobalBootstrapDst_d]
  simpa only [sreg_eq,compactLegacyReg,compactMapReg_reg,compactMapRegName] using compactMnSyn_legacy (.s 1)


def compactMnBootstrapFinal (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :=
  compactSetupUpdate7 (compactMnBootstrapCopied R p d) compactMnBootstrapDst (compactGlobalBootstrapValues p d)

/-- The two copied words are consumed by the charged bootstrap cleanup. -/
theorem compactMnBootstrap_copies_cleared (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :
    compactMnBootstrapFinal R p d (compactMnSyn (.s 0))=[] ∧
    compactMnBootstrapFinal R p d (compactMnSyn (.s 1))=[] := by
  have hget := compactSetupUpdate7_get compactMnBootstrapDst compactMnBootstrapDst_injective
    (compactMnBootstrapCopied R p d) (compactGlobalBootstrapValues p d)
  exact ⟨by simpa [compactMnBootstrapFinal,compactGlobalBootstrapValues,compactMnBootstrapDst_p] using hget 2,
    by simpa [compactMnBootstrapFinal,compactGlobalBootstrapValues,compactMnBootstrapDst_d] using hget 3⟩


/-- Every register outside the explicitly listed copy and output destinations is preserved. -/
theorem compactMnBootstrap_frame (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ)
    (x : Fin compactMnT) (h0 : x≠compactMnSyn (.s 0)) (h1 : x≠compactMnSyn (.s 1))
    (hout : ∀ i,x≠compactMnBootstrapDst i) : compactMnBootstrapFinal R p d x=R x := by
  rw [compactMnBootstrapFinal,compactSetupUpdate7_off _ _ _ _ hout]
  simp only [compactMnBootstrapCopied,Function.update_of_ne h0,Function.update_of_ne h1]


/-- The original unary precision register is preserved exactly. -/
theorem compactMnBootstrap_preserves_precision (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :
    compactMnBootstrapFinal R p d (compactMnRg (.io .dpn))=R (compactMnRg (.io .dpn)) := by
  apply compactMnBootstrap_frame R p d _ (compactMnRg_ne_lay _ _) (compactMnRg_ne_lay _ _)
  intro i
  have h4 : compactGlobalBootstrapDst 4=reg (.bc (.inl (.work 4))) := compactBasisSetupReg_output 1
  have h5 : compactGlobalBootstrapDst 5=reg (.bc (.inl (.work 3))) := compactBasisSetupReg_output 0
  have h6 : compactGlobalBootstrapDst 6=reg (.bc (.inl (.work 5))) := compactBasisSetupReg_output 2
  have hi : compactGlobalBootstrapDst i≠reg (BReg:=CompactHostBReg) .io := by
    fin_cases i
    · change compactGlobalBootstrapDst 0≠reg (BReg:=CompactHostBReg) .io
      rw [compactGlobalBootstrapDst_guard]
      exact reg_ne (by simp)
    · change compactGlobalBootstrapDst 1≠reg (BReg:=CompactHostBReg) .io
      rw [compactGlobalBootstrapDst_depth]
      exact reg_ne (by simp)
    · change compactGlobalBootstrapDst 2≠reg (BReg:=CompactHostBReg) .io
      rw [compactGlobalBootstrapDst_p]
      exact reg_ne (by simp)
    · change compactGlobalBootstrapDst 3≠reg (BReg:=CompactHostBReg) .io
      rw [compactGlobalBootstrapDst_d]
      exact reg_ne (by simp)
    · change compactGlobalBootstrapDst 4≠reg (BReg:=CompactHostBReg) .io
      rw [h4]
      exact reg_ne (by simp)
    · change compactGlobalBootstrapDst 5≠reg (BReg:=CompactHostBReg) .io
      rw [h5]
      exact reg_ne (by simp)
    · change compactGlobalBootstrapDst 6≠reg (BReg:=CompactHostBReg) .io
      rw [h6]
      exact reg_ne (by simp)
  change compactMnRg (.io .dpn)≠compactMnLayerReg (compactGlobalBootstrapDst i)
  simp only [compactMnLayerReg,hi,ite_false]
  exact compactMnRg_ne_lay _ _


/-- Initial transform depth remains available at its original named source. -/
theorem compactMnBootstrap_preserves_depth (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :
    compactMnBootstrapFinal R p d (compactMnLayerReg (compactLegacyReg (sreg (.p .D))))=
      R (compactMnLayerReg (compactLegacyReg (sreg (.p .D)))) := by
  rw [compactMnSyn_legacy]
  apply compactMnBootstrap_frame R p d _
    (fun h => (by decide : SynW.p .D≠.s 0) (compactMnSyn_injective h))
    (fun h => (by decide : SynW.p .D≠.s 1) (compactMnSyn_injective h))
  intro i h
  have he := compactMnBootstrapReg_source (.p .D)
    (by intro j; fin_cases j <;> simp [compactBasisOutputWire])
  rw [←he] at h
  change compactMnLayerReg (compactBasisSetupReg (sreg (.p .D)))=
    compactMnLayerReg (compactBasisSetupReg (sreg (compactGlobalBootstrapSource i))) at h
  have hh := compactBasisSetupReg_injective (compactMnLayerReg_injective h)
  have hx := sreg_injective hh
  fin_cases i <;> simp [compactGlobalBootstrapSource] at hx

end
end IntegerMultBounds.MathlibTM2.Fast.Main
