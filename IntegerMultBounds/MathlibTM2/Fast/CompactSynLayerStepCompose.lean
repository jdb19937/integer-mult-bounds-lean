module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUnpark
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCleanup
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPark
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStep
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Exact assembly of independently proved concrete round stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactSynParkedFile_io_update
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (io io' park : List (Fin (A+4))) (N r working K ρ : ℕ) (cfg pfs : List ℕ) :
    Function.update (compactSynParkedFile R io park N r working K ρ cfg pfs)
      (reg (BReg := CompactHostBReg) .io) io'=
    compactSynParkedFile R io' park N r working K ρ cfg pfs := by
  have hi : compactLegacyReg (lreg .io)=reg (BReg := CompactHostBReg) .io := by
    simp [lreg,compactLegacyReg,compactMapRegName]
  unfold compactSynParkedFile
  rw [←hi,compactEmbExt_update_image compactLegacyReg compactLegacyReg_injective]
  rw [synG_update_out (lreg_out (by simp)),synRestFile_update (by simp),synIdle_update_io]

lemma compactSynRestored_io_update
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (io io' park : List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (hR : R ∘ compactLegacyReg=synG (synIdle io park) v) :
    embExt compactLegacyReg (synG (synIdle io' park) v) R=
      Function.update R (reg (BReg := CompactHostBReg) .io) io' := by
  have hi : compactLegacyReg (lreg .io)=reg (BReg := CompactHostBReg) .io := by
    simp [lreg,compactLegacyReg,compactMapRegName]
  have he : embExt compactLegacyReg (synG (synIdle io park) v) R=R := by
    rw [←hR,embExt_comp]
  rw [←hi,←he,compactEmbExt_update_image compactLegacyReg compactLegacyReg_injective]
  rw [synG_update_out (lreg_out (by simp)),synIdle_update_io,compactEmbExt_overwrite]

/-- Assembly keeps the original right-associated program and exact stage costs. -/
theorem compactSynLayerStep_compose (body : LProc → Pr LProc (nT CompactHostBReg) Q A U)
    (ds : ComplexFramedExecution.Directions)
    (R₀ R₁ R₂ R₃ R₄ R₅ : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (c₁ c₂ c₃ c₄ c₅ : ℕ)
    (hp : LayRuns body (compactSynLayerPrepare (gateCount (program ds)) (factorCount (program ds))) R₀ R₁ c₁)
    (hk : LayRuns body compactSynLayerPark R₁ R₂ c₂)
    (ht : LayRuns body (compactTopProg (.call .layer)) R₂ R₃ c₃)
    (hu : LayRuns body compactSynLayerUnpark R₃ R₄ c₄)
    (hc : LayRuns body compactBasisRefreshCleanup R₄ R₅ c₅) :
    LayRuns body (compactSynLayerStep ds) R₀ R₅ (c₁+(c₂+(c₃+(c₄+c₅)))) := by
  intro v S hL hR
  obtain ⟨v₁,n₁,hu₁,hc₁,e₁⟩ := hp v S hL hR
  obtain ⟨v₂,n₂,hu₂,hc₂,e₂⟩ := hk v₁ {S with R:=R₁} hL rfl
  obtain ⟨v₃,n₃,hu₃,hc₃,e₃⟩ := ht v₂ {S with R:=R₂} hL rfl
  obtain ⟨v₄,n₄,hu₄,hc₄,e₄⟩ := hu v₃ {S with R:=R₃} hL rfl
  obtain ⟨v₅,n₅,hu₅,hc₅,e₅⟩ := hc v₄ {S with R:=R₄} hL rfl
  let total := n₁+(n₂+(n₃+(n₄+n₅)))
  cases e₂ with
  | seq e₂a e₂bc =>
    cases e₂bc with
    | seq e₂b e₂c =>
      cases e₄ with
      | seq e₄a e₄bc =>
        cases e₄bc with
        | seq e₄b e₄c =>
          refine ⟨v₅,total,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
          · dsimp only [total]; omega
          · simpa only [total,Nat.add_assoc,compactSynLayerStep] using Exec.seq e₁ (Exec.seq e₂a (Exec.seq e₂b (Exec.seq e₂c
              (Exec.seq e₃ (Exec.seq e₄a (Exec.seq e₄b (Exec.seq e₄c e₅)))))))

end
end IntegerMultBounds.MathlibTM2.Fast
