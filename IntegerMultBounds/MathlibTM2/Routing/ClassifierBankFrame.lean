module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBankLayout
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierClean

/-! Project the concretely placed classifier outputs onto the core bank.
All sixteen auxiliary tapes remain exactly as they were before generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem classifierPairBank_project {N A : ℕ} (p : Par) (temporary phase : Fin N)
    (bank : Fin (N + 16) → List (Fin (A + 4))) :
    (fun i => classifierPairBank p (classifierBankRepeat temporary phase) bank (classifierCore i)) =
      Function.update (Function.update (fun i => bank (classifierCore i)) temporary
        (binSyms (p.wy + 1) (IntegerMultBounds.MathlibTM2.Node.mAV p))) phase
        (binSyms (p.wy + 1) (mkV p)) := by
  funext i
  simp [classifierPairBank, classifierBankRepeat, Function.update_apply, classifierCore_injective.eq_iff]

theorem classifierPairBank_aux {N A : ℕ} (p : Par) (temporary phase : Fin N)
    (bank : Fin (N + 16) → List (Fin (A + 4))) (i : Fin 16) :
    classifierPairBank p (classifierBankRepeat temporary phase) bank (classifierAux i) = bank (classifierAux i) := by
  simp [classifierPairBank, classifierBankRepeat, (classifierCore_aux temporary i).symm,
    (classifierCore_aux phase i).symm]

theorem classifierPairBank_core {N A : ℕ} (p : Par) (temporary phase i : Fin N)
    (bank : Fin (N + 16) → List (Fin (A + 4))) (htemporary : i ≠ temporary) (hphase : i ≠ phase) :
    classifierPairBank p (classifierBankRepeat temporary phase) bank (classifierCore i) = bank (classifierCore i) := by
  simp [classifierPairBank, classifierBankRepeat, classifierCore_injective.eq_iff, htemporary, hphase]

end IntegerMultBounds.MathlibTM2.Routing
