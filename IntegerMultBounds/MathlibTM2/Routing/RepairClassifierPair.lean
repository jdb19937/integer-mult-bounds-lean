module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierData
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierPair

/-! Identify the executed two-output classifier bank with the raw R2 inputs.
This derives the existing configuration contract without supplied masks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem classifierPairBank_repair {T A : ℕ} (p : Par) (core : Fin repairT → Fin T)
    (rp : Fin 5 → Fin T)
    (htemporary : rp 3 = core (repairSetupSource (.inr .badMask)))
    (hphase : rp 4 = core (repairSetupSource (.inr .badPhase)))
    (bank : Fin T → List (Fin (A + 4))) :
    classifierPairBank p rp bank = repairClassifierGenerated p core bank := by
  simp only [classifierPairBank, repairClassifierGenerated, htemporary, hphase]

theorem RepairPendingMaskData.classifiersGenerated {T A : ℕ} (p : Par) (X rb : ℕ)
    (core : Fin repairT → Fin T) (hcore : Function.Injective core)
    (rp : Fin 5 → Fin T)
    (htemporary : rp 3 = core (repairSetupSource (.inr .badMask)))
    (hphase : rp 4 = core (repairSetupSource (.inr .badPhase)))
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin T → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (core i))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => classifierPairBank p rp bank (core i)) := by
  rw [classifierPairBank_repair p core rp htemporary hphase]
  exact data.generated p X rb core hcore

theorem classifierPairBank_keep {T A : ℕ} (p : Par) (rp : Fin 5 → Fin T)
    (bank : Fin T → List (Fin (A + 4))) (i : Fin T) (htemporary : i ≠ rp 3) (hphase : i ≠ rp 4) :
    classifierPairBank p rp bank i = bank i := by
  simp [classifierPairBank, htemporary, hphase]

end
end IntegerMultBounds.MathlibTM2.Routing
