module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBankRepair

/-! The concrete classifier workspace extends the combined exact-repair bank.
Its core projection is exactly the generated bank used by exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairClassifierT := repairConfigurationT + 16

def repairClassifierTemporary : Fin repairConfigurationT :=
  repairConfigurationCore (repairSetupSource (.inr .badMask))

def repairClassifierPhase : Fin repairConfigurationT :=
  repairConfigurationCore (repairSetupSource (.inr .badPhase))

theorem repairClassifierOutputs_ne : repairClassifierTemporary ≠ repairClassifierPhase :=
  repairConfigurationCore_injective.ne (by simp [repairSetupSource])

theorem repairClassifierTemporary_src : repairClassifierTemporary ≠ repairConfigurationCore repairHost.src :=
  repairConfigurationSource_src _

theorem repairClassifierPhase_src : repairClassifierPhase ≠ repairConfigurationCore repairHost.src :=
  repairConfigurationSource_src _

theorem repairClassifierBank_project {A : ℕ} (p : Par) (S : Stacks repairClassifierT A) :
    embStk classifierCore
      { S with R := classifierPairBank p (classifierBankRepeat repairClassifierTemporary repairClassifierPhase) S.R } =
      { embStk classifierCore S with R := repairConfigurationClassifierBank p (embStk classifierCore S).R } := by
  have hR := classifierPairBank_project p repairClassifierTemporary repairClassifierPhase S.R
  change (fun i => classifierPairBank p (classifierBankRepeat repairClassifierTemporary repairClassifierPhase) S.R (classifierCore i)) =
    repairConfigurationClassifierBank p (embStk classifierCore S).R at hR
  simp only [embStk]
  congr 1

end
end IntegerMultBounds.MathlibTM2.Routing
