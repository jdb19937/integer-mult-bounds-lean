module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBankRepair

/-! The concrete classifier workspace extends the combined exact-repair bank.
Its core projection is exactly the generated bank used by exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairCompactClassifierT := repairCompactConfigurationT + 16

def repairCompactClassifierTemporary : Fin repairCompactConfigurationT :=
  repairCompactConfigurationCore (repairSetupSource (.inr .badMask))

def repairCompactClassifierPhase : Fin repairCompactConfigurationT :=
  repairCompactConfigurationCore (repairSetupSource (.inr .badPhase))

theorem repairCompactClassifierOutputs_ne : repairCompactClassifierTemporary ≠ repairCompactClassifierPhase :=
  repairCompactConfigurationCore_injective.ne (by simp [repairSetupSource])

theorem repairCompactClassifierTemporary_src : repairCompactClassifierTemporary ≠ repairCompactConfigurationCore repairHost.src :=
  repairCompactConfigurationSource_src _

theorem repairCompactClassifierPhase_src : repairCompactClassifierPhase ≠ repairCompactConfigurationCore repairHost.src :=
  repairCompactConfigurationSource_src _

theorem repairCompactClassifierBank_project {A : ℕ} (p : Par) (S : Stacks repairCompactClassifierT A) :
    embStk classifierCore
      { S with R := classifierPairBank p (classifierBankRepeat repairCompactClassifierTemporary repairCompactClassifierPhase) S.R } =
      { embStk classifierCore S with R := repairCompactConfigurationClassifierBank p (embStk classifierCore S).R } := by
  have hR := classifierPairBank_project p repairCompactClassifierTemporary repairCompactClassifierPhase S.R
  change (fun i => classifierPairBank p (classifierBankRepeat repairCompactClassifierTemporary repairCompactClassifierPhase) S.R (classifierCore i)) =
    repairCompactConfigurationClassifierBank p (embStk classifierCore S).R at hR
  exact congrArg (fun R => { embStk classifierCore S with R := R }) hR

end
end IntegerMultBounds.MathlibTM2.Routing
