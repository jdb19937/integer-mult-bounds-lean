module

public import IntegerMultBounds.MathlibTM2.Routing.SharedHeaderBankLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactClassifierBank
public import IntegerMultBounds.MathlibTM2.Routing.RepairSharedHeaderLayout

/-! Connect the shared fifteen-tape header workspace to the exact-repair core.
Dimensions, block width and generated headers use existing raw configuration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

def repairCompactHeaderCore (r : HeaderCoreRole) : Fin repairCompactClassifierT :=
  classifierCore (repairCompactConfigurationCore (repairRoutingConfig (repairHeaderCoreKey r)))

theorem repairCompactHeaderCore_injective : Function.Injective repairCompactHeaderCore := by
  intro r s he
  have hc := repairCompactConfigurationCore_injective (classifierCore_injective he)
  cases r <;> cases s <;>
    simp_all [repairHeaderCoreKey, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

abbrev repairCompactHeaderT := sharedHeaderT repairCompactClassifierT

def repairCompactSharedHeaderBank (c : Fin 2) : RepairHeaderReg → Fin repairCompactHeaderT := sharedHeaderBank repairCompactHeaderCore c

theorem repairCompactSharedHeaderBank_injective (c : Fin 2) : Function.Injective (repairCompactSharedHeaderBank c) :=
  sharedHeaderBank_injective repairCompactHeaderCore repairCompactHeaderCore_injective c

theorem repairCompactSharedHeaderBank_cross (r : RepairHeaderReg) (i : Fin 5) :
    repairCompactSharedHeaderBank 1 r ≠ repairCompactSharedHeaderBank 0 (.exchange (.base (.header i))) :=
  sharedHeaderBank_cross repairCompactHeaderCore repairCompactHeaderCore_injective r i

theorem repairCompactSharedHeaderBinary_separate (c : Fin 2) (i : Fin 2) (r : RepairHeaderReg) :
    sharedHeaderBinary i ≠ repairCompactSharedHeaderBank c r :=
  sharedHeaderBinary_separate repairCompactHeaderCore repairCompactHeaderCore_injective c i r

@[simp] theorem repairCompactSharedHeaderBank_header (c : Fin 2) (i : Fin 5) :
    repairCompactSharedHeaderBank c (.exchange (.base (.header i))) =
      sharedHeaderCore (classifierCore (repairCompactConfigurationCore (repairRoutingConfig (.header c i)))) := rfl

@[simp] theorem repairCompactSharedHeaderBank_dimension (c : Fin 2) (i : Fin 5) :
    repairCompactSharedHeaderBank c (.dimension i) =
      sharedHeaderCore (classifierCore (repairCompactConfigurationCore (repairRoutingConfig (.field i)))) := rfl

@[simp] theorem repairCompactSharedHeaderBank_block (c : Fin 2) :
    repairCompactSharedHeaderBank c (.exchange (.base .block)) =
      sharedHeaderCore (classifierCore (repairCompactConfigurationCore (repairRoutingConfig .block))) := rfl

end
end IntegerMultBounds.MathlibTM2.Routing
