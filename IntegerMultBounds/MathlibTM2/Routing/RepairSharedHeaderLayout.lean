module

public import IntegerMultBounds.MathlibTM2.Routing.SharedHeaderBankLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierBank

/-! Connect the shared fifteen-tape header workspace to the exact-repair core.
Dimensions, block width and generated headers use existing raw configuration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

def repairHeaderCoreKey : HeaderCoreRole → SetupKey
  | .dimension i => .field i
  | .block => .block
  | .header c i => .header c i

def repairHeaderCore (r : HeaderCoreRole) : Fin repairClassifierT :=
  classifierCore (repairConfigurationCore (repairRoutingConfig (repairHeaderCoreKey r)))

theorem repairHeaderCore_injective : Function.Injective repairHeaderCore := by
  intro r s he
  have hc := repairConfigurationCore_injective (classifierCore_injective he)
  cases r <;> cases s <;>
    simp_all [repairHeaderCoreKey, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

abbrev repairHeaderT := sharedHeaderT repairClassifierT

def repairSharedHeaderBank (c : Fin 2) : RepairHeaderReg → Fin repairHeaderT := sharedHeaderBank repairHeaderCore c

theorem repairSharedHeaderBank_injective (c : Fin 2) : Function.Injective (repairSharedHeaderBank c) :=
  sharedHeaderBank_injective repairHeaderCore repairHeaderCore_injective c

theorem repairSharedHeaderBank_cross (r : RepairHeaderReg) (i : Fin 5) :
    repairSharedHeaderBank 1 r ≠ repairSharedHeaderBank 0 (.exchange (.base (.header i))) :=
  sharedHeaderBank_cross repairHeaderCore repairHeaderCore_injective r i

theorem repairSharedHeaderBinary_separate (c : Fin 2) (i : Fin 2) (r : RepairHeaderReg) :
    sharedHeaderBinary i ≠ repairSharedHeaderBank c r :=
  sharedHeaderBinary_separate repairHeaderCore repairHeaderCore_injective c i r

@[simp] theorem repairSharedHeaderBank_header (c : Fin 2) (i : Fin 5) :
    repairSharedHeaderBank c (.exchange (.base (.header i))) =
      sharedHeaderCore (classifierCore (repairConfigurationCore (repairRoutingConfig (.header c i)))) := rfl

@[simp] theorem repairSharedHeaderBank_dimension (c : Fin 2) (i : Fin 5) :
    repairSharedHeaderBank c (.dimension i) =
      sharedHeaderCore (classifierCore (repairConfigurationCore (repairRoutingConfig (.field i)))) := rfl

@[simp] theorem repairSharedHeaderBank_block (c : Fin 2) :
    repairSharedHeaderBank c (.exchange (.base .block)) =
      sharedHeaderCore (classifierCore (repairConfigurationCore (repairRoutingConfig .block))) := rfl

end
end IntegerMultBounds.MathlibTM2.Routing
