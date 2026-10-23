module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryRepairHeaderPair

/-! Both header generators share dimensions, binary inputs and all workspace.
Only their five output-header roles differ. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

inductive HeaderCoreRole where
  | dimension (i : Fin 5) | block | header (c : Fin 2) (i : Fin 5)
  deriving DecidableEq

inductive HeaderWorkRole where
  | rowExp | gapExp | target | rows | lower | triple | scratch (i : Fin 7) | binary (i : Fin 2)
  deriving DecidableEq, Fintype

def sharedHeaderRole (c : Fin 2) : RepairHeaderReg → HeaderCoreRole ⊕ HeaderWorkRole
  | .dimension i => .inl (.dimension i)
  | .exchange (.base .rowExp) => .inr .rowExp
  | .exchange (.base .gapExp) => .inr .gapExp
  | .exchange (.base .target) => .inr .target
  | .exchange (.base .rows) => .inr .rows
  | .exchange (.base .block) => .inl .block
  | .exchange (.base (.header i)) => .inl (.header c i)
  | .exchange (.base (.scratch i)) => .inr (.scratch i)
  | .exchange .lowerExp => .inr .lower
  | .exchange .triple => .inr .triple

def sharedHeaderDecode : HeaderCoreRole ⊕ HeaderWorkRole → RepairHeaderReg
  | .inl (.dimension i) => .dimension i
  | .inl .block => .exchange (.base .block)
  | .inl (.header _ i) => .exchange (.base (.header i))
  | .inr .rowExp => .exchange (.base .rowExp)
  | .inr .gapExp => .exchange (.base .gapExp)
  | .inr .target => .exchange (.base .target)
  | .inr .rows => .exchange (.base .rows)
  | .inr .lower => .exchange .lowerExp
  | .inr .triple => .exchange .triple
  | .inr (.scratch i) => .exchange (.base (.scratch i))
  | .inr (.binary _) => .dimension 0

theorem sharedHeaderDecode_role (c : Fin 2) (r : RepairHeaderReg) :
    sharedHeaderDecode (sharedHeaderRole c r) = r := by
  cases r with
  | dimension i => rfl
  | exchange r =>
    cases r with
    | lowerExp => rfl
    | triple => rfl
    | base r => cases r <;> rfl

theorem sharedHeaderRole_injective (c : Fin 2) : Function.Injective (sharedHeaderRole c) := by
  intro r s he
  simpa only [sharedHeaderDecode_role] using congrArg sharedHeaderDecode he

theorem sharedHeaderRole_cross (r : RepairHeaderReg) (i : Fin 5) :
    sharedHeaderRole 1 r ≠ sharedHeaderRole 0 (.exchange (.base (.header i))) := by
  cases r with
  | dimension j => simp [sharedHeaderRole]
  | exchange r =>
    cases r with
    | lowerExp => simp [sharedHeaderRole]
    | triple => simp [sharedHeaderRole]
    | base r => cases r <;> simp [sharedHeaderRole]

theorem sharedHeaderRole_binary (c : Fin 2) (r : RepairHeaderReg) (i : Fin 2) :
    Sum.inr (HeaderWorkRole.binary i) ≠ sharedHeaderRole c r := by
  cases r with
  | dimension j => simp [sharedHeaderRole]
  | exchange r =>
    cases r with
    | lowerExp => simp [sharedHeaderRole]
    | triple => simp [sharedHeaderRole]
    | base r => cases r <;> simp [sharedHeaderRole]

end IntegerMultBounds.MathlibTM2.Routing
