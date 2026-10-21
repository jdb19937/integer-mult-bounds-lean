module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRoot
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

/-! The reversed family's data semantics `FamilySpec` is `RevSemantics.rev97_family_spec`. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Spec

open RevMachine

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

theorem familySpec : FamilyRoot.FamilySpec capacity :=
  RevSemantics.rev97_family_spec capacity

end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Spec
