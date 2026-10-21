module

public import IntegerMultBounds.MathlibTM2.M8.Global.Instance
public import IntegerMultBounds.MathlibTM2.M8.Machine.Net

/-!
# The supplier's network

The bit supplier of the cost chain runs the M8 machine on the PR97 node (`Global.pr97`).
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryRadixEqualShared

/-- The network of the supplier machine. -/
noncomputable instance supplierNet : IntegerMultBounds.MathlibTM2.M8.Machine.Net :=
  ⟨IntegerMultBounds.MathlibTM2.M8.Global.pr97, IntegerMultBounds.MathlibTM2.M8.Global.runs_pr97.supports⟩

end IntegerMultBounds.Machine.BinaryRadixEqualShared
