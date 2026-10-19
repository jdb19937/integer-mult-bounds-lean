module

public import IntegerMultBounds.MathlibTM2.M8.Local.Witness

/-!
# The donor count of the PR97 side DAG

A kernel count over the node records: `38741` nodes donate a linked operand.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

theorem donors_count : ((List.range nodeCount).countP fun n => (recAt n).link.isSome) = 38741 := by
  decide +kernel

end IntegerMultBounds.MathlibTM2.M8.Local
