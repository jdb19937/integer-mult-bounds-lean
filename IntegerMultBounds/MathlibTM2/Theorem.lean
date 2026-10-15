module

public import IntegerMultBounds.MathlibTM2.Fast.Final
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynLoop

/-!
# Integer multiplication below `n log n` on Mathlib's Turing machines

`IntegerMultBounds.MathlibTM2.Statement` (`Statement.lean`) follows from the fast host multiplier
(`Fast/Final.fast_statement_of`) and the cost bound of its synthetic transforms
(`Cost/MatchSynLoop.mr_loop_cost_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2

theorem statement : Statement := Fast.Main.fast_statement_of Cost.mr_loop_cost_le

end IntegerMultBounds.MathlibTM2
