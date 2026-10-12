module

public import IntegerMultBounds.Machine
public import IntegerMultBounds.Machine.Execution

/-! Section 1 milestones (plan/01-machine-model-target.md): one theorem per sub-problem, each bundling the exact statements of its proved pieces. -/

@[expose] public section

namespace IntegerMultBounds.Machine

/-- For all n-bit x, y there is exactly one output word of length 2n with binaryValue x*y, so outputCorrect pins tape zero to a unique, always-achievable content and EndToEnd is a meaningful (non-vacuous) target. -/
theorem outputCorrect_wellPosed :
    (type_of% @IntegerMultBounds.Machine.product_fits) ∧
    (type_of% @IntegerMultBounds.Machine.binaryValue_lt) :=
  ⟨@IntegerMultBounds.Machine.product_fits, @IntegerMultBounds.Machine.binaryValue_lt⟩

end IntegerMultBounds.Machine

namespace IntegerMultBounds.Machine

/-- One step of any literal Program writes only the scanned cell of each tape, moves each head by at most one cell, and its result is determined by the state and the scanned symbols. -/
theorem step_semantics :
    (type_of% @IntegerMultBounds.Machine.Move.unit) ∧
    (type_of% @IntegerMultBounds.Machine.step_local) ∧
    (type_of% @IntegerMultBounds.Machine.step_head_bound) :=
  ⟨@IntegerMultBounds.Machine.Move.unit, @IntegerMultBounds.Machine.step_local, @IntegerMultBounds.Machine.step_head_bound⟩

end IntegerMultBounds.Machine
