module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Backward
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Properties

/-! Exact native-event label certificates for both selected orientations.
No frame operators, wrapper semantics, or dirty routing theorem are asserted. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

theorem same_initial_state : forwardInitial = backwardInitial := rfl

/-- Every native register exists in the initial label trie. -/
theorem initial_contains (i : ℕ) (hi : i < 712) :
    forwardInitial.labels.contains i = true := by
  have h : checkRegisters 712 (fun j => forwardInitial.labels.contains j) = true := by
    decide
  exact checkRegisters_sound h i hi

/-- The two orientations end at the same local label profile; private labels may differ. -/
theorem final_local_labels (i : ℕ) (hi : i < 704) :
    forwardFinal.label i = backwardFinal.label i := by
  have h : checkRegisters 704
      (fun j => forwardFinal.label j == backwardFinal.label j) = true := by decide
  exact eq_of_beq (checkRegisters_sound h i hi)

end IntegerMultBounds.Networks.Certificates.T16.Trace
