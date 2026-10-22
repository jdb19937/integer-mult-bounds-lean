module

public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.Kernel

/-! Structural aggregation of small finite target checks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB

/-- Adjacent checked ranges combine without evaluating a long concrete list. -/
theorem all_range_merge (f : Nat → Bool) (n a b : Nat)
    (ha : (List.range' n a).all f = true)
    (hb : (List.range' (n + a) b).all f = true) :
    (List.range' n (a + b)).all f = true := by
  rw [← List.range'_append_1, List.all_append, ha, hb]
  rfl

end IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
