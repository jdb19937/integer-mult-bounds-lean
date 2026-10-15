module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.EdgeBank
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward24

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem forwardEvents768_checked : checkEvents edgeBank false Trace.forwardEvents768 = true := by decide
theorem forwardEvents769_checked : checkEvents edgeBank false Trace.forwardEvents769 = true := by decide
theorem forwardEvents770_checked : checkEvents edgeBank false Trace.forwardEvents770 = true := by decide
theorem forwardEvents771_checked : checkEvents edgeBank false Trace.forwardEvents771 = true := by decide
theorem forwardEvents772_checked : checkEvents edgeBank false Trace.forwardEvents772 = true := by decide
theorem forwardEvents773_checked : checkEvents edgeBank false Trace.forwardEvents773 = true := by decide
theorem forwardGroup24_checked : checkEvents edgeBank false Trace.forwardGroup24.flatten = true := by
  rw [checkEvents_flatten]
  simp only [Trace.forwardGroup24, List.all_cons, List.all_nil, forwardEvents768_checked,forwardEvents769_checked,forwardEvents770_checked,forwardEvents771_checked,forwardEvents772_checked,forwardEvents773_checked, Bool.true_and]

end IntegerMultBounds.Networks.Certificates.T16.Geometry
