module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.EdgeBank
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Backward24

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem backwardEvents768_checked : checkEvents edgeBank true Trace.backwardEvents768 = true := by decide
theorem backwardEvents769_checked : checkEvents edgeBank true Trace.backwardEvents769 = true := by decide
theorem backwardEvents770_checked : checkEvents edgeBank true Trace.backwardEvents770 = true := by decide
theorem backwardEvents771_checked : checkEvents edgeBank true Trace.backwardEvents771 = true := by decide
theorem backwardEvents772_checked : checkEvents edgeBank true Trace.backwardEvents772 = true := by decide
theorem backwardEvents773_checked : checkEvents edgeBank true Trace.backwardEvents773 = true := by decide
theorem backwardGroup24_checked : checkEvents edgeBank true Trace.backwardGroup24.flatten = true := by
  rw [checkEvents_flatten]
  simp only [Trace.backwardGroup24, List.all_cons, List.all_nil, backwardEvents768_checked,backwardEvents769_checked,backwardEvents770_checked,backwardEvents771_checked,backwardEvents772_checked,backwardEvents773_checked, Bool.true_and]

end IntegerMultBounds.Networks.Certificates.T16.Geometry
