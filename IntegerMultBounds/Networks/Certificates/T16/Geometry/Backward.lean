module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward0
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward1
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward2
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward3
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward4
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward5
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward6
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward7
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward8
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward9
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward10
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward11
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward12
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward13
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward14
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward15
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward16
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward17
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward18
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward19
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward20
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward21
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward22
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward23
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward24
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Backward

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem backward_checked : checkEvents edgeBank true Trace.backwardEvents = true := by
  rw [Trace.backwardEvents, checkEvents_flatten]
  simp only [Trace.backwardChunks, List.all_cons, List.all_nil, backwardGroup0_checked,backwardGroup1_checked,backwardGroup2_checked,backwardGroup3_checked,backwardGroup4_checked,backwardGroup5_checked,backwardGroup6_checked,backwardGroup7_checked,backwardGroup8_checked,backwardGroup9_checked,backwardGroup10_checked,backwardGroup11_checked,backwardGroup12_checked,backwardGroup13_checked,backwardGroup14_checked,backwardGroup15_checked,backwardGroup16_checked,backwardGroup17_checked,backwardGroup18_checked,backwardGroup19_checked,backwardGroup20_checked,backwardGroup21_checked,backwardGroup22_checked,backwardGroup23_checked,backwardGroup24_checked, Bool.true_and]
theorem backward_geometry (event : Trace.Event) (h : event ∈ Trace.backwardEvents) : EventGood catalog true event :=
  checkEvents_sound edgeBank true backward_checked event h

end IntegerMultBounds.Networks.Certificates.T16.Geometry
