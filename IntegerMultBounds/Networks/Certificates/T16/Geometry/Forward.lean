module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward0
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward1
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward2
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward3
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward4
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward5
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward6
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward7
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward8
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward9
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward10
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward11
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward12
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward13
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward14
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward15
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward16
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward17
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward18
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward19
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward20
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward21
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward22
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward23
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward24
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem forward_checked : checkEvents edgeBank false Trace.forwardEvents = true := by
  rw [Trace.forwardEvents, checkEvents_flatten]
  simp only [Trace.forwardChunks, List.all_cons, List.all_nil, forwardGroup0_checked,forwardGroup1_checked,forwardGroup2_checked,forwardGroup3_checked,forwardGroup4_checked,forwardGroup5_checked,forwardGroup6_checked,forwardGroup7_checked,forwardGroup8_checked,forwardGroup9_checked,forwardGroup10_checked,forwardGroup11_checked,forwardGroup12_checked,forwardGroup13_checked,forwardGroup14_checked,forwardGroup15_checked,forwardGroup16_checked,forwardGroup17_checked,forwardGroup18_checked,forwardGroup19_checked,forwardGroup20_checked,forwardGroup21_checked,forwardGroup22_checked,forwardGroup23_checked,forwardGroup24_checked, Bool.true_and]
theorem forward_geometry (event : Trace.Event) (h : event ∈ Trace.forwardEvents) : EventGood catalog false event :=
  checkEvents_sound edgeBank false forward_checked event h

end IntegerMultBounds.Networks.Certificates.T16.Geometry
