module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward

/-! Every forward climb and center is a certified frame edge. The span checker runs over the
literal forward trace in kernel pieces between the given event offsets. All edge events lie in
events 9216 to 17407, which are checked 1024 at a time to keep each declaration's kernel memory
small. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem forward_part0 :
    checkEvents catalog false ((Trace.forwardEvents.drop 0).take 9216) = true := by
  decide +kernel

theorem forward_part1 :
    checkEvents catalog false ((Trace.forwardEvents.drop 9216).take 1024) = true := by
  decide +kernel

theorem forward_part2 :
    checkEvents catalog false ((Trace.forwardEvents.drop 10240).take 1024) = true := by
  decide +kernel

theorem forward_part3 :
    checkEvents catalog false ((Trace.forwardEvents.drop 11264).take 1024) = true := by
  decide +kernel

theorem forward_part4 :
    checkEvents catalog false ((Trace.forwardEvents.drop 12288).take 1024) = true := by
  decide +kernel

theorem forward_part5 :
    checkEvents catalog false ((Trace.forwardEvents.drop 13312).take 1024) = true := by
  decide +kernel

theorem forward_part6 :
    checkEvents catalog false ((Trace.forwardEvents.drop 14336).take 1024) = true := by
  decide +kernel

theorem forward_part7 :
    checkEvents catalog false ((Trace.forwardEvents.drop 15360).take 1024) = true := by
  decide +kernel

theorem forward_part8 :
    checkEvents catalog false ((Trace.forwardEvents.drop 16384).take 1024) = true := by
  decide +kernel

theorem forward_part9 : checkEvents catalog false (Trace.forwardEvents.drop 17408) = true := by
  decide +kernel

theorem forward_checked : checkEvents catalog false Trace.forwardEvents = true := by
  rw [← List.drop_zero (l := Trace.forwardEvents),
    checkEvents_drop_split _ _ _ (rfl : 0 + 9216 = 9216), forward_part0, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 9216 + 1024 = 10240), forward_part1, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 10240 + 1024 = 11264), forward_part2, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 11264 + 1024 = 12288), forward_part3, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 12288 + 1024 = 13312), forward_part4, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 13312 + 1024 = 14336), forward_part5, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 14336 + 1024 = 15360), forward_part6, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 15360 + 1024 = 16384), forward_part7, Bool.true_and,
    checkEvents_drop_split _ _ _ (rfl : 16384 + 1024 = 17408), forward_part8, Bool.true_and,
    forward_part9]

theorem forward_geometry (event : Trace.Event) (h : event ∈ Trace.forwardEvents) :
    EventGood catalog false event :=
  checkEvents_sound false forward_checked event h

end IntegerMultBounds.Networks.Certificates.T16.Geometry
