module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.EdgeBank
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward16

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem forwardEvents512_checked : checkEvents edgeBank false Trace.forwardEvents512 = true := by decide
theorem forwardEvents513_checked : checkEvents edgeBank false Trace.forwardEvents513 = true := by decide
theorem forwardEvents514_checked : checkEvents edgeBank false Trace.forwardEvents514 = true := by decide
theorem forwardEvents515_checked : checkEvents edgeBank false Trace.forwardEvents515 = true := by decide
theorem forwardEvents516_checked : checkEvents edgeBank false Trace.forwardEvents516 = true := by decide
theorem forwardEvents517_checked : checkEvents edgeBank false Trace.forwardEvents517 = true := by decide
theorem forwardEvents518_checked : checkEvents edgeBank false Trace.forwardEvents518 = true := by decide
theorem forwardEvents519_checked : checkEvents edgeBank false Trace.forwardEvents519 = true := by decide
theorem forwardEvents520_checked : checkEvents edgeBank false Trace.forwardEvents520 = true := by decide
theorem forwardEvents521_checked : checkEvents edgeBank false Trace.forwardEvents521 = true := by decide
theorem forwardEvents522_checked : checkEvents edgeBank false Trace.forwardEvents522 = true := by decide
theorem forwardEvents523_checked : checkEvents edgeBank false Trace.forwardEvents523 = true := by decide
theorem forwardEvents524_checked : checkEvents edgeBank false Trace.forwardEvents524 = true := by decide
theorem forwardEvents525_checked : checkEvents edgeBank false Trace.forwardEvents525 = true := by decide
theorem forwardEvents526_checked : checkEvents edgeBank false Trace.forwardEvents526 = true := by decide
theorem forwardEvents527_checked : checkEvents edgeBank false Trace.forwardEvents527 = true := by decide
theorem forwardEvents528_checked : checkEvents edgeBank false Trace.forwardEvents528 = true := by decide
theorem forwardEvents529_checked : checkEvents edgeBank false Trace.forwardEvents529 = true := by decide
theorem forwardEvents530_checked : checkEvents edgeBank false Trace.forwardEvents530 = true := by decide
theorem forwardEvents531_checked : checkEvents edgeBank false Trace.forwardEvents531 = true := by decide
theorem forwardEvents532_checked : checkEvents edgeBank false Trace.forwardEvents532 = true := by decide
theorem forwardEvents533_checked : checkEvents edgeBank false Trace.forwardEvents533 = true := by decide
theorem forwardEvents534_checked : checkEvents edgeBank false Trace.forwardEvents534 = true := by decide
theorem forwardEvents535_checked : checkEvents edgeBank false Trace.forwardEvents535 = true := by decide
theorem forwardEvents536_checked : checkEvents edgeBank false Trace.forwardEvents536 = true := by decide
theorem forwardEvents537_checked : checkEvents edgeBank false Trace.forwardEvents537 = true := by decide
theorem forwardEvents538_checked : checkEvents edgeBank false Trace.forwardEvents538 = true := by decide
theorem forwardEvents539_checked : checkEvents edgeBank false Trace.forwardEvents539 = true := by decide
theorem forwardEvents540_checked : checkEvents edgeBank false Trace.forwardEvents540 = true := by decide
theorem forwardEvents541_checked : checkEvents edgeBank false Trace.forwardEvents541 = true := by decide
theorem forwardEvents542_checked : checkEvents edgeBank false Trace.forwardEvents542 = true := by decide
theorem forwardEvents543_checked : checkEvents edgeBank false Trace.forwardEvents543 = true := by decide
theorem forwardGroup16_checked : checkEvents edgeBank false Trace.forwardGroup16.flatten = true := by
  rw [checkEvents_flatten]
  simp only [Trace.forwardGroup16, List.all_cons, List.all_nil, forwardEvents512_checked,forwardEvents513_checked,forwardEvents514_checked,forwardEvents515_checked,forwardEvents516_checked,forwardEvents517_checked,forwardEvents518_checked,forwardEvents519_checked,forwardEvents520_checked,forwardEvents521_checked,forwardEvents522_checked,forwardEvents523_checked,forwardEvents524_checked,forwardEvents525_checked,forwardEvents526_checked,forwardEvents527_checked,forwardEvents528_checked,forwardEvents529_checked,forwardEvents530_checked,forwardEvents531_checked,forwardEvents532_checked,forwardEvents533_checked,forwardEvents534_checked,forwardEvents535_checked,forwardEvents536_checked,forwardEvents537_checked,forwardEvents538_checked,forwardEvents539_checked,forwardEvents540_checked,forwardEvents541_checked,forwardEvents542_checked,forwardEvents543_checked, Bool.true_and]

end IntegerMultBounds.Networks.Certificates.T16.Geometry
