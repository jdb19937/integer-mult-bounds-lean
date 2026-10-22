module

public import IntegerMultBounds.MathlibTM2.M8.Local.DataCovB.Tables
public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.Data

/-! Checked block masks let target checks skip readouts that cannot touch the target. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
noncomputable section
open Local

structure Hint where
  mask : Nat
  slots : List Nat

def Hint.covers (h : Hint) : Bool :=
  h.slots.all fun s => Nat.beq (Nat.land (CovarianceB.slotMask s) h.mask) (CovarianceB.slotMask s)

def fastLabels (hs : List Hint) (t : Nat) : List Signed.Frame :=
  hs.flatMap fun h => if h.mask.testBit t then
    (h.slots.filter fun s => (CovarianceB.slotMask s).testBit t).map AssignmentB.sigmaLabel else []

end
end IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
