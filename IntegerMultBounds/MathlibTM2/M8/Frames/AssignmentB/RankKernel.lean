module

public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.Data
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.Data

/-! Local readout ranks determine the design-B exterior ranks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB
noncomputable section

@[irreducible] def sigmaRankOk (_ : Nat) (label : Signed.Frame) : Bool :=
  Nat.ble (label.rankValue SignedFull.bankEntry) 22

end
end IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB
