module

public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.SlotData
public import IntegerMultBounds.MathlibTM2.M8.Frames.ArgumentLabelsB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.LookupData

/-! Readout frames lie below each slot's start frame. The witness is only
an index of an existing certified chain. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section

@[irreducible] def slotOk (s i : Nat) : Bool :=
  ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt i)
    [AssignmentB.sigmaLabel s, AssignmentB.startLabel s]

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
