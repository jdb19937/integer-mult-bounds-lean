module

public import IntegerMultBounds.MathlibTM2.M8.Local.LocalSteps
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.SlotData
public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.Data
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.LookupData
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedMoves

/-! Rank-step counts indexed by actual compiler slots, plus data chains and readout ranks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.SignedHistogramB
noncomputable section
open Local

@[irreducible] def chainMoves (_ i : Nat) : List Nat :=
  Signed.rankSteps SignedFull.bankEntry (SignedFull.chainAt i)

@[irreducible] def sigmaMoves (_ : Nat) (f : Signed.Frame) : List Nat :=
  [f.rankValue SignedFull.bankEntry]

end
end IntegerMultBounds.MathlibTM2.M8.Frames.SignedHistogramB
