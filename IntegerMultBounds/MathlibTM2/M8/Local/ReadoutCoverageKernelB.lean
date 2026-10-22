module

public import IntegerMultBounds.MathlibTM2.M8.Local.DataKeyB.ReadoutSequence
public import IntegerMultBounds.MathlibTM2.M8.Local.TreeFacts

/-! Every nonzero readout frame names an entry of the concrete deferred key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.KeyOrderB
noncomputable section

@[irreducible] def nonzeroCovered (s : Nat) (f : Frames.Signed.Frame) : Bool :=
  if f = .zero then true else
    Nat.blt (readoutIndex s) 11565 && Nat.beq (readoutAt (readoutIndex s)) s

end
end IntegerMultBounds.MathlibTM2.M8.Local.KeyOrderB
