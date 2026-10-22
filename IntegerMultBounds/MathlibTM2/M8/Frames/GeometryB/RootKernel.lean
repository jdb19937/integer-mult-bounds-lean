module

public import IntegerMultBounds.MathlibTM2.M8.Frames.ArgumentLabelsB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.LookupData

/-! Final read frames are bounded by a known root complement containing
the output triple (or centre vector). Existing chains supply the nesting edge. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section
open Local

def rootCode (j : Nat) : Nat :=
  if j < 3 * leafCount then
    match (records.get width (j / 3)).supp with
    | .three a b c => a + 32 * b + 1024 * c
    | _ => 0
  else RootCheck.cen + (j - 3 * leafCount)

@[irreducible] def rootOk (j : Nat) (w : Nat × Nat) : Bool :=
  ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt w.1)
    [AssignmentB.rootLabel j, .negative w.2] &&
      (SignedFull.bankEntry w.2).basis.contains (rootCode j)

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
