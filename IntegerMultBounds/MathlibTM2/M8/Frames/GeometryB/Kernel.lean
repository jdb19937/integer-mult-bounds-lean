module

public import IntegerMultBounds.MathlibTM2.M8.Frames.ArgumentLabelsB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.LookupData

/-! Each entry names existing chains witnessing two incoming edges and the
copy path. Only label comparisons are evaluated here; geometry is reused. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section
open Local

def copyLabels (n : Nat) : List Signed.Frame :=
  AssignmentB.nodeLabel n :: (List.range' (slotsBefore n) ((bAt n).2.length - 1)).map
    AssignmentB.startLabel

@[irreducible] def nodeOk (n : Nat) (w : Nat × Nat × Nat) : Bool :=
  if n < leafCount then true else
    ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt w.1)
      [AssignmentB.argumentLabel n false, AssignmentB.nodeLabel n] &&
    ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt w.2.1)
      [AssignmentB.argumentLabel n true, AssignmentB.nodeLabel n] &&
    ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt w.2.2) (copyLabels n)

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
