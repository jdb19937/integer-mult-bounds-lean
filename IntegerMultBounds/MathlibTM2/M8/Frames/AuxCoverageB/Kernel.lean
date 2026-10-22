module

public import IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB.Kernel
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.SlotData
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootData
public import IntegerMultBounds.MathlibTM2.M8.Frames.ArgumentLabelsB
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.LookupData

/-! Membership in canonical auxiliary chains, using the checked compiler slot table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB
noncomputable section
open Local

def chainIndex (s : Nat) : Nat := GeometryB.slotTree.get 32768 s

def contains (s : Nat) (f : Signed.Frame) : Bool :=
  (SignedFull.chainAt (chainIndex s)).contains f

@[irreducible] def slotOk (s i : Nat) : Bool :=
  Nat.blt i GeometryB.slotCount && (SignedFull.chainAt i).contains (AssignmentB.sigmaLabel s) &&
    (SignedFull.chainAt i).contains (AssignmentB.startLabel s) &&
    (SignedFull.chainAt i).contains .one

@[irreducible] def nodeOk (n : Nat) (x : Nat × Nat) : Bool :=
  if n < leafCount then true else
    contains x.1 (AssignmentB.nodeLabel n) && contains x.2 (AssignmentB.nodeLabel n) &&
      (List.range ((bAt n).2.length - 1)).all fun i =>
        contains (SlotAssignmentB.pivotSlot n x) (AssignmentB.startLabel (slotsBefore n + i))

/-- Root endpoints use the same canonical slot chain and have codimension one. -/
@[irreducible] def rootOk (j : Nat) (w : Nat × Nat) : Bool :=
  Nat.beq w.1 (chainIndex (SlotAssignmentB.slotOf (.root j))) &&
    (SignedFull.chainAt w.1).contains (.negative w.2) &&
    Nat.beq (SignedFull.bankEntry w.2).basis.length 1

end
end IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB
