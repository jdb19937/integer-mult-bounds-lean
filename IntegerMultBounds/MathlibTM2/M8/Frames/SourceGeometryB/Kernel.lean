module

public import IntegerMultBounds.MathlibTM2.M8.Local.SourceCoverageKernelB
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotSortB
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootKernel

/-! Source paths are checked on each leaf's small allocation interval. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB
noncomputable section
open Local

def earlySlots (n : Nat) : List Nat :=
  sortSlots KeyOrderB.earlyIndex ((KeyOrderB.sourceSlots n).filter KeyOrderB.earlyMember)

def lateSlots (n : Nat) : List Nat :=
  sortSlots KeyOrderB.lateIndex ((KeyOrderB.sourceSlots n).filter KeyOrderB.lateMember)

def sourceLabels (n : Nat) : List Signed.Frame :=
  (earlySlots n ++ lateSlots n).map AssignmentB.startLabel

/-- A known source chain and a bank containing the input triple bound its actual labels. -/
@[irreducible] def sourceOk (n start : Nat) : Bool :=
  ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt (30637 + n))
    (.positive start :: sourceLabels n ++ [.one]) &&
      ((SignedFull.bankEntry start).basis.contains (GeometryB.rootCode (3 * n)) &&
        Nat.beq (SignedFull.bankEntry start).basis.length 1)

end
end IntegerMultBounds.MathlibTM2.M8.Frames.SourceGeometryB
