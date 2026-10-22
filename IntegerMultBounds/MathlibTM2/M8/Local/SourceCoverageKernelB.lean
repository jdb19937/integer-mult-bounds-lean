module

public import IntegerMultBounds.MathlibTM2.M8.Local.DataKeyB.SourceSequences

/-! Source coverage and phase checks use only allocation counts and indexed keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.KeyOrderB
noncomputable section

def deferredMember (s : Nat) : Bool := keyMember deferredIndex deferredAt 11565 s

def earlyMember (s : Nat) : Bool := keyMember earlyIndex earlyAt 6258 s

def lateMember (s : Nat) : Bool := keyMember lateIndex lateAt 5116 s

/-- A key entry belongs to the intended side of the deferred-slot partition. -/
@[irreducible] def sourcePhaseOk (late : Bool) (u : Use) : Bool :=
  deferredMember (useSlotB u) == late

/-- The slots allocated to a leaf, in allocation order. -/
def sourceSlots (n : Nat) : List Nat :=
  List.range' (slotsBefore n) (bAt n).2.length

/-- Every actual leaf slot occurs in one of the source keys. -/
@[irreducible] def sourceCovered (n : Nat) : Bool :=
  (sourceSlots n).all (fun s => earlyMember s || lateMember s)

end
end IntegerMultBounds.MathlibTM2.M8.Local.KeyOrderB
