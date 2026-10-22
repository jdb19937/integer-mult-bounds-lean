module

public import IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB.Data
public import IntegerMultBounds.MathlibTM2.M8.Local.KernelOrderB

/-! Local equations for an untrusted table of every argument and root slot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB
noncomputable section

def argument (n : Nat) : Nat × Nat := argumentSlots.get width n

def slotOf : Use → Nat
  | .gate n pos => if pos then (argument n).2 else (argument n).1
  | .root j => rootSlots.get rootWidth j

def pivotSlot (n : Nat) (x : Nat × Nat) : Nat :=
  match (records.get width n).link with
  | none => x.1
  | some L => if L.operand then x.1 else x.2

def expectedSlot (n p i : Nat) : Nat :=
  if n < leafCount then slotsBefore n + i else if i = 0 then p else slotsBefore n + (i - 1)

/-- Structural recursion over one node's short free-use list. -/
def freeSlotsOk (n p : Nat) : Nat → List Use → Bool
  | _, [] => true
  | i, u :: us => Nat.beq (slotOf u) (expectedSlot n p i) && freeSlotsOk n p (i + 1) us

@[irreducible] def nodeOk (n : Nat) (x : Nat × Nat) : Bool :=
  freeSlotsOk n (pivotSlot n x) 0 (bAt n).2 &&
    match (records.get width n).link with
    | none => true
    | some L => Nat.beq (slotOf (.gate L.user L.pos)) (if L.operand then x.2 else x.1)

end
end IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB
