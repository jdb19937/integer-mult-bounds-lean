module

public import IntegerMultBounds.MathlibTM2.M8.Local.KernelB

/-! Local checks for the complete design-B serving orders. Membership is
checked at each use's consumer, so no check scans the whole DAG. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

def argumentOrderOk (n : Nat) (pos : Bool) : Bool :=
  match (records.get width n).donor pos with
  | some _ => true
  | none => ((bAt ((records.get width n).arg pos)).2).contains (.gate n pos)

/-- Cached next-slot count, checked by the local allocation recurrence. -/
def slotsBefore (n : Nat) : Nat := bnext.get width n

def allocationOk (n : Nat) (us : List Use) : Bool :=
  Nat.beq (slotsBefore (n + 1))
    (slotsBefore n + (us.length - 1) + (if n < leafCount then 1 else 0))

@[irreducible] def bOrderOk (n : Nat) (x : Nat × List Use) : Bool :=
  (x.2.all (freeB n) && decide x.2.Nodup &&
    (bif Nat.ble leafCount n then argumentOrderOk n false && argumentOrderOk n true else true)) &&
      allocationOk n x.2

def rootOrderOk (j : Nat) (r : RootRec) : Bool :=
  (bAt r.node).2.contains (.root j)

end
end IntegerMultBounds.MathlibTM2.M8.Local
