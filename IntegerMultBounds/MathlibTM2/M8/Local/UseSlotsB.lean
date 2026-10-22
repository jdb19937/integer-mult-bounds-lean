module

public import IntegerMultBounds.MathlibTM2.M8.Local.KernelOrderB

/-! Computable slots for leaf uses and non-kept internal uses. Allocation
counts and serving orders are checked independently of compiler execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local
noncomputable section

def useSlotB (u : Use) : Nat :=
  let n := useNodeB u
  let i := (bAt n).2.idxOf u
  slotsBefore n + if n < leafCount then i else i - 1

@[irreducible] def sourceUseOk (u : Use) : Bool :=
  Nat.blt (useNodeB u) leafCount && freeB (useNodeB u) u

end
end IntegerMultBounds.MathlibTM2.M8.Local
