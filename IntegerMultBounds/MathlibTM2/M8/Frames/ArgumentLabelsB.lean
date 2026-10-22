module

public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.Data
public import IntegerMultBounds.MathlibTM2.M8.Local.KernelOrderB

/-! Computable labels for the frames consumed by design-B arguments and roots.
The compiler correspondence is proved separately in Global.ArgumentFramesB. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB
noncomputable section
open Local

def freeUseLabel (n i : Nat) : Signed.Frame :=
  let next := slotsBefore n
  if n < leafCount then startLabel (next + i)
  else if i = 0 then
    if (bAt n).2.length ≤ 1 then nodeLabel n
    else startLabel (next + ((bAt n).2.length - 1) - 1)
  else startLabel (next + (i - 1))

def argumentLabel (k : Nat) (pos : Bool) : Signed.Frame :=
  let r := records.get width k
  match r.donor pos with
  | some n => nodeLabel n
  | none => freeUseLabel (r.arg pos) ((bAt (r.arg pos)).2.idxOf (.gate k pos))

def rootLabel (j : Nat) : Signed.Frame :=
  let n := (roots.get rootWidth j).node
  freeUseLabel n ((bAt n).2.idxOf (.root j))

end
end IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB
