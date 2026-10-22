module

public import IntegerMultBounds.MathlibTM2.M8.Local.KernelOrderB
public import IntegerMultBounds.MathlibTM2.M8.Local.MaskWeightsB

/-! Narrow local mask checks. Generated data are untrusted until these pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.CovarianceB
noncomputable section

structure Masks where
  argument : Nat → Bool → Nat
  root : Nat → Nat
  slot : Nat → Nat

def Masks.use (M : Masks) : Use → Nat
  | .gate n pos => M.argument n pos
  | .root j => M.root j

/-- Check consecutive fresh allocations once each. -/
def allocationOk (M : Masks) : Nat → List Use → Bool
  | _, [] => true
  | s, u :: us => Nat.beq (M.slot s) (M.use u) && allocationOk M (s + 1) us

def argumentOk (M : Masks) (n : Nat) (us : List Use) (pos : Bool) : Bool :=
  let b := MaskWeightsB.xorSum (us.map M.use)
  let d := match (records.get width n).link with
    | none => 0
    | some L => if pos = L.operand then M.argument L.user L.pos else 0
  Nat.beq (M.argument n pos) (b ^^^ d)

@[irreducible] def nodeOk (M : Masks) (n : Nat) (x : Nat × List Use) : Bool :=
  allocationOk M (slotsBefore n) (if n < leafCount then x.2 else x.2.tail) &&
    (if n < leafCount then true else argumentOk M n x.2 false && argumentOk M n x.2 true)

/-- Target triples through a centre, read directly from the checked leaf records. -/
def centreTargets (c : Nat) : List Nat :=
  (List.range leafCount).filter fun t =>
    match (records.get width t).supp with
    | .three a b d => Nat.beq c a || Nat.beq c b || Nat.beq c d
    | _ => false

@[irreducible] def centreOk (M : Masks) (c : Nat) : Bool :=
  Nat.beq (M.root (3 * leafCount + c))
    (MaskWeightsB.xorSum ((centreTargets c).map (Nat.shiftLeft 1)))

end
end IntegerMultBounds.MathlibTM2.M8.Local.CovarianceB
